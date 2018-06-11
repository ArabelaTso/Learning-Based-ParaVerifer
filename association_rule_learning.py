import sys
import time
from sklearn.externals import joblib
import os
import subprocess
import re
from shutil import copyfile
import collections
import multiprocessing
import multiprocessing.dummy
import multiprocessing.managers


class Save_Load_Data(object):
    def __init__(self, protocol_name):
        self.L_name = protocol_name + '/backup/' + 'L_' + protocol_name + '.pkl'
        self.Support_name = protocol_name + '/backup/' + 'SupportData_' + protocol_name + '.pkl'

        if not os.path.exists(protocol_name + '/backup'):
            os.mkdir(protocol_name + '/backup')

    def load_from_plk(self):
        print("Loading L and Supportive Data ........")
        L = joblib.load(self.L_name)
        support_data = joblib.load(self.Support_name)
        print("L and Supportive Data loaded successfully!")
        return L, support_data

    def save_to_plk(self, L, support_data):
        print("Saving L and Supportive data......")
        joblib.dump(L, self.L_name)
        joblib.dump(support_data, self.Support_name)
        print("L and Supportive data saved Successfully!")


class FreqSet_AssoRule(object):
    def __init__(self):
        self.d_super_set = collections.defaultdict(set)

    def generate(self, name, dataset, global_vars, itemMeaning, freq_size=3, min_support=0.0, min_confidence=1.0,
                 is_minimize=False):
        L, support_data = self.apriori(dataset, global_vars, set_num=freq_size, minSupport=min_support, is_minimize=is_minimize)

        print("learning association rule  ...")
        bigRuleList = self.generateRules(L, support_data, minConf=min_confidence)

        return self.prntRules(bigRuleList, itemMeaning, name)

    def createC1(self, dataSet):  # creat candidates frequent set with 1 element
        C1 = []
        for transaction in dataSet:
            for item in transaction:
                if [item] not in C1:
                    C1.append([item])

        C1.sort()
        return list(map(frozenset, C1))  # use frozen set so we can use it as a key in a dict

    def scanD(self, D, Ck, minSupport):
        print("len d: {}, len ck:{} ".format(len(D), len(Ck)))
        print("time complexity will be: O({})".format(len(D) * len(Ck)))

        ssCnt = {}
        for key in Ck:
            can = list(key)
            res = self.d_super_set[can[0]]
            for t in can[1:]:
                res = res & self.d_super_set[t]
            if len(res) != 0:
                ssCnt[key] = len(res)

        numItems = float(len(D))
        retList = []
        supportData = {}
        for key in ssCnt:
            support = ssCnt[key] / numItems
            if support >= minSupport:
                retList.append(key)
            supportData[key] = support
        return retList, supportData

    def _build_trie(self, data, k):
        root = {}
        for i, row in enumerate(data):
            row = sorted(list(row))[:k - 2]
            cur = root
            for d in row:
                if d not in cur:
                    cur[d] = {}
                cur = cur[d]
            cur[i] = None
        return root

    def aprioriGen(self, Lk, k):  # creates Ck
        retList = []
        root = self._build_trie(Lk, k)
        for i, row in enumerate(Lk):
            row = sorted(list(row))[:k - 2]
            cur = root
            ok = True
            for d in row:
                if d not in cur:
                    ok = False
                    break
                cur = cur[d]
            if ok:
                retList.extend([Lk[i] | Lk[j] for j in cur.keys() if i < j])
        return retList

    def _build_super_set(self, data: list):
        """
        :param data: [set,set..]
        :return:
        """
        print('---build_super_set----')
        for i, d in enumerate(data):
            for x in d:
                self.d_super_set[x].add(i)

        print('build_super_set done')

    def apriori(self, dataSet, global_vars, set_num, minSupport=0.0, is_minimize=False):
        print('--------------------------\nGenerating frequent set........')
        start_freq = time.time()
        C1 = self.createC1(dataSet)
        D = list(map(set, dataSet))  # add cast to list. In py3, map create a genarator.

        self._build_super_set(D)

        start = time.time()
        L1, supportData = self.scanD(D, C1, minSupport)
        print('time for scan L1: %.3f' % (time.time() - start))

        L = [L1]
        k = 2
        while k <= set_num:
            Ck = self.aprioriGen(L[k - 2], k)
            start = time.time()

            # remove those 3 global variables if minimize = True
            Ck = filter(lambda x: len(x & global_vars) < 3, Ck) if is_minimize else Ck

            all_lemma_set = list(Ck)
            Lk, supK = [], {}

            for t in [self.parellel_cal(D, all_lemma_set, minSupport)]:
                Lk.extend(t[0])
                supK.update(t[1])

            print('time for scan L%d : %.3f\n-------------------\n' % (k, time.time() - start))

            supportData.update(supK)
            L.append(Lk)
            k += 1

        print('Running time for frequent sets: %.3f s' % (time.time() - start_freq))
        return L, supportData

    def parellel_cal(self, D, Ck, minSupport):
        Lk, supK = self.scanD(D, Ck, minSupport)  # scan DB to get Lk
        return (Lk, supK)

    def generateRules(self, L, supportData, minConf=1.0):  # supportData is a dict coming from scanD
        start = time.time()

        bigRuleList = []
        for i in range(1, len(L)):  # only get the sets with two or more items
            for freqSet in L[i]:
                H1 = [frozenset([item]) for item in freqSet]
                if i > 1:
                    self.rulesFromConseq(freqSet, H1, supportData, bigRuleList, minConf)
                else:
                    self.calcConf(freqSet, H1, supportData, bigRuleList, minConf)

        print('Running time for calculating association rules: %.3f s ' % (time.time() - start))

        return bigRuleList

    def calcConf(self, freqSet, H, supportData, brl, minConf=1.0):
        prunedH = []  # create new list to return

        for cond in H:
            conf = supportData[freqSet] / supportData[cond]  # calc confidence
            if conf >= minConf:
                if len(freqSet - cond) == 1:
                    brl.append((cond, freqSet - cond, conf))
                prunedH.append(cond)

        return prunedH

    def rulesFromConseq(self, freqSet, H, supportData, brl, minConf=1.0):
        m = len(H[0])
        if (len(freqSet) > (m + 1)):  # try further merging
            Hmp1 = self.aprioriGen(H, m + 1)  # create Hm+1 new candidates

            Hmp1 = self.calcConf(freqSet, Hmp1, supportData, brl, minConf)

            if (len(Hmp1) > 1):  # need at least two sets to merge
                self.rulesFromConseq(freqSet, Hmp1, supportData, brl, minConf)

    def prntRules(self, bigRuleList, itemMeaning, name):
        sortedRuleList = sorted(bigRuleList, key=lambda d: d[2], reverse=True)

        left, right, rules = [], [], set()
        for ruleTup in sortedRuleList:
            ant, conseq = ruleTup[0], ruleTup[1]
            e_ant = set(itemMeaning[a] for a in ant)
            e_conseq = set(itemMeaning[c] for c in conseq)

            rules.add(' & '.join(e_ant) + ' -> ' + ''.join(e_conseq))
            # left_var, right_var = set([a.split(' ')[0] for a in e_ant]), set(c.split(' ')[0] for c in e_conseq)

            # if left_var.issubset(right_var) or right_var.issubset(left_var) or not re.search('[\[\]]',
            #                                                                                  ''.join(left_var)):
            #     continue
            # else:
            left.append(sorted([a for a in e_ant]))
            for c in e_conseq:
                right.append(c)
        with open('%s/assoRules.txt' % name, 'w') as fw:
            for i, rule in enumerate(rules, 1):
                fw.write('rule_%d: %s\n' % (i, rule))

        print('Association rule: {}'.format(len(sortedRuleList)))
        return left, right
