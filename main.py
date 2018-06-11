import os
import re
import sys
import csv
import time
import getopt
import subprocess
import collections
import pandas as pd
import find_invariant as fi
import refine as refine
from shutil import copyfile
import association_rule_learning as assorule
import multiprocessing
import multiprocessing.dummy
import multiprocessing.managers
from sklearn.externals import joblib


class DataProcess(object):
    def __init__(self, name, replace_index):
        self.name = name
        self.replace_index = replace_index

    def execute(self, save=True, load=False):
        if load:
            try:
                return joblib.load("%s/data/dataset.pkl" % self.name), joblib.load("%s/itemMeaning.pkl" % self.name)
            except:
                raise FileExistsError
        dataList, stateDict = processor.collect_dataset()
        para_digit = self.para_form(stateDict.keys())
        dataset, itemMeaning = processor.encode(dataList, stateDict)

        if save:
            joblib.dump(dataset, "{}/data/dataset.pkl".format(self.name))
            joblib.dump(itemMeaning, "{}/data/itemMeaning.pkl".format(self.name))

        return dataset, itemMeaning, para_digit  # df, itemMeaning

    def para_form(self, name_list):
        """
        the parameter the protocol uses
        with symmetry reduction: NODE_1, NODE_2, ...
        without: 1, 2, ...
        '[]' is a symbol of local variables
        :param name_list:
        :return:
        """
        for name in name_list:
            if '[' in name:
                return False if re.search(r'\w+\_\d', name) else True
            continue
        return True

    def collect_dataset(self):
        """
        From reachable set collect dataset
        :return:
        dataList:
            [
                [v1, v2, ..., vn],
                [e11, e12, ..., e1n],
                ...,
                [en1,en2, ..., enn]]
        dataDict:
            {v1: {e11,e21,..., en1}, v2: {e12,e22, ..., en2},...}
        """
        print('Reading reachable set')
        if not os.path.exists('{0}/{0}.csv'.format(self.name)) and not os.path.exists('{0}/{0}.txt'.format(self.name)):
            raise FileExistsError
        if not os.path.exists('{0}/{0}.csv'.format(self.name)) or not self.is_rs_match_dataset():
            return self.txt2csv()
        else:
            return self.readcsv()

    def is_rs_match_dataset(self):
        """
        Counts the number of states in reachable set printed by Murphi and the number of lines in transferred csv.
        If these two equal, return True; else return False

        NOTE: actually csv file will add a title line with variable names, so # states in txt +1 = # lines in csv
        """
        print('call is_rs_match_dataset')

        csv_cnt = subprocess.check_output(['wc', '-l', '{0}/{0}.csv'.format(self.name)]).decode('utf-8')
        tail_rs = subprocess.check_output(['tail', '{0}/{0}.txt'.format(self.name)]).decode('utf-8')
        return int(re.findall(r'\d+', csv_cnt)[0]) == int(
            re.findall(r'State Space Explored:.*?(\d+)\sstates', tail_rs, re.S)[0]) + 1

    def readcsv(self):
        print('call read_csv')
        df = pd.read_csv('{0}/{0}.csv'.format(self.name))
        stateDict = {}
        booleandf = set(df.select_dtypes(include=[bool]).columns.values)

        for col in df.columns:
            if col in booleandf:
                df[col] = df[col].map({True: 'true', False: 'false'})
            stateDict[col] = set(df[col])
        return [df.columns.tolist()] + df.values.tolist(), stateDict

    def txt2csv(self):
        print('txt2csv...')
        csv_filename = '{0}/{0}.csv'.format(self.name)

        reachset = open('{0}/{0}.txt'.format(self.name)).read()

        if self.replace_index:
            for k, v in self.replace_index.items():
                reachset = reachset.replace(k, v)
        states = re.findall(r'State\s\d+:\n(.*?)\n\n', reachset, re.S)

        variables = [var.split(':')[0] for var in states[0].split('\n')]

        dataset = [variables]
        open(csv_filename, 'w').write("{}\n".format("".join(variables)))

        stateDict = collections.defaultdict(set)

        for state in states:
            for var in state.split('\n'):
                stateDict[var.split(":")[0]].add(var.split(":")[1])
            # dataset.append([var for var in state.split('\n')])
            dataset.append([var.split(':')[1] for var in state.split('\n')])

        with open(csv_filename, 'w') as f:
            for line in dataset:
                f.write(','.join(line) + '\n')
        return dataset, stateDict

    def describe(self, dataList):
        print('---------------------')
        print('Protocol {} has {} states.'.format(self.name, len(dataList) - 1))
        print('Each state has {} variables.'.format(len(dataList[0])))
        print('---------------------\n')

    def encode(self, dataList, stateDict):
        has_atom = os.path.exists('{0}/atom.txt'.format(self.name))
        dataset, itemMeaning = self.tonumber(dataList, stateDict, atom=has_atom, neg=True)
        # print(dataset, itemMeaning)
        #
        # # encoding
        # print('encoding...')
        # te = TransactionEncoder()
        # te_ary = te.fit(dataset).transform(dataset)
        # df = pd.DataFrame(te_ary, columns=te.columns_)
        # print('Total items in rs: %d' % len(itemMeaning))
        # print('finished')
        #
        # saving data
        # return df, itemMeaning
        return dataset, itemMeaning

    def tonumber(self, stateList, statesDict, atom=False, neg=False):
        stateList, statesDict = self.atom_feature(statesDict, stateList, self.get_atoms())
        mappingDict, itemMeaning = self.states2num_atom(statesDict)
        states_numberful = self.mapStates(mappingDict, stateList)
        return states_numberful, itemMeaning
        # elif neg:
        #     stateList, statesDict = self.negative(stateList, statesDict)
        #     mappingDict, itemMeaning = self.states2num(statesDict)
        # else:
        #     mappingDict, itemMeaning = self.states2num(statesDict)

    def enumerateStates(self, stateslist):
        statesDict = collections.defaultdict(set)
        col = len(stateslist[0])
        row = len(stateslist)
        for c in range(col):
            for r in range(1, row):
                if (stateslist[r][c] not in statesDict[stateslist[0][c]]) and (stateslist[r][c] != 'Undefined'):
                    statesDict[stateslist[0][c]].add(stateslist[r][c])
        return statesDict

    def atom_feature(self, stateDict, stateList, atom_feature):
        new_statelist, new_stateDict = [], {}
        index = {title: i for i, title in enumerate(stateList[0])}

        for i, af in enumerate(atom_feature):
            pre = af.split(' ')[0]
            post = af.split(' ')[-1]
            col = index[pre]
            cur = [af]

            for row in range(1, len(stateList)):
                if post in stateDict[pre]:
                    cur.append(str(post == stateList[row][col]))
                else:
                    if post in index:
                        col_post = index[post]
                        if stateList[row][col] != 'Undefined' and stateList[row][col_post] != 'Undefined':
                            cur.append(str(stateList[row][col_post] == stateList[row][col]))
                        else:
                            cur.append('Undefined')
                    else:
                        cur = []
                        break
            if cur:
                new_statelist.append(cur)
                new_stateDict[af] = {x for x in cur} - {af}

        t_statelist = list(list(i) for i in zip(*new_statelist))
        assert len(new_statelist) == len(t_statelist[0])
        assert len(new_statelist[0]) == len(t_statelist)

        print("Features / Atomic predicates: % d " % len(atom_feature))
        return t_statelist, new_stateDict

    def states2num_atom(self, statesDict):
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v == 'Undefined':
                    continue
                low_key = key.lower()
                if 'true' in low_key or 'false' in low_key:
                    if 'true' in low_key:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('true', 'false', key)
                    else:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('false', 'true', key)
                else:
                    if v.lower() == 'false':
                        itemMeaning[cnt] = re.sub(r'=', '!=', key)
                    else:
                        itemMeaning[cnt] = key

                newDict[key][v] = cnt
                cnt += 1
        # print('ItemMeaning:', itemMeaning)
        # for key, value in itemMeaning.items():
        #     print(key, value)
        print('Total products in rs: %d ' % len(itemMeaning))
        return newDict, itemMeaning

    def mapStates(self, mappingDict, stateList):
        print('Mapping states into numbers using all variables...')
        states_numberful = []
        for r in range(1, len(stateList)):
            temp = set()
            for c in range(len(stateList[0])):
                if stateList[r][c] != 'Undefined':
                    temp.add(mappingDict[stateList[0][c]][stateList[r][c]])
            states_numberful.append(temp)

        print('successfully mapped!')
        return states_numberful

    def get_atoms(self):
        file_name = "{}/atom.txt".format(self.name)
        return set(filter(lambda x: x,
                          map(lambda x: re.sub(r'[()]', '', x.strip()), open(file_name, 'r').read().split("\n"))))

    def select_global(self, itemMeaning):
        global_vars = set()
        for k, v in itemMeaning.items():
            if not re.search('[\[\]]', v):
                global_vars.add(k)
        return global_vars

    def negative(self, stateList, statesDict):
        for i in range(1, len(stateList)):
            n = len(stateList[i])
            for j in range(n):
                vals = statesDict[stateList[0][j]]
                if len(vals) <= 2:
                    continue
                for v in vals:
                    if i == 1:
                        stateList[0].append(stateList[0][j])
                    stateList[i].append(v if v == stateList[i][j] else '!' + v)

        statesDict2 = self.enumerateStates(stateList)
        return stateList, statesDict2
        # def states2num(self, statesDict):
        #     newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        #     itemMeaning = {}
        #     cnt = 0
        #
        #     for key, value in statesDict.items():
        #         for v in value:
        #             v = str(v)
        #             if v == 'Undefined': continue
        #             if '!' in v: itemMeaning[cnt] = key + ' != ' + v[1:]
        #             else:
        #                 itemMeaning[cnt] = key + ' = ' + v
        #             newDict[key][v] = cnt
        #             cnt += 1
        #     return newDict, itemMeaning


class RuleLearing(object):
    def __init__(self, df, params, itemMeaning, name, global_vars, freq_size=3, min_support=0.0, min_confidence=1.0,
                 is_minimize=False):
        self.df = df
        self.params = params
        self.name = name
        self.global_vars = global_vars
        self.itemMeaning = itemMeaning
        self.freq_size = freq_size
        self.min_support = min_support
        self.min_confidence = min_confidence
        self.is_minimize = is_minimize
        self.antecedants = []
        self.consequents = []

    def execute(self, para_digit, save=True, load=False):
        if load:
            try:
                self.antecedants = joblib.load('{0}/data/left.pkl'.format(self.name))
                self.consequents = joblib.load('{0}/data/right.pkl'.format(self.name))
            except:
                print('data for RuleLearning cannot be found!')
                # raise FileNotFoundError('data for RuleLearning cannot be found!')

        self.antecedants, self.consequents = assorule.FreqSet_AssoRule().generate(self.name, self.df, self.global_vars,
                                                                                  self.itemMeaning,
                                                                                  self.freq_size, self.min_support,
                                                                                  self.min_confidence,
                                                                                  self.is_minimize)

        # learner.learn_association_rule()
        para_rules = self.para_rules(para_digit, save)
        ins_rules = self.instantiate(para_rules)
        self.minimize_rule(ins_rules)

    def para_rules(self, para_digit, save=True):
        """
        parameterize association rules:
        1. parameterize: paralized line, subsitute parameters into P1,P2,... in original order
            i.e., n[NODE_1] = NODE_2 --> n[P1] = P2
                  n[NODE_2] = NODE_1 --> n[P1] = P2

        2. remove repeated: predicates that before and after '->' have the same variable name
            v1 = e1 -> v1 != e2
            or
            v1 = e1 & v2 = e3 -> v1 != e2
           will be removed
        """

        left, right = [], []
        para_rules, rules = set(), set()

        def paralize(line, par):
            """
            paralized line, subsitute parameters into P1,P2,... in original order
            i.e., n[NODE_1] = NODE_2 --> n[P1] = P2
                  n[NODE_2] = NODE_1 --> n[P1] = P2
            :param line:
            :param par:
            :return: paralized line, without changing the original parameters such as 'NODE_1', 'NODE_2'
            """

            search_para = re.search(r'\[\d\]', line) if para_digit else re.search(r'\[%s\_\d\]' % par, line)

            cnt = 1
            while search_para:
                line = line.replace(search_para.group(), '[P%d]' % cnt)
                search_para = re.search(r'\[\d\]', line) if para_digit else re.search(r'\[%s\_\d\]' % par, line)
                cnt += 1
            return line

        for ant, conse in zip(self.antecedants, self.consequents):
            # if len(conse) <= 1:
            line = "{} -> {}".format(' & '.join(sorted(ant)), conse)
            for par in self.params:
                paralized_line = paralize(line, par)
                # paralized_line = line
                if paralized_line in para_rules:
                    # para_rules.remove(paralized_line)
                    continue
                else:
                    para_rules.add(paralized_line)

                    # extract variable names and remove the rule which has same variable in both sides of '='
                    left_var, right_var = set([a.split(' ')[0] for a in ant]), set([conse.split(' ')[0]])

                    if left_var.issubset(right_var) or right_var.issubset(
                            left_var):  # or not re.search('[\[\]]', ''.join(left_var)):
                        para_rules.remove(paralized_line)
                        continue
                    else:
                        left.append(sorted([a for a in ant]))
                        right.append(conse)
                        rules.add("{} -> {}".format(' & '.join(sorted(ant)), conse))

        assert (len(left) == len(right))
        self.antecedants, self.consequents = left, right

        print('Parametrized rules: %d ' % len(left))

        # with open('%s/assoRule_min.txt' % name, 'w') as fw:
        #     for i, rule in enumerate(ins_rules, 1):
        #         fw.write('rule_%d: %s\n' % (i, rule))

        if save:
            f_left = '%s/data/left.pkl' % self.name
            f_right = '%s/data/right.pkl' % self.name

            joblib.dump(left, f_left)
            joblib.dump(right, f_right)

        return para_rules

    def instantiate(self, para_line, paras=['NODE_1', 'NODE_2']):
        """
        instantiate association rules.
        E.g. n[P1] -> P2  will be instantiated into :
             n[i] -> j
        and  n[j] -> i
        :param para_line:
        :return:
        """
        # paras = ['NODE_1', 'NODE_2']
        fname = '{0}/aux_invs.txt'.format(self.name)
        ins_lines = []
        for line in para_line:
            for index in range(len(paras)):
                temp = line
                search_para = re.search(r'P\d', temp)

                while search_para:
                    temp = re.sub(search_para.group(), paras[index], temp)
                    search_para = re.search(r'P\d', temp)
                    index ^= 1
                ins_lines.append(temp)

        with open(fname, 'w') as f:
            for cnt, line in enumerate(ins_lines, 1):
                f.write('rule_%d:   %s\n' % (cnt, line))

        print('instantiated rules: %d ' % len(ins_lines))
        return ins_lines

    def minimize_rule(self, ins_lines):
        fout = '%s/assoRule_min.txt' % self.name

        # with open(fn, 'r') as f:
        #     rules = list(line.strip('\n').split(': ')[1].strip(' ') for line in f.readlines() if line.strip())
        #
        rules = list(map(lambda line: line.split(' -> '), sorted(ins_lines, key=lambda x: len(x))))
        # joblib.dump(rules, 'mutualEx/data/rules.pkl')
        # rules = joblib.load('mutualEx/data/rules.pkl')


        left = [rule[0].split(' & ') for rule in rules]
        right = [rule[1] for rule in rules]

        same_right = collections.defaultdict(list)
        for l, r in zip(left, right):
            same_right[r].append(l)

        for r, left_list in same_right.items():
            index = [x for x in range(len(left_list))]
            for i in range(len(left_list)):
                for j in range(i + 1, len(left_list)):
                    if j not in index: continue
                    if not (set(left_list[i]) - set(left_list[j])):
                        index.remove(j)
            same_right[r] = [left_list[i] for i in index]

        min_rules = []
        new_l, new_r = [], []
        # with open(fout, 'w') as f:
        cnt = 1
        for r, left_list in same_right.items():
            for l in left_list:

                if not re.search('[\[\]]', ''.join(l)):
                    continue
                each = '{} -> {}\n'.format(' & '.join(l), r)
                new_l.append(l)
                new_r.append(r)
                min_rules.append(each)
                # f.write('rule_%d: %s' % (cnt, each))
                cnt += 1

        self.antecedants, self.consequents = new_l, new_r
        print('minimized: %d ' % (cnt - 1))
        assert len(self.antecedants) == cnt - 1
        return min_rules

    def built_map(self):
        """
        build a rule map using antecendents:

        e.g. n[NODE_1] = C -> n[NODE_2] != C
        build a rule map:
        {n[NODE]: n[NODE_1] = C -> n[NODE_2] != C}

        :return:
        """

        rules_map = collections.defaultdict(lambda: collections.defaultdict(set))
        par = self.params[0]

        for left, right in zip(self.antecedants, self.consequents):
            # key = ','.join(sorted(left))
            # for par in self.params:
            #     key = lambda x : re.sub(r'%s\_\d' % par, par, x)

            key = frozenset(map(lambda x: re.sub(r'%s\_\d' % par, par, x), left))
            # key = frozenset(map(lambda x: re.sub(r'\d', par, x), left))


            rules_map[key][frozenset(left)].add(right)
        return rules_map

    def slct_rules_by_guards(self, rules_map, guards, par, save=True, load=False):
        if load and os.path.exists("{}/data/norm_rule_dict.pkl".format(self.name)) and os.path.exists(
                "{}/data/rules.pkl".format(self.name)):
            return joblib.load("{}/data/norm_rule_dict.pkl".format(self.name)), joblib.load(
                "{}/data/rules.pkl".format(self.name))

        par = par[0]
        norm_rule_dict = {key: rules for key, rules in rules_map.items() if set(key).issubset(guards)}

        rules = set()

        for ant_dict in norm_rule_dict.values():
            for ant, conse_set in ant_dict.items():
                for conse in conse_set:
                    line = "{} -> {}".format(' & '.join(sorted(ant)), conse)
                    search_para = re.search(r'%s\_\d' % par, line)
                    # search_para = re.search(r'\d', line)

                    cnt = 1
                    while search_para:
                        line = re.sub(search_para.group(), 'P%d' % cnt, line)
                        search_para = re.search(r'%s\_\d' % par, line)
                        # search_para = re.search(r'%s\_\d' % par, line)

                        cnt += 1

                    rules.add(line)
        print('select %d association rules' % len(rules))

        # fout = '%s/selected_by_guard.txt' % self.name
        # with open(fout, 'w') as f:
        #     for i, r in enumerate(rules, 1):
        #         f.write('rule_%d: %s\n' % (i, r))

        # save data
        # self.write_to_file(rules)

        if save:
            joblib.dump(norm_rule_dict, "{}/data/norm_rule_dict.pkl".format(self.name))
            joblib.dump(rules, "{}/data/rules.pkl".format(self.name))

        return norm_rule_dict, rules

    def write_to_file(self, rules):
        with open("{}/rules.txt".format(self.name), 'w') as f:
            f.writelines("\n".join(rules))


class SlctInv(object):
    def __init__(self, name, par, test_rules, home=False):
        self.name = name
        self.home = home
        self.murphi_dir = self.loc_murphi_dir()
        self.par = par
        self.test_rules = {'rule_%d' % i: rule for i, rule in enumerate(test_rules, 1)}

    def select_invariant(self, pattern=re.compile(r'P\d'), num_core=multiprocessing.cpu_count(), original_file=None):
        translate_dic = self.translate_test_inv(pattern=pattern)
        original_file = "{0}/{0}.m".format(self.name) if original_file is None else original_file

        n = len(self.test_rules)
        jobs = [(i * n // num_core, (i + 1) * n // num_core) for i in range(num_core)]

        print('ranges', jobs)
        spurious = []
        with multiprocessing.Pool(num_core) as p:
            spurious.extend(p.starmap(self.parallel,
                                      [(index_range, pid, translate_dic, original_file) for
                                       pid, index_range
                                       in enumerate(jobs, 1)]))

        # print(spurious)
        spurious_cnt = 0
        for key in spurious:
            for k in key:
                self.test_rules.pop(k)
                spurious_cnt += 1

        print(n, spurious_cnt, len(self.test_rules))
        assert n == spurious_cnt + len(self.test_rules)
        return spurious_cnt

    def loc_murphi_dir(self):
        if not os.path.exists('murphi_url.txt'): raise FileExistsError
        return open('murphi_url.txt').read().strip()

    def run_murphi(self, file, aux_para=''):
        file = file.split('.')[0]
        process1 = subprocess.Popen("{0}/src/mu {1}.m".format(self.murphi_dir, file), shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)

        (stdout, stderr) = process1.communicate()
        if not re.search(r'Code generated', stdout.decode('utf-8')):
            print(stderr.decode('utf-8'))
            raise ValueError

        command2 = "g++ -ggdb -o {0}.o {0}.cpp -I {1}/include -lm".format(file, self.murphi_dir)

        process2 = subprocess.Popen(command2, shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        process2.communicate()

        process = subprocess.Popen("{0}.o -k10000000 {1}".format(file, aux_para), shell=True,
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)

        (stdoutdata, stderrdata) = process.communicate()

        pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed')
        counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))
        print(counter_ex)

        os.remove('%s.cpp' % file)
        os.remove('%s.o' % file)

        return counter_ex[0] if len(counter_ex) else 0

    def translate_test_inv(self, pattern):
        # test_invs is empty
        if not self.test_rules: return []
        # print('testing %d rules' % len(self.test_rules))

        translate_dic = {}
        for key, rule in self.test_rules.items():
            translate_dic.update(
                {key: '\n\nInvariant \"%s\"\n' % key + self.to_murphi(rule, self.par, pattern, self.home)})
        return translate_dic

    def parallel(self, index_range, id, translate_dic, original_file):
        start, end = index_range
        counters = []
        new_file = "{}_{}.m".format(original_file.split('.')[0], id)
        copyfile(original_file, new_file)
        with open(new_file, 'a') as f:
            for rule_num in range(start + 1, end + 1):
                f.writelines(translate_dic['rule_%d' % rule_num])
        print(new_file)
        counter_ex = self.run_murphi(new_file)

        while counter_ex:
            counters.append(counter_ex)
            pattern = re.compile(r'Invariant \"%s\".*?;' % counter_ex, re.S)
            new_content = re.sub(pattern, '', open(new_file).read())

            with open(new_file, 'w') as fw:
                fw.writelines(new_content)
            counter_ex = self.run_murphi(new_file)

        os.remove("{}.m".format(new_file.split('.')[0]))
        # os.remove("{}.cpp".format(new_file.split('.')[0]))
        # os.remove("{}.o".format(new_file.split('.')[0]))

        return counters

    def to_murphi(self, rule, par, pattern, home=False):
        """
        translate an association rule('Chan2[__P1__].Cmd = Inv -> Cache[__P2__].Data = AuxData') into murphi code
        invariant "rule_1"
            forall __P1__: NODE do forall __P2__: NODE do
            __P1__ != __P2__ -> (Chan2[__P1__].Cmd = Inv -> Cache[__P2__].Data = AuxData)
        end end;

        :param rule: an association rule
        :param par: NODE
        :return: murphi code
        """

        paras = list(set(pattern.findall(rule)))
        definition = " ".join("forall {} : {} do".format(x, par[0]) for x in paras)

        pre= ""

        home_def = " & ".join("{} != Home".format(x) for x in paras) if home else ""

        if len(paras) == 2:
            pre += "{} != {}".format(paras[0], paras[1])

        if home and pre: pre += " & " +home_def
        if pre: pre += ' -> '
        end = "end " * len(paras)

        murphi_code = "{}\n  {}({})\n{};".format(definition, pre, rule, end)

        return murphi_code

    def check_usedF(self, pattern, num_core, original_file):
        spurious_cnt = self.select_invariant(pattern=pattern, num_core=num_core, original_file=original_file)
        if not spurious_cnt:
            print('usedF all passed!')
        else:
            print('usedF failed.')
            print(spurious_cnt)

    def prnt_inv(self):
        invs = set(v for k, v in self.test_rules.items())
        with open("{}/invs.txt".format(self.name), 'w') as f:
            for i, inv in enumerate(invs, 1):
                f.writelines("rule_%d: %s\n" % (i, inv))
        return invs


def check_file(name):
    """
    check whether the folder, files (murphi, atoms) exist.
    If txt/csv doesn't exist, then call Murphi to generate reachable set
    Mkdir 'data' folder
    :param name:
    :return:
    """

    prefix = '{0}/{0}'.format(name)
    if os.path.exists('%s.m' % prefix):
        # and (os.path.exists('%s.csv' % prefix) or os.path.exists('%s.txt' % prefix)) \
        # and os.path.exists('%s/atom.txt' % name):

        # Need collect reachable set
        if not os.path.exists('%s.txt' % prefix) and not os.path.exists('%s.csv' % prefix):
            print('calling Murphi to generate reachable set...')
            inv_slcter = SlctInv(name, [], set(), home=False)
            inv_slcter.run_murphi('{0}/{0}.m'.format(name), '-ta >{0}/{0}.txt'.format(name))
        if not os.path.exists('%s/data' % name):
            os.mkdir('%s/data' % name)
    else:
        raise FileNotFoundError(
            'There must be murphi, reachable set, and atomic predicates in the corresponding folder')


prefix_msg = '''
==========================================================================
Welcome to L-CMP

1. Please make sure you have installed CMurphi properly, and 
   write CMurphi's location into murphi_url.txt. 
        E.g. /home/usr/cmurphi5.4.9.1/
2. We provide several testing protocols including:
        MutualExclusion, Mesi, Meosi, German, and Flash.
3. If you have any question, please contact us at:
        caojl[at]ios[dot]ac[dot]cn
==========================================================================
'''

help_msg = '''
==========================================================================
Usage:

Options:
1) General: (default: -n 2)
	-h            help.
	-p            protocol name
	-n <n>        number of node used for verification
	              (protocols with only homogenerous nodes -- 2
	               protocols with a heterogenerous node   -- 3)
2) Learning process: (default: -f 2, -s -0, -c 1)
	-l            load the existing auxiliary invariants. 
	              (if file "aux_invs.txt" in the correspondent folder)
	-f <n>        the size of frequent set
	-s <n>        the minimun support in association rule learning algorithm
	-c <n>        the minimun confidence in association rule learning algorithm
2) Other options: (default: -k 2)
	-k <n>        number of processor

==========================================================================
'''

end_msg = '''
==========================================================================
Thank you for using L-CMP

All generated files can be found in the folder named after input protocol name.
If you have any question, please send to caojl[at]ios[dot]ac[dot]cn.
==========================================================================
'''

if __name__ == "__main__":
    try:
        if not os.path.exists('./murphi_url.txt'):
            print('murphi_url.txt does not exists! Please create!')
            sys.exit(1)

        with open('./murphi_url.txt', 'r') as f:
            murphi_url = f.read().strip()

        if murphi_url == '':
            print('Empty murphi_url.txt, please check again.')
            exit(1)
        if not os.path.exists(murphi_url):
            print('Wrong murphi url, please check url in murphi_url.txt again.')
            exit(1)

        sys.stderr.write(prefix_msg)

        opts, args = getopt.getopt(sys.argv[1:], 'p:n:f:s:c:k:h:l',
                                   ['protocol=', 'node=', 'frequentset=', 'support=', 'confid=', 'kernel=', 'help',
                                    'load'])

        # opts = [('-p', 'german'), ('-n', '2')]

        protocol_name = ''
        NODE_NUM, set_n, min_support, min_config, core_num, LOAD = 2, 3, 0.0, 1.0, multiprocessing.cpu_count(), False
        for opt, arg in opts:
            if opt in ('-h', '--help'):
                sys.stdout.write(help_msg)
                sys.exit(0)
            elif opt in ('-l', '--load'):
                LOAD = True
            elif opt in ('-p', '--protocol'):
                protocol_name = arg
            elif opt in ('-n', '--node'):
                NODE_NUM = int(arg)
            elif opt in ('-f', '--frequentset'):
                set_n = int(arg)
            elif opt in ('-s', '--support'):
                min_support = float(arg)
            elif opt in ('-c', '--confid'):
                min_config = float(arg)
            elif opt in ('-k', '--kernel'):
                core_num = int(arg)
            else:
                print('Wrong input!\n')
                sys.stderr.write(help_msg)
                sys.exit(1)

        if not protocol_name:
            print('Please input protocol name!')
            sys.exit(1)
    except getopt.GetoptError:
        sys.stderr.write(help_msg)
        sys.exit()
    else:
        # -------------------- Config --------------------
        name = protocol_name  # 'german'
        NUM = NODE_NUM  # 2
        # -------------------- End Config --------------------

        check_file(name)

        # -------------------- Start --------------------
        start = time.time()

        # ----------------------------------------
        # anaylze murphi description
        murphi_analyser = fi.Protocol(name)
        params, guards = murphi_analyser.execute()

        murphi_analyser.set_paras('NODE', NUM)
        print('PARA = %d' % (NUM))

        if LOAD:
            finv = "%s/aux_invs.txt" % name
            ins_invs = list(map(lambda x: x.split(':   ')[1],
                                filter(lambda x: x, [line.strip() for line in open(finv, 'r').readlines()])))
        else:
            # ----------------------------------------
            # preprocessor
            replace_index = None if NUM == 2 else {'NODE_1': 'Home'}
            processor = DataProcess(name, replace_index=replace_index)  # {'NODE_1': 'Home'})
            dataset, itemMeaning, para_digit = processor.execute(load=False)
            global_vars = processor.select_global(itemMeaning)
            print('local', global_vars)

            # ----------------------------------------
            # learner & minimize association rules
            learner = RuleLearing(dataset, params, itemMeaning, name, global_vars=global_vars, freq_size=3,
                                  min_support=0.0,
                                  min_confidence=1.0, is_minimize=False)
            learner.execute(para_digit, save=True, load=False)

            # build a rule map to easily find association rules
            rules_map = learner.built_map()
            new_dict, useful_rules = learner.slct_rules_by_guards(rules_map, guards, params, save=True, load=True)

            # ----------------------------------------
            # select auxiliary invariant
            murphi_analyser.set_paras('NODE', NUM + 1)
            print('PARA = %d' % (NUM + 1))

            former, add = 0x77777777, 2
            while True:
                inv_slcter = SlctInv(name, params, useful_rules, home=False if NUM == 2 else True)
                inv_slcter.select_invariant(num_core=core_num)
                invs = inv_slcter.prnt_inv()

                cur = len(invs)
                if former == cur:
                    break
                else:
                    print('PARA = %d' % (NUM + add))
                    former = min(former, cur)
                    murphi_analyser.set_paras('NODE', NUM + add)
                    add += 1

            ins_invs = learner.instantiate(invs, paras=['i', 'j'])
            # print(ins_invs)

        print('\n--------------------\nPhase 1 finished!\n--------------------\n')

        # strengthen and abstract
        refiner = refine.Refiner(name, ins_invs)
        abs_file, usedF = refiner.refine(node_num=NUM)

        print('\nchecking usedF...')
        murphi_analyser.set_paras('NODE', NUM)
        print('PARA = %d' % NUM)
        inv_slcter = SlctInv(name, params, usedF, home=False if NUM == 2 else True)
        inv_slcter.check_usedF(pattern=re.compile(r'\b[ij]\b'), num_core=core_num, original_file=abs_file)

        print('\n--------------------\nPhase 2 finished!\n--------------------\n')

        print('Total running time: %.3f s.' % (time.time() - start))
        sys.stderr.write(prefix_msg)
