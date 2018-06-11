import re
from shutil import copyfile
import copy


class Refiner(object):
    def __init__(self, name, ins_inv):
        self.PN = name
        self.ins_inv = ins_inv

    def refine(self, node_num):
        if node_num == 2:
            refiner = Refine_2_NODE(self.PN, self.ins_inv)
            refiner.analyzer()
            return refiner.abs_file, refiner.write_lemma()
        elif node_num == 3:
            refiner = Refine_3_NODE(self.PN, self.ins_inv)
            refiner.analyzer()
            return refiner.abs_file, refiner.write_lemma()
        else:
            raise Exception


class Refine_2_NODE(object):
    def __init__(self, name, ins_inv):
        self.pn = name
        self.abs_file = self.create_abs()
        self.content = open("{0}/{0}.m".format(self.pn)).read()
        self.lemma = set()
        self.rules = self.read_rule(ins_inv)

    def create_abs(self):
        fabs = '{0}/ABS_{0}.m'.format(self.pn)
        copyfile('{0}/{0}.m'.format(self.pn), fabs)
        return fabs

    def read_rule(self, lines):
        rules = []
        for line in lines:
            pre = set(line.split(' -> ')[0].split(' & '))
            cond = line.split(' -> ')[1]

            rules.append((pre, cond))
        # print(rules)
        return rules

    def analyzer(self):
        pattern = re.compile(
            r'ruleset\s+(\w+?)\s*:\s*\w*NODE.*?rule\s+"(\w*?)"\s+(.*?)\s*==>\s*begin\n?\s?(.*?)\s+endrule', re.S)

        rule_text = pattern.findall(self.content)
        self.dealwith_ruleset(rule_text)

    def dealwith_ruleset(self, rule_text):
        for rule in rule_text:
            param, rulename, guard_text, action_text = rule

            action = list(filter(lambda x: x, map(lambda x: x.strip(), action_text.split(';'))))

            guard = set(map(lambda x: x.strip(), guard_text.split('&')))

            invs, data_invs, data_lemma = self.split_guard(param, guard)
            action = self.dealwith_auxdata(action, data_invs)
            abs_action = self.abstract(param, action)

            if not abs_action:
                self.lemma -= data_lemma
                continue

            abs_guard = self.abstract(param, guard)
            abs_invs = self.abstract(param, invs)

            self.write_abs(param, rulename, abs_guard, abs_action, abs_invs)

    def dealwith_auxdata(self, action, data_invs):
        """
        replace local data-related variables with auxiliary data-related variables
        :param action:
        :param data_invs:
        :return:
        """
        if not data_invs: return action
        new_action = []
        for data_inv in data_invs:
            part1, part2 = data_inv.split(' ')[0], data_inv.split(' ')[-1]
            for a in action:
                if part1 == a.split(' ')[-1] and ':=' in a:
                    a = a.replace(part1, part2)
                new_action.append(a)
        return new_action

    def split_guard(self, param, guard):
        next, data_inv, data_lemma = self.find_invs(param, guard)
        prev, next = copy.deepcopy(guard), copy.deepcopy(guard | next)
        while prev != next:
            prev |= next
            new_next, temp_data_inv, temp_data_lemma = self.find_invs(param, prev)
            next |= new_next
            data_inv |= temp_data_inv
            data_lemma |= temp_data_lemma

        return list(next), list(data_inv), data_lemma

    def find_invs(self, param, guard):
        invs, data_inv, data_lemma = set(), set(), set()
        for pre, cond in self.rules:
            if set(guard) & pre == pre:
                invs.add(cond)
                if not re.search(r'\s{0}|\[{0}\]'.format(param), cond):
                    self.lemma.add(' & '.join([p for p in pre]) + ' -> ' + cond)
                    data_lemma.add(' & '.join([p for p in pre]) + ' -> ' + cond)
                if 'data' in cond.lower() and re.search(r'\s{}|\[{}\]'.format(param, param), cond.split(' ')[0]):
                    data_inv.add(cond)
                    self.lemma.add(' & '.join([p for p in pre]) + ' -> ' + cond)
                    data_lemma.add(' & '.join([p for p in pre]) + ' -> ' + cond)
        return invs, data_inv, data_lemma

    def abstract(self, param, guard):
        temp_guard = []
        for g in guard:
            if ("[" + param + "]" not in g) and (len(g) > 0):
                # if re.search('undefine\s.*data', g.lower()):
                #     continue
                if param in g:
                    g = re.sub(r'\b' + param + r'(\b|;)', 'Other', g)
                    ans = re.search(r'(Other\s(=|!=)\s\w+)|(\w+\s(=|!=)\sOther)', g)
                    if ans:
                        ans = ans.group(0)
                        parts = ans.split(' ')
                        if parts[0] in ('i', 'j', 'p') or parts[2] in ('i', 'j', 'p'):
                            g = re.sub(ans, str(parts[1] == '!='), g)
                temp_guard.append(g)
        return temp_guard

    def concat_pre(self, pres):
        with_var, without_var = [], []
        flag_i, flag_j = False, False

        for pre in pres:
            pre = pre.strip('\n')
            if len(pre) > 0:
                # contain only globals
                if not re.search(r'\b[ij]\b',pre):
                    without_var.append(pre)
                    continue
                # contain forall
                elif re.search(r'forall', pre):
                    without_var.append(pre)
                # contain local variables about i
                elif re.search(r'\bi\b', pre):
                    flag_i = True
                    with_var.append(pre)
                # contain local variables about j
                elif re.search(r'\bj\b', pre):
                    flag_j = True
                    with_var.append(pre)

        if flag_i:
            without_var.append('forall i : NODE do \n    %s \n  end' % ' &\n    '.join(with_var))
        elif flag_j:
            without_var.append('forall j : NODE do \n    %s \n  end' % ' &\n    '.join(with_var))

        temp_str = ' &\n  '.join(without_var)

        return temp_str

    def write_abs(self, param, rulename, guard, action, invs):
        if not action:
            return

        data_string = ''
        flag_for, flag_if = False, False

        for a in action:
            if ' data' in a and ' do' not in a: data_string = 'ruleset data: DATA do '
            # if 'for' in a: flag_for = True
            # if 'if' in a: flag_if = True

        with open(self.abs_file, 'a') as fw:
            print('\n' + data_string + 'rule \"ABS_' + rulename + '\"')
            fw.write('\n\n\n' + data_string + 'rule \"ABS_' + rulename + '\"\n')

            pre = list(set(guard) | set(invs))
            if len(pre) == 0:
                print('  True\n')
                fw.write('  True\n')
            else:
                print('  ' + self.concat_pre(pre))
                fw.write('  ' + self.concat_pre(pre) + '\n')

            if not data_string:
                print('==>\n\n' + ';\n '.join(action) + ';\nend;')
                fw.write('==>\n' + ';\n '.join(action) + ';\nend;\n')
            else:
                print('==>\n' + ';\n '.join(action) + ';\nend;end;')
                fw.write('==>' + ';\n '.join(action) + ';\nend;end;\n')

    def write_lemma(self):
        fn_lemma_used = self.pn + '/lemma_used.txt'
        with open(fn_lemma_used, 'w') as fw:
            for cnt, lemma in enumerate(self.lemma, 1):
                fw.write('rule_%d:   %s\n' % (cnt, lemma))
                # print('rule_%d:   %s' % (cnt, lemma))
        return self.lemma


class Refine_3_NODE(object):
    def __init__(self, pn, ins_inv):
        self.pn = pn
        self.origin_protocol = pn + '/' + pn + '.m'
        self.abs_file = self.create_abs()
        self.content = open(self.origin_protocol, 'r').read()
        self.lemma = set()
        self.rules = self.read_rule(ins_inv)

    def create_abs(self):
        fabs = '{0}/ABS_{0}.m'.format(self.pn)
        copyfile('{0}/{0}.m'.format(self.pn), fabs)
        return fabs

    def read_rule(self, lines):
        rules = []
        for line in lines:
            pre = set(line.split(' -> ')[0].split(' & '))
            cond = line.split(' -> ')[1]
            rules.append((pre, cond))
        return rules

    def analyzer(self):
        pattern_ruleset1 = re.compile(
            r'ruleset\s+(\w+?)\s*:\s*\w*NODE\sdo\srule\s+"(\w*?)"\s+(.*?)\s*==>\nbegin\n*(.*?);\s+endrule;', re.S)
        pattern_ruleset2 = re.compile(
            r'ruleset\s+(\w+?)\s*:\s*NODE;\s+(\w+?)\s*:\s*NODE\sdo\srule\s+"(\w*?)"\s+(.*?)\s*==>\nbegin\n*(.*?);\s+endrule',
            re.S)
        # pattern_rule = re.compile(r'\n\nrule\s+"(\w*?)"\s+(.*?)\s*==>\s*(.*?);\s+endrule', re.S)
        pattern_data = re.compile(
            r'ruleset\s*(\w+)\s*:\s*NODE;\s*data\s*:\s*DATA\s+do\srule\s+"(\w*?)"\s+(.*?)\s*==>\nbegin\n*(.*?);\s+endrule',
            re.S)

        self.rule_data(pattern_data)
        self.ruleset_1_pararm(pattern_ruleset1)
        self.ruleset_2_param(pattern_ruleset2)

        print('Strengthened abstracted protocol has been writen in %s. ' % self.abs_file)

    def rule_data(self, pattern_data):
        """

        :param pattern_data: "ruleset i : NODE; data: DATA do rule...endrule;"
        :return: no return
        """
        ruleset = pattern_data.findall(self.content)
        for rule in ruleset:
            param, rulename, guard, action = rule

            guard, action, param = re.sub(param, 'i', guard), re.sub(param, 'i', action), 'i'

            self.dealwith_ruleset_1_param(param, rulename, guard, action)

    def ruleset_1_pararm(self, pattern1):
        """

        :param pattern1:  " ruleset i : NODE do rule "rulename" guard1 & guard2 ==> ac1; ac2; endrule;
        :return: no return, write abstract rules directly
        """
        ruleset = pattern1.findall(self.content)
        for rule in ruleset:
            param, rulename, guard, action = rule
            guard, action, param = re.sub(param, 'i', guard), re.sub(param, 'i', action), 'i'
            self.dealwith_ruleset_1_param(param, rulename, guard, action)

    def ruleset_2_param(self, pattern2):
        ruleset = pattern2.findall(self.content)
        for rule in ruleset:
            param1, param2, rulename, guard, action = rule
            param1, param2 = 'i', 'j'

            guard = re.sub(r'src', 'i', guard)
            guard = re.sub(r'dst', 'j', guard)
            action = re.sub(r'src', 'i', action)
            action = re.sub(r'dst', 'j', action)

            abs_guard1, abs_inv1, abs_action1, lemma_each1, inv, pset1 = self.dealwith_ruleset_2_param(param1, param2,
                                                                                                       guard,
                                                                                                       action)

            if abs_action1:
                self.write_src_dst(param2, rulename + '_' + param1, abs_guard1, abs_inv1, abs_action1, lemma_each1,
                                   pset1)

            abs_guard2, abs_inv2, abs_action2, lemma_each2, inv, pset2 = self.dealwith_ruleset_2_param(param2, param1,
                                                                                                       guard,
                                                                                                       action)
            if abs_action2:
                self.write_src_dst(param1, rulename + '_' + param2, abs_guard2, abs_inv2, abs_action2, lemma_each2,
                                   pset2)

            if abs_action1 and abs_action2:
                abs_guard3 = self.abstract(param2, abs_guard1)
                abs_inv3 = self.abstract(param2, abs_inv1)
                abs_action3 = self.abstract(param2, abs_action1)
                self.write_abs(rulename, abs_guard3, abs_action3, abs_inv3, pset=pset1 | pset2)

    def dealwith_auxdata(self, action, data_invs):
        if not data_invs: return action
        new_action = []
        for data_inv in data_invs:
            part1, part2 = data_inv.split(' ')[0], data_inv.split(' ')[-1]
            for a in action:
                if part1 == a.split(' ')[-1] and ':=' in a:
                    a = a.replace(part1, part2)
                new_action.append(a)

        return new_action

    def dealwith_ruleset_1_param(self, param, rulename, guard, action):
        """

        :param param: i, j
        :param rulename:
        :param guard: raw data of guard
        :param action: raw data of action
        :return: no return, write abstract rules in files directly
        """

        action = list(filter(lambda x: x, map(lambda x: x.strip(), action.split(';'))))

        invs, guard, lemma_each, _, data_invs = self.strengthen(param, guard)
        action = self.dealwith_auxdata(action, data_invs)
        abs_action = self.abstract(param, action)
        if not abs_action:
            self.lemma -= lemma_each
            return

        abs_guard, abs_invs = self.abstract(param, guard), self.abstract(param, invs)
        self.write_abs(rulename + '_' + param, abs_guard, abs_action, abs_invs, lemma_each)

    def dealwith_ruleset_2_param(self, param1, param2, guard, action):
        action = list(map(lambda x: x.strip(), action.split(';')))

        invs, guard, lemma_each, pset, data_invs = self.strengthen(param1, guard, param2)
        action = self.dealwith_auxdata(action, data_invs)
        abs_action = self.abstract(param1, action)
        if not abs_action:
            self.lemma -= lemma_each
            return [], [], [], [], [], []

        abs_guard, abs_invs, abs_pset = self.abstract(param1, guard), self.abstract(param1, invs), self.abstract(param1,
                                                                                                                 pset)

        return abs_guard, abs_invs, abs_action, lemma_each, invs, set(abs_pset)

    def strengthen(self, param, guard, param2=''):
        """

        :param param: i, j
        :param guard: raw data of guard
        :return:
        """
        guard = set(map(lambda x: x.strip(), guard.split('&')))
        next, lemma_each, pset, data_invs = self.find_invs(param, guard, param2)
        prev, next = copy.deepcopy(guard), copy.deepcopy(guard | next)
        while prev != next:
            prev |= next
            new_next, new_lemma, p_temp, temp_data_inv = self.find_invs(param, prev, param2)
            next |= new_next
            lemma_each |= new_lemma
            pset |= p_temp
            data_invs |= temp_data_inv

        return list(next), list(guard), lemma_each, pset, list(data_invs)

    def find_invs(self, param, guard, param2=''):
        lemma_each, invs, pset, data_inv = set(), set(), set(), set()
        for pre, cond in self.rules:
            if set(guard) & pre == pre:
                invs.add(cond)
                if not re.search(r'\s{}|\[{}\]'.format(param, param), cond):
                    self.lemma.add(' & '.join([p for p in pre]) + ' -> ' + cond)
                    lemma_each.add(' & '.join([p for p in pre]) + ' -> ' + cond)
                if re.search(r'\s{}|\[{}\]'.format(param2, param2), cond):
                    if not self._in_pre(pre, param2):
                        cond = re.sub(r'\s{}'.format(param2), ' p', cond)
                        cond = re.sub(r'\[{}\]'.format(param2), '[p]', cond)
                        pset.add(cond)
                if 'data' in cond.lower() and re.search(r'\s{}|\[{}\]'.format(param, param), cond.split(' ')[0]):
                    data_inv.add(cond)
                    self.lemma.add(' & '.join([p for p in pre]) + ' -> ' + cond)
        return invs, lemma_each, pset, data_inv

    def _in_pre(self, pre, param):
        for p in pre:
            if ' ' + param in p or '[' + param + ']' in p:
                return True
        return False

    def abstract(self, param, guard):
        temp_guard = []
        for g in guard:
            if ("[" + param + "]" not in g) and (len(g) > 0):
                if param in g:
                    g = re.sub(r'\b' + param + r'(\b|;)', 'Other', g)
                    ans = re.search(r'(Other\s(=|!=)\s\w+)|(\w+\s(=|!=)\sOther)', g)
                    if ans:
                        ans = ans.group(0)
                        parts = ans.split(' ')
                        if parts[0] in ('i', 'j', 'Home', 'p') or parts[2] in ('i', 'j', 'Home', 'p'):
                            g = re.sub(ans, str(parts[1] == '!='), g)
                temp_guard.append(g)
        return temp_guard

    def concat_pre(self, pres, forall_i=False, forall_j=False):
        with_var, without_var = [], []
        flag_i, flag_j = False, False

        for pre in pres:
            if len(pre) == 0:
                continue
            if '[i]' not in pre and '[j]' not in pre and not re.search(r'.*(\si|i\s|\sj|j\s)', pre):
                without_var.append(pre)
                continue
            if re.search(r'.*(\si|i\s|\[i\])', pre):
                flag_i = True
                if re.search(r'.*(forall\si)', pre):
                    forall_i = True
            elif re.search(r'.*(\sj|j\s|\[j\])', pre):
                flag_j = True
                if re.search(r'.*(forall\sj)', pre):
                    forall_j = True
            with_var.append(pre)

        temp_str = ''

        if not without_var and not flag_j and not flag_i:
            return temp_str
        elif without_var and not flag_i and not flag_j:
            return '\n & '.join(without_var)
        elif without_var and (flag_i or flag_j):
            temp_str += '\n & '.join(without_var)
            temp_str += ' &\n  '
        elif not without_var and (flag_i or flag_j):
            temp_str += ' \n  '

        temp_str += 'forall i : NODE do ' if flag_i and not forall_i else ''
        temp_str += 'forall j : NODE do ' if flag_j and not forall_j else ''
        temp_str += '\n  '
        temp_str += 'i != j -> ' if flag_i and flag_j else ''
        temp_str += '(' + ')\n & ('.join(with_var) + ')\n'
        if flag_i and flag_j:
            temp_str += '  end\nend'
        elif forall_j or forall_i:
            temp_str += ''
        else:
            temp_str += 'end'

        return temp_str

    def write_abs(self, rulename, guard, action, invs, lemma_each=set(), pset=set()):
        pre = list(set(guard) | set(invs))
        if not pre:
            return
        data_string = ''

        flag_if = False

        for a in action:
            if re.search(r'\bdata\b',a):
                data_string = 'ruleset data: DATA do '

        with open(self.abs_file, 'a') as fw:

            print('\n' + data_string + 'rule \"ABS_' + rulename + '\"')
            fw.write('\n' + data_string + 'rule \"ABS_' + rulename + '\"\n')

            pres = self.concat_pre(pre)
            print('  ' + pres)
            fw.write('  ' + pres + '\n')

            if pset:
                fw.write(' & forall p : NODE do\n   ' + '\n & '.join(pset) + ' end\n')
                print((' & forall p : NODE do\n   ' + '\n & '.join(pset) + ' end\n'))

            if not data_string and not flag_if:
                print('==>\n\n' + ';\n '.join(action) + ';\nend;')
                fw.write('==>\n' + ';\n '.join(action) + ';\nend;\n')
            else:
                print('==>\n' + ';\n '.join(action) + ';\nend;end;')
                fw.write('==>' + ';\n '.join(action) + ';\nend;end;\n')

    def write_src_dst(self, param, rulename, guard, invs, action, lemma_each=set(), pset=set()):
        # if len(action) <= 0:
        #     return
        pre = list(set(guard) | set(invs))
        if not pre:
            return

        with open(self.abs_file, 'a') as fw:
            print('\n\nruleset ' + param + ' : NODE do rule \"ABS_' + rulename + '\"')
            fw.write('\n\nruleset ' + param + ' : NODE do rule \"ABS_' + rulename + '\"\n')

            if param == 'i':
                f_i, f_j = True, False
            elif param == 'j':
                f_i, f_j = False, True
            else:
                f_i, f_j = False, False

            pres = self.concat_pre(pre, forall_i=f_i, forall_j=f_j)
            print('  ' + pres)
            fw.write('  ' + pres + '\n')
            if pset:
                fw.write(' & forall p : NODE do\n   ' + '\n & '.join(pset) + ' end\n')
                print((' & forall p : NODE do\n   ' + '\n & '.join(pset) + ' end\n'))

            print('==>\n' + ';\n '.join(action) + ';\nend;end;')
            fw.write('==>\n' + ';\n '.join(action) + ';\nend;end;\n')

    def write_lemma(self):
        fn_lemma_used = self.pn + '/lemma_used.txt'
        with open(fn_lemma_used, 'w') as fw:
            for cnt, lemma in enumerate(self.lemma, 1):
                fw.write('rule_%d:   %s\n' % (cnt, lemma))
        return self.lemma
