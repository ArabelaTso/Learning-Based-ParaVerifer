import re


class TypeDef(object):
    """
    Deal with type and const in murphi

    It can deal with the following definition:
        const
            NODE_NUM : 3;
            DATA_NUM : 2;
        type
            NODE : scalarset(NODE_NUM);
            DATA : 1..DATA_NUM;

    and turn it into:
        self.type = {NODE:NODE_NUM, DATA: DATA_NUM}
        self.const = {NODE_NUM : 3, DATA_NUM:2}
        para = ["NODE"] -- because the type used to represent 'processor' is usually used with 'array [__] of'
    """

    def __init__(self, text):
        self.text = text
        self.type = {}
        self.const = {}
        self.para = []
        self.eval_scalarset()
        self.eval_const()

    def eval_scalarset(self):
        """
        collect types from two kinds of type:
            1. NODE: 1..NODE_NUM
            2. NODE: scalarset(NODE_NUM)

        :param text: murphi description
        :return: NONE
        """
        scalarsets = re.findall(r'(\w*?)\s*:\s*\w+?\s*\.\.\s*(\w+?)\s*;', self.text, re.S)
        scalarsets2 = re.findall(r'(\w*?)\s*:\s*scalarset\((\w+)\)', self.text, re.S)

        self.type.update({name: num for name, num in scalarsets})
        self.type.update({name: num for name, num in scalarsets2})

    def eval_arr(self):
        """
        For now, the type that will be used as a represent of a processor usually can be found in form of :
        array [NODE] of ...
        So identifying it using 'array [\w+] of', and check whether it is in self.types.
        :return:
        """
        pattern = re.compile(r'array\s*\[\s?(\w+)\s?\]\s*of\s*.+')
        array = list(set(re.findall(pattern, self.text)))
        self.para = [a for a in array if a in self.type]

    def eval_const(self):
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', self.text)
        self.const = {v: d for v, d in config}

    def reset_const(self, para, num):
        """
        reset the configuration by the given parameter name and new number
        :param para:
        :param num:
        :return: new murphi description
        """
        para_const = self.type[para]
        self.text = re.sub(r'%s\s?:\s?(\d+?)\s?;' % para_const, r"%s : %d;" % (para_const, num), self.text)
        return self.text


class Field(object):
    def __init__(self):
        self.para_dict = {}
        self.content = []


class Guard(object):
    def __init__(self, text, param_name_dict):
        self.param_name_dict = param_name_dict
        self.text = text
        self.guards = set()
        self.field = Field()
        self.field.para_dict = param_name_dict
        self.sparse()

    def normalize_field(self, field=None):
        guards = set()
        if not field:
            field = self.field

        def para_repl(match):
            return field.para_dict[match.group()] if match.group() in field.para_dict else match.group()

        for f in field.content:
            if type(f) is str:
                guards.add(re.sub('\w+', para_repl, f))
            elif type(f) is Field:
                guards |= self.normalize_field(f)
        return guards

    def sparse(self):
        def para_repl(match):
            return self.param_name_dict[match.group()] if match.group() in self.param_name_dict else match.group()

        split_guard = list(map(lambda x: x.strip(), self.text.split('&')))
        for g in split_guard:
            if g.startswith(('forall', '!forall')):
                self.deal_forall(g)
            elif g.startswith(('exists', '!exists')):
                self.deal_exist(g)
            else:
                self.guards.add(re.sub('\w+', para_repl, g))
                self.field.content.append(g)

    def deal_forall(self, text):
        pattern = re.compile(r'!?forall(.*?)do(.*)end', re.S)
        params, content = re.findall(pattern, text)[0]
        temp_field = Field()

        param_name_dict = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        for var, type in param_name_dict.items():
            # for var, type, statesment in forall_parts:
            parts = set(map(lambda x: re.sub(var, type, x.strip()),
                            filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            temp_field.content = list(map(lambda x: x.strip(),
                                          filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            self.guards |= parts
            self.field.content.append(temp_field)

    def deal_exist(self, text):
        pattern = re.compile(r'!?exists(.*?)do(.*)end', re.S)
        params, content = re.findall(pattern, text)[0]
        temp_field = Field()

        param_name_dict = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        for var, type in param_name_dict.items():
            # for var, type, statesment in forall_parts:
            parts = set(map(lambda x: re.sub(var, type, x.strip()),
                            filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            temp_field.content = list(map(lambda x: x.strip(),
                                          filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            self.guards |= parts
            self.field.content.append(temp_field)


class Action(object):
    def __init__(self, text, param_name_dict):
        self.param_name_dict = param_name_dict
        self.text = text
        self.actions = set()
        self.field = Field()
        self.field.para_dict = param_name_dict
        self.sparse()

    def normalize_field(self, field=None):
        norm_actions = set()
        if not field:
            field = self.field

        def para_repl(match):
            return field.para_dict[match.group()] if match.group() in field.para_dict else match.group()

        for f in field.content:
            if type(f) is str:
                norm_actions.add(re.sub('\w+', para_repl, f))
            elif type(f) is Field:
                norm_actions |= self.normalize_field(f)
        return norm_actions

    def sparse(self):
        def para_repl(match):
            return self.param_name_dict[match.group()] if match.group() in self.param_name_dict else match.group()

        split_action = list(filter(lambda x: x, map(lambda x: x.strip(), self.text.split(';'))))
        for a in split_action:
            if a.startswith(('forall', '!forall')):
                self.deal_forall(a)
            elif a.startswith(('exists', '!exists')):
                self.deal_exist(a)
            else:
                self.actions.add(re.sub('\w+', para_repl, a))
                self.field.content.append(a)

    def deal_forall(self, text):
        pattern = re.compile(r'!?forall(.*?)do(.*)end', re.S)
        params, content = re.findall(pattern, text)[0]
        temp_field = Field()

        param_name_dict = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        for var, type in param_name_dict.items():
            # for var, type, statesment in forall_parts:
            parts = set(map(lambda x: re.sub(var, type, x.strip()),
                            filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            temp_field.content = list(map(lambda x: x.strip(),
                                          filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            self.actions |= parts
            self.field.content.append(temp_field)

    def deal_exist(self, text):
        pattern = re.compile(r'!?exists(.*?)do(.*)end', re.S)
        params, content = re.findall(pattern, text)[0]
        temp_field = Field()

        param_name_dict = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        for var, type in param_name_dict.items():
            # for var, type, statesment in forall_parts:
            parts = set(map(lambda x: re.sub(var, type, x.strip()),
                            filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            temp_field.content = list(map(lambda x: x.strip(),
                                          filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
            self.actions |= parts
            self.field.content.append(temp_field)


class Ruleset(object):
    def __init__(self, text, type):
        self.text = text
        self.type = type
        self.guards = set()
        self.deal_rulesets()

    def extract_guards(self):
        # print('\nextract %d guard formulas' % len(self.guards))
        # print('\n'.join(self.guards))
        # print('---------------------')

        return self.guards

    def deal_rulesets(self):
        pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
        rulesets = pattern.findall(self.text)

        for params, rules_str in rulesets:
            param_name_dict = analyzeParams(params)
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                rulename, guards_obj, actions_obj = self.deal_rule(each_rule, param_name_dict)
                self.guards |= guards_obj.normalize_field()

    def deal_rule(self, rule_text, param_name_dict):
        pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
        rule_name, guards, actions = pattern.findall(rule_text)[0]

        # deal with guard
        guard_obj = Guard(guards, param_name_dict)
        action_obj = Action(actions, param_name_dict)

        # print(rule_name)
        # print(guard_obj.field.para_dict)
        # print(guard_obj.field.content)

        # print(action_obj.field.para_dict)
        # print(action_obj.field.content)

        return rule_name, guard_obj, action_obj
#
# class Rule(object):
#     def __init__(self,text,param_name_dict):
#         self.text = text
#         self.param_name_dict = param_name_dict
#         self.guard_obj = Guard(guards, param_name_dict)
#         # action_obj = Action(actions, param_name_dict)
#

def analyzeParams(params):
    """
    @param params: as `i:Node; j:Node`
    @return a tuple as `{'i': 'Node', 'j': 'Node'}
    """
    if not params: return {}, '[]'
    parts = params.split(';')
    param_name_dict = {}
    for p in parts: param_name_dict[p.split(':')[0].strip()] = p.split(':')[1].strip()

    return param_name_dict


class Protocol(object):
    def __init__(self, name):
        self.name = name
        self.text = open('{0}/{0}.m'.format(self.name)).read()
        # self.show_config()

    def show_config(self):
        """
        Reads prtocol in murphi language

        return protocol description, and configuration
        i.e., NODE: 2; DATA: 3;
        """
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', self.text)
        print('---------------------\nConfiguration parameters: ')
        for name, num in config:
            print('{} : {}'.format(name, num))
        print('---------------------\n')

    def execute(self):
        paras = self.extract_par()
        return paras, self.extract_guards()

    def extract_par(self):
        typedf = TypeDef(self.text)
        typedf.eval_arr()
        if not typedf.para:
            raise ValueError
        # else:
        #     print('Parameter:', ','.join(typedf.para))
        return typedf.para

    def extract_guards(self):
        ruleset = Ruleset(self.text, set())
        guards = ruleset.extract_guards()
        return guards

    def set_paras(self, para, num):
        typedf = TypeDef(self.text)
        self.text = typedf.reset_const(para, num)
        with open('{0}/{0}.m'.format(self.name),'w') as f:
            f.write(self.text)


# class Rule:
#     def __init__(self, rule_text, param_name_dict):
#         self.rule_name = ''
#         self.paras = param_name_dict
#         self.guards = set()
#         self.actions = set()
#         self.usedInvs = set()
#         self.sparse(rule_text)
#
#     def sparse(self, rule_text):
#         pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
#         self.rule_name, guards, actions = pattern.findall(rule_text)[0]


#
# content = open('german/german.m').read()
# ruleset = Ruleset(content, set())
# ruleset.extract_guards()
# ruleset.deal_rulesets()
#
