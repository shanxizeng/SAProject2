from z3 import *

all_consts = {}
target_param = []

class examp :
    def __init__(self, example) :
        self.consts = {}
        self.funcs = {}
        self.constraints = []
        self.target_params = {}
        self.target_fun = example[len(example)-1]
        for func in example :
            if func != self.target_fun :
                if func.arity() == 0 :
                    if func.name() not in all_consts :
                        all_consts[func.name()] = example[func]
                    self.consts[func.name()] = example[func]
                else :
                    self.funcs[func.name()] = example[func]
        return
    
    def call(self, expr) :
        if type(expr) == list :
            if expr[0] in self.funcs :
                para = []
                for term in expr[1:] :
                    para.append(self.call(term))
                return self.funcs[expr[0]](para)
            elif expr[0] == '+' :
                return self.call(expr[1]) + self.call(expr[2])
            elif expr[0] == '-' :
                if len(expr) == 2 :
                    return - self.call(expr[1])
                else :
                    return self.call(expr[1]) - self.call(expr[2])
            elif expr[0] == 'ite' :
                if self.call(expr[1]) :
                    return self.call(expr[2])
                else :
                    return self.call(expr[3])
            elif expr[0] == '*' :
                return self.call(expr[1]) + self.call(expr[2])
            elif expr[0] == 'div' :
                return self.call(expr[1]) // self.call(expr[2])
            elif expr[0] == 'mod' :
                return self.call(expr[1]) % self.call(expr[2])
            elif expr[0] == '<=' :
                return self.call(expr[1]) <= self.call(expr[2])
            elif expr[0] == '>=' :
                return self.call(expr[1]) >= self.call(expr[2])
            elif expr[0] == '=' :
                return self.call(expr[1]) == self.call(expr[2])
            elif expr[0] == 'not' :
                return not self.call(expr[1])
            elif expr[0] == 'or' :
                return self.call(expr[1]) or self.call(expr[2])
            elif expr[0] == 'and' :
                return self.call(expr[1]) and self.call(expr[2])
            elif expr[0] == '=>' :
                return not self.call(expr[1]) or self.call(expr[2])
            else :
                print(expr)
                assert False
        elif type(expr) == str :
            if expr in all_consts or expr in self.target_params :
                if expr in self.target_params :
                    return self.target_params[expr] 
                elif expr in self.consts :
                    temp = self.consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    else : 
                        print(temp)
                        assert False
                else :
                    temp = all_consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    else : 
                        print(temp)
                        assert False
            else :
                print(expr)
                assert False
        elif type(expr) == tuple :
            if expr[0] == 'Int' :
                return expr[1]
            else :
                print(expr)
                assert False
        else :
            print(expr)
            assert False
        return

    def eval(self, expr) :
        if type(expr) == list :
            if expr[0] in self.funcs :
                para = []
                for term in expr[1:] :
                    para.append(self.eval(term))
                return self.funcs[expr[0]](para)
            elif expr[0] == self.target_fun.name() :
                for i in range(1, len(expr)) :
                    temp = self.eval(expr[i])
                    self.target_params[target_param[i-1]] = temp
                return self.call(self.value)
            elif expr[0] == '+' :
                return self.eval(expr[1]) + self.eval(expr[2])
            elif expr[0] == '-' :
                if len(expr) == 2 :
                    return - self.eval(expr[1])
                else :
                    return self.eval(expr[1]) - self.eval(expr[2])
            elif expr[0] == 'ite' :
                if self.eval(expr[1]) :
                    return self.eval(expr[2])
                else :
                    return self.eval(expr[3])
            elif expr[0] == '*' :
                return self.eval(expr[1]) + self.eval(expr[2])
            elif expr[0] == 'div' :
                return self.eval(expr[1]) // self.eval(expr[2])
            elif expr[0] == 'mod' :
                return self.eval(expr[1]) % self.eval(expr[2])
            elif expr[0] == '<=' :
                return self.eval(expr[1]) <= self.eval(expr[2])
            elif expr[0] == '>=' :
                return self.eval(expr[1]) >= self.eval(expr[2])
            elif expr[0] == '=' :
                return self.eval(expr[1]) == self.eval(expr[2])
            elif expr[0] == 'not' :
                return not self.eval(expr[1])
            elif expr[0] == 'or' :
                return self.eval(expr[1]) or self.eval(expr[2])
            elif expr[0] == 'and' :
                return self.eval(expr[1]) and self.eval(expr[2])
            elif expr[0] == '=>' :
                return not self.eval(expr[1]) or self.eval(expr[2])
            else :
                print(expr)
                assert False
        elif type(expr) == str :
            if expr in all_consts :
                if expr in self.consts :
                    temp = self.consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    else : 
                        print(temp)
                        assert False
                else :
                    temp = all_consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    else : 
                        print(temp)
                        assert False
            else :
                print(expr)
                assert False
        elif type(expr) == tuple :
            if expr[0] == 'Int' :
                return expr[1]
            else :
                print(expr)
                assert False
        else :
            print(expr)
            assert False

    def check(self, expr, constraints) :
        # print(2, expr, self.consts)
        self.value = expr
        # print(self.value)
        for constraint in constraints :
            # print(constraint)
            temp = self.eval(constraint)
            if not temp :
                return True
        return False

class examples :
    def __init__(self) :
        self.constraints = []
        self.examples = []
        return 

    def check(self, expr) :
        for exam in self.examples :
            if exam.check(expr, self.constraints) :
                return True
        return False

    def add_example(self, example) :
        self.examples.append(examp(example))
        return
    
    def add_constraint(self, constraint) :
        if len(constraint) == 2 :
            self.constraints.append(constraint[1])
        else :
            self.constraints.append(constraint[1:])
        return