import translator
from main import prevexamples

def contains(Exprs, Nums, Term) :
    return Nums in Exprs and Term in Exprs[Nums]

def searchNewExpr(Exprs, Productions, Nondetermain, Size) :
    Ret = {}
    for Nonterm in Productions :
        Proexprs = Productions[Nonterm]
        possible_list = []
        for terms in Proexprs :
            l = Size - len(terms)
            if type(terms) != list :
                if type(terms) != tuple and terms in Nondetermain :
                    if contains(Exprs, Size, terms) :
                        for term in Exprs[Size][terms] :
                            possible_list.append(term)
                else :
                    if Size == 1 :
                        possible_list.append(terms)
                continue
            Nontermnum = 0
            for term in terms :
                if term in Nondetermain :
                    Nontermnum += 1
            if Nontermnum == 0 :
                if len(terms) == Size :
                    possible_list.append(terms)
            elif Nontermnum == 1 :
                for i in range(len(terms)) :
                    if terms[i] in Nondetermain and contains(Exprs, l+1, terms[i]) :
                        for j in Exprs[l+1][terms[i]] :
                            possible_list.append(terms[:i]+[j]+terms[i+1:])
                        break
            elif Nontermnum == 2 :
                for i in range(len(terms)) :
                    if terms[i] in Nondetermain :
                        for j in range(i+1,len(terms)) :
                            if terms[j] in Nondetermain :
                                for li in range(1, Size) :
                                    if contains(Exprs, li, terms[i]) and contains(Exprs, l+2-li, terms[j]) :
                                        for ti in Exprs[li][terms[i]] :
                                            for tj in Exprs[l+2-li][terms[j]] :
                                                possible_list.append(terms[:i]+[ti]+terms[i+1:j]+[tj]+terms[j+1:])
                                break
                        break
            else :
                for i in range(len(terms)) :
                    if terms[i] in Nondetermain :
                        for j in range(i+1,len(terms)) :
                            if terms[j] in Nondetermain :
                                for k in range(j+1, len(terms)) :
                                    if terms[k] in Nondetermain :
                                        for li in range(1, Size) :
                                            for lj in range(1, Size) :
                                                if contains(Exprs, li, terms[i]) and contains(Exprs, lj, terms[j]) and contains(Exprs, l+3-li-lj, terms[k]) :
                                                    for ti in Exprs[li][terms[i]] :
                                                        for tj in Exprs[lj][terms[j]] :
                                                            for tk in Exprs[l+3-li-lj][terms[k]] :
                                                                possible_list.append(terms[:i]+[ti]+terms[i+1:j]+[tj]+terms[j+1:k]+[tk]+terms[k+1:])
                                        break
                                break
                        break
        Ret[Nonterm] = possible_list
    return Ret

def solve(Type, Productions, Start, checker, FuncDefine, Constraints) :
    Exprs = {}
    Nondetermain = set()
    for Nonterm in Productions :
        Nondetermain.add(Nonterm)
    for constraint in Constraints :
        prevexamples.add_constraint(constraint)
    size = 1
    count = 0
    while 1 :
        temp = searchNewExpr(Exprs, Productions, Nondetermain, size)
        Exprs[size] = temp
        size += 1
        for Nonterm in Nondetermain :
            if Type[Nonterm] == Type[Start] :
                for expr in temp[Nonterm] :
                    # print(1, expr)
                    count += 1
                    if count == 1000 :
                        return
                    if prevexamples.check(expr) :
                        continue
                    FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True)
                    CurrStr = translator.toString(expr)
                    Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1]
                    counterexample = checker.check(Str)
                    if counterexample == None : # No counter-example
                        print(Str)
                        return
                    else :
                        # print(counterexample)
                        prevexamples.add_example(counterexample)
                        # print(type(counterexample),counterexample)
                        # for i in counterexample :
                        #     print(counterexample[i],type(counterexample[i]))
                        # print(counterexample, Str)
    return