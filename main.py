import sys
import sexp
import pprint
import translator
import bottomup
import examples
import listTrie
import BVsolver

prevexamples = examples.examples()

def Extend(Stmts,Productions):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i],Productions)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
    return ret

def stripComments(bmFile):
    noComments = '(\n'
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + '\n)'

def count_size(Stmts) :
    l = 0
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            l = l + count_size(Stmts[i])
        else :
            l = l + 1
    return l


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    # print(bm)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    # pprint.pprint(bmExpr)
    checker=translator.ReadQuery(bmExpr)
    #print (checker.check('(define-fun f ((x Int)) Int (mod (* x 3) 10)  )'))
    #raw_input()
    SynFunExpr = []
    Constraints = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    # print(bmExpr)
    for expr in bmExpr:
        # print(expr)
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
        elif expr[0]=='constraint' :
            Constraints.append(expr)
        elif expr[0]=='declare-var' :
            if expr[2]=='Int' :
                examples.all_consts[expr[1]]=0
        elif expr[0]=='set-logic' :
            # print(expr)
            if expr[1] == 'BV' :
                listTrie.isLIA = 0
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    examples.target_func = SynFunExpr[1]
    # print(SynFunExpr)
    for i in range(0, len(SynFunExpr[2])) :
        examples.target_param.append(SynFunExpr[2][i][0])
    #print(FuncDefine)
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        Productions[NTName] = NonTerm[2]
    # print(Productions)
    if listTrie.isLIA == 0 :
        temp = BVsolver.work(checker, Constraints)
        # print(temp)
        FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) 
        CurrStr = translator.toString(temp)
        Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] 
        print(Str)
        exit()
    useBottomUp = 1
    if useBottomUp :
        while not bottomup.solve(Type, Productions, StartSym, checker, FuncDefine, Constraints) :
            continue
    else :
        Count = 0
        Ans  = ""
        for i in range(20) :
            flag = 0
            TE_set = set()
            BfsQueue = [[StartSym]] #Top-down
            while(len(BfsQueue)!=0):
                Curr = BfsQueue.pop(0)
                TryExtend = Extend(Curr,Productions)
                if(len(TryExtend)==0): # Nothing to
                    #print(FuncDefine)
                    # print("find", Curr)
                    FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
                    CurrStr = translator.toString(Curr)
                    #SynFunResult = FuncDefine+Curr
                    #Str = translator.toString(SynFunResult)
                    Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
                    Count += 1
                    # print (Count)
                    # print (Str)
                    # if Count % 100 == 1:
                        # print (Count)
                        # print (Str)
                        #raw_input()
                    #print '1'
                    counterexample = checker.check(Str)
                    #print counterexample
                    if(counterexample == None): # No counter-example
                        Ans = Str
                        flag = 1
                        break
                    #print '2'
                #print(TryExtend)
                #raw_input()
                #BfsQueue+=TryExtend
                for TE in TryExtend:
                    TE_str = str(TE)
                    if count_size(TE) > i :
                        continue
                    if not TE_str in TE_set:
                        BfsQueue.append(TE)
                        TE_set.add(TE_str)
            if flag == 1 :
                break

        print(Ans)

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
