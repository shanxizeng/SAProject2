import math
import sys
import sexp
import pprint
import translator
import time
import random
from queue import PriorityQueue
from bitset import BitSet
from queue import Queue

Token2Prog = {}
checker = None
FuncDefine = None

def stripComments(bmFile):
    noComments = '(\n'
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + '\n)'

def getOp(Stmts):
    while type(Stmts) == list:
        Stmts = Stmts[0]
    return Stmts

def Prog2Token(prog):
    Str = str(prog)
    Token2Prog[Str] = prog
    return Str
    

def Extend(Stmts, Productions, cost):
    ret = []
    lastOp = ''
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i], Productions, cost)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append((extended[0], Stmts[0:i]+[extended[1]]+Stmts[i+1:]))
                break
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                Op = getOp(extended[0])
                if lastOp == 'bvnot' and Op == 'bvnot': continue
                #if lastOp == 'shr1' and Op == 'shl1': continue
                #if lastOp == 'shl1' and Op == 'shr1': continue
                if Op == 'if0': continue
                ret.append((cost + 1, Stmts[0:i]+[extended]+Stmts[i+1:]))
            break
        lastOp = getOp(Stmts[i])
    return ret

def ParseBmExpr(bmExpr):
    SynFunExpr = []
    Constraints = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
        elif expr[0] == 'constraint':
            assert len(expr[1]) == 3
            assert expr[1][0] == '='
            Constraints.append((expr[1][1][1][1], expr[1][2][1]))
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    #print(FuncDefine)
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type
    #print(SynFunExpr[4])
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        Productions[NTName] = NonTerm[2]
    
    for NTName in Productions.keys():
        i = 0
        while True:
            if i >= len(Productions[NTName]): break
            if Productions[NTName][i][0][0] == '>':
                Productions[NTName].pop(i)
            else: i += 1
            
    return FuncDefine, Productions, Constraints

def simulate(prog, arg):
    #print(prog)
    if type(prog) == tuple:
        return prog[1]
    if prog == 'x':
        return arg
    
    op = prog[0]
    if type(op) == list: return simulate(op, arg)
    if op == 'bvnot':
        return simulate(prog[1],arg) ^ ((1<<64) - 1)
    elif op == 'shl1':
        return (simulate(prog[1],arg) << 1) % ((1<<64))
    elif op == 'shr1':
        return simulate(prog[1],arg) >> 1
    elif op == 'shr4':
        return simulate(prog[1],arg) >> 4
    elif op == 'shr16':
        return simulate(prog[1], arg) >> 16
    elif op == 'bvand':
        return simulate(prog[1], arg) & simulate(prog[2], arg)
    elif op == 'bvor':
        return simulate(prog[1], arg) | simulate(prog[2], arg)
    elif op == 'bvxor':
        return simulate(prog[1], arg) ^ simulate(prog[2], arg)
    elif op == 'bvadd':
        return (simulate(prog[1], arg) + simulate(prog[2], arg)) % ((1<<64))
    elif op == 'if0':
        return simulate(prog[2], arg) if simulate(prog[1], arg) == 1 else simulate(prog[3], arg)
    elif len(op) == 1 or type(op) == tuple: return simulate(op, arg)
    else:
        print(op) 
        assert False
    
def test(prog, Constraints, decision = False):
    testResult = BitSet(len(Constraints))
    for i in range(len(Constraints)):
        constraint = Constraints[i]
        arg = constraint[0]
        stdResult = constraint[1]
        realResult = simulate(prog, arg)
        if decision and realResult == 1: testResult.set(i)
        elif not decision and stdResult == realResult: testResult.set(i)
    return testResult


def pushq(q, cost, prog):
    token = str(prog)
    if token in Token2Prog:
        return
    Token2Prog[token] = prog
    q.put((cost, token))
    
def popq(q):
    cost, token = q.get()
    return cost, Token2Prog[token]

def solver(Productions, Constraints, thres, decision = False):
    q = Queue()
    Token2Prog.clear()
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    pushq(q, 1, [StartSym])
    Progs = []
    cover = BitSet(len(Constraints))
    while not q.empty():
        cost , prog = popq(q) 
        #print(cost, prog)
        TryExtend = Extend(prog, Productions, cost)
        if len(TryExtend) == 0:
            #print(prog)
            testResult = test(prog, Constraints, decision)
            
            if decision and not (testResult.none() or testResult.full()):
                Progs.append((prog, testResult))
                cover = cover.union(testResult)
            elif not decision and not testResult.none():
                Progs.append((prog, testResult))
                cover = cover.union(testResult)
            #if not decision and cover.full():
                #return Progs
            #print(cover.toString())
        for extended in TryExtend:
            if extended[0] < thres:
                pushq(q, extended[0], extended[1])
    #print(cover.toString())
    if not decision and cover.full():
        return Progs
    if decision:    
        return Progs
    return []

def singleProg(Progs):
    for prog, testResult in Progs:
        if testResult.full(): return prog
    return None

def legalDecisions(progs, decisions, Conditions):
    progResult = [prog[1] for prog in progs]
    decisionResult = [decision[1] for decision in decisions]
    visited = [False for _ in range(len(Conditions))]
    
    def complete(eqClass):
        for res in progResult:
            cover = True
            for j in eqClass:
                if res.get(j) == 0:
                    cover = False
                    break
            if cover: return True
        return False
    
    for i in range(len(Conditions)):
        if visited[i]: continue
        visited[i] = True
        eqClass = [i]
        
        eq = True
        for j in range(i+1, len(Conditions)):
            if visited[j]: continue
            for res in decisionResult:
                if not res.get(i) == res.get(j):
                    eq = False
                    break
            if eq:
                visited[j] = True
                eqClass.append(j)
        
        if not complete(eqClass): return False
    return True
        

def crossEntropy(x, y):
    #print(x,y)
    if x == 0 or y == 0:
        return 0
    r = x / (x + y)
    return -r * math.log(r) - (1 - r) * math.log(1 - r)

def crossSquare(x, y):
    if x == 0 or y == 0:
        return 0
    r = x / (x + y)
    return r * (1 - r)

def synthesis(Progs, Decisions, Conditions, mode = 'default'):
    #print(mode)
    for prog, progResult in Progs:
        if progResult.union(Conditions).full():
            return prog
    
    bestScore = -19260817
    selectedIndex = 0
    mask = Conditions.complement()
    cnt = mask.count()
    if mode == 'default':
        selectedIndex = random.randint(0, len(Decisions) - 1)
    else:
        for i in range(len(Decisions)):
            score = 0
            decisionResult = Decisions[i][1]
            for _ , progResult in Progs:
                c11 = decisionResult.intersect(progResult.intersect(mask)).count()
                c00 = decisionResult.complement().intersect(progResult.complement().intersect(mask)).count()
                c01 = decisionResult.complement().intersect(progResult.intersect(mask)).count()
                c10 = decisionResult.intersect(progResult.complement().intersect(mask)).count()
                
                tr = (c11 + c10) / cnt
                fr = (c01 + c00) / cnt
                if mode == 'crossEntropy':
                    score += crossEntropy(c11 + c01, c00 + c10) - tr * crossEntropy(c11, c10) - fr * crossEntropy(c00, c01)
                elif mode == 'crossSquare':
                    score += crossSquare(c11 + c01, c00 + c10) - tr * crossSquare(c11, c10) - fr * crossSquare(c00, c01)
                else: assert False
            
            if score > bestScore:
                selectedIndex, bestScore = i, score
        
    
    #selectedIndex = random.randint(0, len(Decisions)-1)
    decisionResult = Decisions[selectedIndex][1]
    
    trueBranch = synthesis(Progs, Decisions, Conditions.union(decisionResult.complement()), mode)
    falseBranch = synthesis(Progs, Decisions, Conditions.union(decisionResult), mode)
    
    return ['if0', Decisions[selectedIndex][0], trueBranch, falseBranch]
    

if __name__ == "__main__":
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    checker=translator.ReadQuery(bmExpr)
   # print (checker.check('(define-fun f ((x Int)) Int (mod (* x 3) 10)  )'))
    #raw_input()
    FuncDefine, Productions, Constraints = ParseBmExpr(bmExpr)    
    #pprint.pprint(Productions)
    thres = 2
    progs = []
    while True:
        #print(thres)
        #time.sleep(1)
        progs = solver(Productions, Constraints, thres)
        #print(progs)
        #time.sleep(1)
        if not len(progs) == 0:
            ##print([(prog[0], prog[1].toString()) for prog in progs])
            break
        thres += 1
    
    prog = singleProg(progs)
    if not prog == None:
        FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
        CurrStr = translator.toString(prog)
        Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
        print(Str)
        exit(0)
    
    thres = 3
    decisions = []
    while True:
        #print(thres)
        decisions = solver(Productions, Constraints, thres, decision = True)
        #print(decisions)
        if not len(decisions) == 0 and legalDecisions(progs, decisions, Constraints):
            #print(len(decisions))
            #print([(prog[0], prog[1].toString()) for prog in decisions])
            break
        thres += 1
    
    hasException = False
    try:
        prog = synthesis(progs, decisions, BitSet(len(Constraints)), mode = 'crossEntropy')
    except Exception as e:
        hasException = True
    
    if hasException:
        hasException = False
        try:
            prog = synthesis(progs, decisions, BitSet(len(Constraints)), mode = 'crossSquare')
        except Exception as e:
            hasException = True
            
    while hasException:
        hasException = False
        try:
            prog = synthesis(progs, decisions, BitSet(len(Constraints)), mode = 'default')
        except Exception as e:
            hasException = True
            
    
    #prog = synthesis(progs, decisions, BitSet(len(Constraints)))
    FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
    CurrStr = translator.toString(prog)
    Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
    print(Str)
    exit(0)
        
        
    
    #FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
    #CurrStr = translator.toString(prog)
    #SynFunResult = FuncDefine+Curr
    #Str = translator.toString(SynFunResult)
    #Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
    #print(Str)
    
    
    
    