from random import sample

bvs = []
constraint_count = 0
poss_bv = {}

def enumerate_bv(size) :
    ans = []
    for bv in bvs[size-1] :
        ans.append(['bvnot',bv])
        ans.append(['shl',bv,1])
        ans.append(['shl',bv,2])
        ans.append(['shl',bv,4])
        ans.append(['shl',bv,8])
        ans.append(['shl',bv,16])
        ans.append(['shr',bv,1])
        ans.append(['shr',bv,2])
        ans.append(['shr',bv,4])
        ans.append(['shr',bv,8])
        ans.append(['shr',bv,16])
    for i in range(1, size // 2) :
        for bvl in bvs[i] :
            for bvr in bvs[size-i-1] :
                ans.append(['bvand',bvl,bvr])
                ans.append(['bvor',bvl,bvr])
                ans.append(['bvxor',bvl,bvr])
    bvs.append(ans)


def calc_bv(bv, xvalue) :
    if type(bv) == list :
        res = 0
        if bv[0] == 'bvand' :
            res =  calc_bv(bv[1],xvalue) & calc_bv(bv[2],xvalue)
        if bv[0] == 'bvor' :
            res =  calc_bv(bv[1],xvalue) | calc_bv(bv[2],xvalue)
        if bv[0] == 'bvxor' :
            res =  calc_bv(bv[1],xvalue) ^ calc_bv(bv[2],xvalue)
        if bv[0] == 'bvnot' :
            res = ~ calc_bv(bv[1],xvalue)
        if bv[0] == 'shl' :
            res =  calc_bv(bv[1],xvalue) << bv[2]
        if bv[0] == 'shr' :
            res =  calc_bv(bv[1],xvalue) >> bv[2]
        return res & 0xffffffffffffffff
    if bv == 'x' :
        return xvalue & 0xffffffffffffffff
    return bv  & 0xffffffffffffffff

def solver(samples, Constraints, minlen) :
    for i in samples :
        for bv in poss_bv[i[1][1][1][1]] :
            flag = False
            for x in samples :
                if calc_bv(bv,x[1][1][1][1])  & 0xffffffffffffffff != x[1][2][1] :
                    flag = True
                    break
            if flag :
                continue
            count = 0
            for x in Constraints :
                if calc_bv(bv,x[1][1][1][1])  & 0xffffffffffffffff == x[1][2][1] :
                    count += 1
            if count >= minlen :
                return bv
    return None

def get_candidate_programs(Constraints, k, n, s) :
    ret = []
    if k > len(Constraints) :
        k = len(Constraints)
    for i in range(0, n*(k**n)) :
        temp = sample(Constraints, k = k)
        p = solver(temp, Constraints, len(Constraints)//k)
        if p == None :
            continue
        ret.append(p)
    return ret

def term_search(Constrains, k, n, s) :
    if len(Constrains) == 0 :
        return []
    if k == 0 :
        return None
    temp = get_candidate_programs(Constrains, k, n, s)
    for p in temp :
        newConstraints = []
        for c in Constrains :
            if calc_bv(p,c[1][1][1][1])  & 0xffffffffffffffff != c[1][2][1] :
                newConstraints.append(c)
        res = term_search(newConstraints, k - 1, n, s)
        if res != None :
            res.append(p)
            return res
    return None

def term_solver(Constraints) :
    s = 1
    n = 3
    k = 5
    while True :
        for nn in range(1, n + 1) :
            for kk in range(1, k + 1) :
                temp = term_search(Constraints, kk, nn, s)
                if temp != None :
                    return temp
        s += 1
        n += 2
        k += 3

def get_conditions(s) :
    res = []
    res.append(0)
    for i in range(0, 64) :
        res.append(['shl','x',i])
        res.append(['shr','x',i])
        res.append(['shl',1,i])
    n = len(res)
    for i in range(0, n) :
        res.append(['bvnot',res[i]])
    # print(res)
    return res

def simply(clause, nexamples) :
    ret = []
    temp = []
    for x in nexamples :
        temp.append(x)
    for c in clause :
        t = []
        # print(c,len(temp))
        for x in temp :
            if calc_bv(c, x[1][1][1][1]) & 1 :
                t.append(x)
        if len(t) == len(temp) :
            continue
        ret.append(c)
        temp = t
    return ret

def get_candidate_clause(conditions, pexamples, nexamples, k, s) :
    ret = [([],pexamples)]
    for c in conditions :
        n = len(ret)
        for j in range(0, n) :
            temp = []
            for i in ret[j][1] :
                if calc_bv(c, i[1][1][1][1]) & 1 :
                    temp.append(i)
            # print(len(temp), len(pexamples))
            if len(temp) < len(pexamples) // k :
                continue
            if len(temp) == len(ret[j][1]) :
                ret[j][0].append(c)
            else :
                t = ([],temp)
                for x in ret[j][0] :
                    t[0].append(x)
                t[0].append(c)
                ret.append(t)
    # for i in ret :
    #     print(i[0])
    ans = []
    for i in ret :
        bj = True
        for x in nexamples :
            flag = True
            for j in i[0] :
                if (calc_bv(j,x[1][1][1][1]) & 1) == 0 :
                    flag = False
                    break
            if flag :
                bj = False
                break
        if bj :
            ans.append(simply(i[0],nexamples))
    return ans

def DNF_search(conditions, pexamples, nexamples, k, s) :
    if len(pexamples) == 0 :
        return []
    if k == 0 :
        return None
    temp = get_candidate_clause(conditions, pexamples, nexamples, k, s)
    # print(k,s)
    # print(temp)
    for c in temp :
        npexamples = []
        for x in pexamples :
            for i in c :
                if (calc_bv(i,x[1][1][1][1]) & 1) == 0 :
                    npexamples.append(x)
                    break
        res = DNF_search(conditions, npexamples, nexamples, k - 1, s)
        if res != None :
            temp = []
            for i in c :
                if temp == [] :
                    temp = i
                else :
                    temp = ['bvand',temp,i]
            if res == [] :
                return temp
            else :
                return ['bvor', res, temp]
    return None

def DNF_solver(pexamples, nexamples) :
    s = 1
    k = 1
    visit = set()
    conditions = get_conditions(s)
    while True :
        for kk in range(1, k+1) :
            for ss in range(1, s+1) :
                if (kk,ss) in visit :
                    continue
                # print(kk,ss)
                visit.add((kk,ss))
                temp = DNF_search(conditions, pexamples, nexamples, kk, ss)
                if temp != None :
                    return temp
        k += 1
        s += 1
    return None

def trans(x) :
    if type(x) == str :
        return x
    elif type(x) == list :
        if x[0] == 'shl' :
            if x[2] == 0 :
                return trans(x[1])
            else :
                temp = []
                temp.append('shl')
                temp.append(x[1])
                temp.append(x[2]-1)
                ret = []
                ret.append('shl1')
                ret.append(trans(temp))
                return ret
        elif x[0] == 'shr' :
            ret = []
            temp = []
            temp.append('shr')
            temp.append(x[1])
            if x[2] >= 16 :
                temp.append(x[2]-16)
                ret.append('shr16')
            elif x[2] >= 4 :
                temp.append(x[2]-4)
                ret.append('shr4')
            elif x[2] >= 1 :
                temp.append(x[2]-1)
                ret.append('shr1')
            else :
                return trans(x[1])
            ret.append(trans(temp))
            return ret
        else :
            ret = []
            for i in range(0, len(x)) :
                ret.append(trans(x[i]))
            return ret
    else :
        return (['BitVec',('Int',64)],x)

def work(checker, Constraints) :
    bvs.append([])
    bvs.append([])
    bvs[1].append(0)
    bvs[1].append(1)
    bvs[1].append('x')
    for i in range(2,8) :
        enumerate_bv(i)
        # print(len(bvs[i]))
    for constraint in Constraints :
        temp = []
        for i in range(1,8) :
            for bv in bvs[i] :
                if calc_bv(bv,constraint[1][1][1][1]) & 0xffffffffffffffff == constraint[1][2][1] :
                    # print('passed',bv)
                    temp.append(bv)
                    if len(temp) == 1 :
                        break
            if len(temp) == 1 :
                break
        if len(temp) == 0 :
            return 'failed'
        # print('pass',constraint[1][1][1][1])
        poss_bv[constraint[1][1][1][1]] = temp
    terms = term_solver(Constraints)
    terms.reverse()
    n = len(terms)
    conditions = []
    for i in range(0, n - 1) :
        pexample = []
        nexample = []
        tempbv = terms[i]
        for c in Constraints :
            if calc_bv(tempbv,c[1][1][1][1]) & 0xffffffffffffffff != c[1][2][1] :
                nexample.append(c)
            else :
                flag = True
                for j in range(i+1, n-1) :
                    if calc_bv(terms[j],c[1][1][1][1]) & 0xffffffffffffffff == c[1][2][1] :
                        flag = False
                if flag :
                    pexample.append(c)
        cond = DNF_solver(pexample, nexample)
        conditions.append(['bvand',cond,1])
    n = n - 1
    res = terms[n]
    while n != 0 :
        n = n - 1
        res = ['if0', conditions[n], terms[n], res]
    # print(Constraints)
    print(res)
    return trans(res)