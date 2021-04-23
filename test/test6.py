from z3 import *

def refine_modu(coe, e, b, res, tmp, last=0):
    if len(coe) == 1:
        if coe[0] == 0:
            if last % e == b:
                tmp.append(0)
            else:
                return
        for i in range(e):
            if (i + last) % e == b:
                tmp.append(i)
                break
        res.append(list(tmp))
        tmp.pop()
    elif coe[0] == 0:
        tmp.append(0)
        refine_modu(coe[1:], e, b, res, tmp, last)
        tmp.pop()
    else:
        for i in range(e):
            tmp.append(i)
            refine_modu(coe[1:], e, b, res, tmp, last + i)
            tmp.pop()


def build_formula(coe, e, M, V):
   expr = And(*[(coe[i] * v) % e == M[i] for i, v in enumerate(V)])
   return simplify(expr)


res = []
A = [1, 0, 3]
V = [Int('v1'), Int('v2'), Int('v3')]
e = 4
refine_modu(A, e, 3, res, [])
for M in res:
    print(M, build_formula(A, e, M, V))


