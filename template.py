from z3 import *


def sum(iter):
    tmp_list = [i for i in iter]
    res = tmp_list[0]
    for i in tmp_list[1:]:
        res += i
    return res


class FormulaTemplate:
    def __init__(self, vi, k, h, m, timeout=300000):
        self.k = k  # amount of clause

        self.h = h  # number of inequality
        self.m = m  # number of mode number

        self.vi = vi
        n = len(vi)
        self.n = n

        self.aeij = [[Int('ae' + str(i) + str(j)) for j in range(n)] for i in range(h)]
        self.bi = [Int('b' + str(i)) for i in range(h)]

        self.amij = [[Int('am' + str(i) + str(j)) for j in range(n)] for i in range(m)]
        self.ei = [Int('e' + str(i)) for i in range(m)]
        self.ci = [Int('c' + str(i)) for i in range(m)]

        self.heij = [[Bool('h_e' + str(j) + str(i)) for i in range(h)] for j in range(k)]
        self.hgeij = [[Bool('h_ge' + str(j) + str(i)) for i in range(h)] for j in range(k)]
        self.hleij = [[Bool('h_le' + str(j) + str(i)) for i in range(h)] for j in range(k)]

        self.tij = [[Bool('t' + str(j) + str(i)) for i in range(m)] for j in range(k)]
        self.ntij = [[Bool('nt' + str(j) + str(i)) for i in range(m)] for j in range(k)]

        self.s = Solver()
        # 系数不能全部为0
        for ai in self.aeij:
            self.s.add(Or(*[a > 0 for a in ai]))
        for mi in self.amij:
            self.s.add(Or(*[m > 0 for m in mi]))
        # 余数必须小于模
        self.s.add(*[And(self.ei[i] > self.ci[i], self.ci[i] >= 0) for i in range(m)])
        # 模必须大于等于2，并且小于一定范围
        self.s.add(*[And(e >= 2, e <= 2 * (m + 1)) for e in self.ei])

        # 判断条件一定有一个是False，避免逻辑出现False
        for j in range(k):
            self.s.add(*[Not(And(self.heij[i][j], self.hgeij[i][j], self.hleij[i][j])) for i in range(h)])
            self.s.add(*[Not(And(self.tij[i][j], self.ntij[i][j])) for i in range(m)])

        self.s.set("timeout", timeout)

    def add(self, example, label):
        self.s.add(self.encoding(example, label))

    def check(self):
        return self.s.check()

    def inequ(self, val):
        Equ = [sum(val[j] * self.aeij[i][j] for j in range(self.n)) != self.bi[i] for i in range(self.h)]
        Ge = [sum(val[j] * self.aeij[i][j] for j in range(self.n)) >= self.bi[i] for i in range(self.h)]
        Le = [sum(val[j] * self.aeij[i][j] for j in range(self.n)) <= self.bi[i] for i in range(self.h)]
        return Equ, Ge, Le

    def mode(self, val):
        return [sum(val[j] * self.amij[i][j] for j in range(self.n)) % self.ei[i] == self.ci[i] for i in range(self.m)]

    def encoding(self, example, label):
        Eq, Ge, Le = self.inequ(example)
        posMo = self.mode(example)
        Tk = []

        for k in range(self.k):
            clause = []
            clause.extend([Implies(self.heij[k][h], Eq[h]) for h in range(self.h)])
            clause.extend([Implies(self.hgeij[k][h], Ge[h]) for h in range(self.h)])
            clause.extend([Implies(self.hleij[k][h], Le[h]) for h in range(self.h)])
            clause.extend([Implies(self.tij[k][m], posMo[m]) for m in range(self.m)])
            clause.extend([Implies(self.ntij[k][m], Not(posMo[m])) for m in range(self.m)])
            Tk.append(And(*clause))
        return Or(*Tk) == label

    def solution(self):
        model = self.s.model()
        self.M = [[model[self.amij[i][j]].as_long() if model[self.amij[i][j]] is not None else 0
              for j in range(self.n)]
             for i in range(self.m)]
        self.E = [model[self.ei[i]].as_long() if model[self.ei[i]] is not None else 1 for i in range(self.m)]
        self.C = [model[self.ci[i]].as_long() if model[self.ci[i]] is not None else 0 for i in range(self.m)]

        self.A = [[model[self.aeij[i][j]].as_long() if model[self.aeij[i][j]] is not None else 0
              for j in range(self.n)]
             for i in range(self.h)]
        self.B = [model[self.bi[i]].as_long() if model[self.bi[i]] is not None else 0 for i in range(self.h)]

        self.He = [
            [bool(model[self.heij[i][j]]) if model[self.heij[i][j]] is not None else False
             for j in range(self.h)]
            for i in range(self.k)
        ]

        self.Hge = [
            [bool(model[self.hgeij[i][j]]) if model[self.hgeij[i][j]] is not None else False
             for j in range(self.h)]
            for i in range(self.k)
        ]

        self.Hle = [
            [bool(model[self.hleij[i][j]]) if model[self.hleij[i][j]] is not None else False
             for j in range(self.h)]
            for i in range(self.k)
        ]

        self.T = [
            [bool(model[self.tij[i][j]]) if model[self.tij[i][j]] is not None else False
             for j in range(self.m)]
            for i in range(self.k)
        ]

        self.Nt = [
            [bool(model[self.ntij[i][j]]) if model[self.ntij[i][j]] is not None else False
             for j in range(self.m)]
            for i in range(self.k)
        ]

    def formula(self, *val):
        if len(val) == 0:
            val = self.vi
        self.solution()
        Eq = [sum(val[j] * self.A[i][j] for j in range(self.n)) != self.B[i] for i in range(self.h)]
        Ge = [sum(val[j] * self.A[i][j] for j in range(self.n)) >= self.B[i] for i in range(self.h)]
        Le = [sum(val[j] * self.A[i][j] for j in range(self.n)) <= self.B[i] for i in range(self.h)]

        Me = [sum(val[j] * self.M[i][j] for j in range(self.n)) % self.E[i] == self.C[i] for i in range(self.m)]

        formu = []
        for k in range(self.k):
            clause = []
            for h in range(self.h):
                if self.He[k][h]:
                    clause.append(Eq[h])
                if self.Hge[k][h]:
                    clause.append(Ge[h])
                if self.Hle[k][h]:
                    clause.append(Le[h])
            for m in range(self.m):
                if self.T[k][m]:
                    clause.append(Me[m])
                if self.Nt[k][m]:
                    clause.append(Not(Me[m]))

            formu.append(And(*clause))
        return Or(*formu)


if __name__ == '__main__':
    smt = FormulaTemplate([Int('v1'), Int('v2')], 2, 2, 2)
    smt.add([1, 2], True)
    smt.add([2, 3], False)
    print(smt.s)
    print(smt.check())

    formu = smt.formula()
    print(formu)
