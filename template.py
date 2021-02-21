from z3 import *


def sum(iter):
    tmp_list = [i for i in iter]
    res = tmp_list[0]
    for i in tmp_list[1:]:
        res += i
    return res


def co_prime(num1, num2):
    for num in range(2, min(num1, num2) + 1):
        if num1 % num == 0 and num2 % num == 0:
            return False
    return True


def gcd(*nums):
    min_num = 1 << 32
    for num in nums:
        min_num = min(min_num, abs(num))
    res = 1
    for i in range(min_num, 1, -1):
        flag = True
        for num in nums:
            if num % i != 0:
                flag = False
                break
        if flag:
            return i
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
        for i in range(m):
            # 模等式的系数m不能全部小于等于0
            self.s.add(Or(*[m > 0 for m in self.amij[i]]))
            # 模等式的系数m绝对值不能大于模e
            self.s.add(*[And(-self.ei[i] < m, m < self.ei[i]) for m in self.amij[i]])

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
        check = self.s.check()
        if check == sat:
            self.solve_model()
        return check

    def encoding(self, example, label):
        Equ = [sum(example[j] * self.aeij[i][j] for j in range(self.n)) != self.bi[i] for i in range(self.h)]
        Ge = [sum(example[j] * self.aeij[i][j] for j in range(self.n)) >= self.bi[i] for i in range(self.h)]
        Le = [sum(example[j] * self.aeij[i][j] for j in range(self.n)) <= self.bi[i] for i in range(self.h)]
        Me = [sum(example[j] * self.amij[i][j] for j in range(self.n)) % self.ei[i] == self.ci[i] for i in
              range(self.m)]

        Tk = []

        for k in range(self.k):
            clause = []
            clause.extend([Implies(self.heij[k][h], Equ[h]) for h in range(self.h)])
            clause.extend([Implies(self.hgeij[k][h], Ge[h]) for h in range(self.h)])
            clause.extend([Implies(self.hleij[k][h], Le[h]) for h in range(self.h)])
            clause.extend([Implies(self.tij[k][m], Me[m]) for m in range(self.m)])
            clause.extend([Implies(self.ntij[k][m], Not(Me[m])) for m in range(self.m)])
            Tk.append(And(*clause))
        return Or(*Tk) == label

    def solve_model(self):
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

        for i in range(self.m):
            flag = True
            for am in self.M[i][1:]:
                if am != self.M[i][0]:
                    flag = False
                    break
            if flag:
                if co_prime(self.M[i][0], self.E[i]):
                    self.M[i] = [1 for _ in range(self.n)]

        for i in range(self.h):
            divisior = gcd(*self.A[i], self.B[i])
            self.B[i] /= divisior
            for j in range(self.n):
                self.A[i][j] /= divisior

    def formula(self, *val):
        if len(val) == 0:
            val = self.vi

        formu = []
        for k in range(self.k):
            clause = []
            for h in range(self.h):
                Coe = sum(val[j] * self.A[h][j] for j in range(self.n))
                status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
                if status == (False, False, True):
                    clause.append(Coe <= self.B[h])
                elif status == (False, True, False):
                    clause.append(Coe >= self.B[h])
                elif status == (True, False, False):
                    clause.append(Coe != self.B[h])
                elif status == (False, True, True):
                    clause.append(Coe == self.B[h])
                elif status == (True, False, True):
                    clause.append(Coe < self.B[h])
                elif status == (True, True, False):
                    clause.append(Coe > self.B[h])

            for m in range(self.m):
                Me = sum(val[j] * self.M[m][j] for j in range(self.n)) % self.E[m] == self.C[m]
                if self.T[k][m]:
                    clause.append(Me)
                elif self.Nt[k][m]:
                    clause.append(Not(Me))

            formu.append(And(*clause))
        return Or(*formu)

    def refine_model(self):
        formu = []
        for k in range(self.k):
            clause = []
            for h in range(self.h):
                Coe = sum(self.vi[j] * self.A[h][j] for j in range(self.n))
                status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
                if status == (False, False, True):
                    clause.append(Coe <= self.B[h])
                elif status == (False, True, False):
                    clause.append(Coe >= self.B[h])
                elif status == (True, False, False):
                    clause.append(Coe != self.B[h])
                elif status == (False, True, True):
                    clause.append(Coe == self.B[h])
                elif status == (True, False, True):
                    clause.append(Coe < self.B[h])
                elif status == (True, True, False):
                    clause.append(Coe > self.B[h])

            for m in range(self.m):
                Me = sum(self.vi[j] * self.M[m][j] for j in range(self.n)) % self.E[m] == self.C[m]
                if self.T[k][m]:
                    clause.append(Me)
                elif self.Nt[k][m]:
                    clause.append(Not(Me))

            formu.append(And(*clause))


if __name__ == '__main__':
    smt = FormulaTemplate([Int('v1'), Int('v2')], 2, 2, 2)
    smt.add([1, 2], True)
    smt.add([2, 3], False)
    print(smt.s)
    print(smt.check())

    formu = smt.formula()
    print(formu)
    print('-' * 50)
    print(simplify(formu))
