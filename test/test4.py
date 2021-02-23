from z3 import *

v0, v1 = Int('v0'), Int('v1')
s = Solver()

e1 = Or(v0 % 2 == 0, v1 % 2 == 0)
e2 = Or(And((v0 + 2 * v1) % 4 == 3, v0 % 4 == 3), And((v0 + 2 * v1) % 4 != 3, v0 % 4 != 3))
def imply(expr1, expr2):
    s = Solver()
    s.add(ForAll([v0, v1], Implies(expr1, expr2)))
    return s.check() == sat

print(imply(e1, e2))
print(imply(e2, e1))