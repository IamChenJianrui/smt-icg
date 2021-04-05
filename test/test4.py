from z3 import *

v0, v1 = Int('v0'), Int('v1')
s = Solver()

e1 = (1*v0 + 1*v1)%2 == 1
e2 = (1*v0 + 0*v1)%2 == 0
def imply(expr1, expr2):
    s = Solver()
    s.add(ForAll([v0, v1], Implies(expr1, expr2)))
    return s.check() == sat

print(imply(e1, e2))
print(imply(e2, e1))