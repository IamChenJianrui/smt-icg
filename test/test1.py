from z3 import *

v0, v1 = Int('v0'), Int('v1')
e1 = (-1*v0 + -1*v1)%4 == 0
e2 = (v0 + v1)%4 == 0

s = Solver()

s.add(ForAll([v0, v1], And(Implies(e2, e1), Implies(e1, e2))))
if s.check() == sat:
    print(s.model())
else:
    print(unsat)
