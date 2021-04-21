from z3 import *

v0, v1 = Int('v0'), Int('v1')

e1 = (v0 + v1) % 3 == 1
e2 = (v0 + v1) % 3 == 2
s = Solver()
s.add(e1, e2)
if s.check() == sat:
    print(s.model())
else:
    print(unsat)


