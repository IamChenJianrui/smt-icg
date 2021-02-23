from z3 import *

v1, v2 = Int('v1'), Int('v2')
s = Solver()

s.add(2*v1%4 == 1)
print(s.check())
# s.add(v1 + v2 < 3, 2 * v1 % 4 != 1)
# if s.check() == sat:
#     print(s.model())
# else:
#     print(unsat)