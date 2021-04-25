from z3 import *

v1, v2 = Int('v1'), Int('v2')
s = Solver()

e1 = (v1 % 5) != 1
e2 = Not((3*v1)%5 == 3)
# s.add(ForAll([v1, v2], Not(And(e1, e2)))) #sat
# s.add(ForAll([v1, v2], Implies(e2, e1))) #unsat
s.add(ForAll([v1, v2], And(Implies(e1, e2), Implies(e2, e1)))) #unsat
if s.check() == unsat:
    print(unsat)
else:
    print(s.model())
