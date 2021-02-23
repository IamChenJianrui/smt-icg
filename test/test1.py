from z3 import *

v1, v2 = Int('v1'), Int('v2')

e1 = And(v1 + v2 <= 3, (-v1 + 2 * v2) % 5 != 0, (3 * v1 + 2 * v2) % 6 != 0)
e2 = Or(And(v1 + v2 <= 4,
       v1 + v2 <= 3,
       Not((-1*v1 + 2*v2)%5 == 0),
       Not((3*v1 + 2*v2)%6 == 0)),
   And(v1 + v2 == 4,
       Not(3 <= v1 + v2),
       Not((-1*v1 + 2*v2)%5 == 0),
       Not((3*v1 + 2*v2)%6 == 0)))

s = Solver()

s.add(ForAll([v1, v2], And(Implies(e1, e2), Implies(e2, e1))))
if s.check() == sat:
    print(s.model())
else:
    print(unsat)

'''
判断蕴含
ForAll([v], Implies(e1, e2))

判断等价
ForAll([v], And(Implies(e1, e2), Implies(e2, e1)))

判断矛盾
ForAll([v], Not(And(e1, e2)))  
'''
