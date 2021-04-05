from z3 import *

v0, v1 = Int('v0'), Int('v1')

e1 = v0
e2 = v0 + v1
e3 = e1 - e2
print(e3)


