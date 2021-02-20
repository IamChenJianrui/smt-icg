from z3 import *

v0, v1 = Int('v0'), Int('v1')
e = (3 * v0 + 15 * v1) % 4 == 0

print(simplify(e))