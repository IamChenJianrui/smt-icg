from domain.parser import PDDLParser
from generator import NormalGenerator

domain = PDDLParser("../pddl/Subtraction_game.pddl")
gen = NormalGenerator(domain)
print('p set:', gen.p_demo)
print('n set:', gen.n_demo)
print(gen.check_np((6,)))
print('p set:', gen.p_demo)
print('n set:', gen.n_demo)