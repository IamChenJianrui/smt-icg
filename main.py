from domain.parser import PDDLParser
from generator import Generator
from z3 import simplify
import time
import os


if __name__ == '__main__':
    start = time.time()
    # domain = PDDLParser("./pddl/Empty_and_divide.pddl")
    domain = PDDLParser("./pddl/two_piled_nim.pddl")
    # domain = PDDLParser("./pddl/Chomp_game.pddl")
    gen = Generator(domain)
    formula_template = gen.generate_formula()
    formula = simplify(formula_template.formula_model())
    print('*'*50)
    print('N-formula:\n\t %s' % formula)

    gen.generate_strategy()

    # sgen = StrategyGenerator(domain, formula_template, refiner_model)
    # sgen.generate()

    # if not os.path.exists("./log"):
    #     os.mkdir("./log")
    # with open("./log/%s" % domain.name, "a") as f:
    #     print("\n*******************Finished*******************")
    #     cost = time.time() - start
    #     print(refiner_model)
    #     print('N-formula:\n\t %s' % formula)
    #     print('Total time cost:\n\t %s' % cost)
    #     print('N-formula: %s' % formula, file=f)
    #     print('Total time cost: %s' % cost, file=f)
