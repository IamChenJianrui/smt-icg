from domain.parser import PDDLParser
from generator import FormulaGenerator, StrategyGenerator
from domain.utils.refiner import Refiner
from z3 import simplify
import time
import os


if __name__ == '__main__':
    start = time.time()
    # domain = PDDLParser("./pddl/Empty_and_divide.pddl")
    domain = PDDLParser("./pddl/two_piled_nim.pddl")
    gen = FormulaGenerator(domain)
    formula_template = gen.generate()
    formula = simplify(formula_template.formula_model())
    print('*'*50)
    print('N-formula:\n\t %s' % formula)

    model = formula_template.refine_model()
    refiner_model = Refiner(list(domain.pddl2icg.values())).refine(model, domain.feasible_region)
    print('*' * 50)
    print('refined model:', refiner_model)

    sgen = StrategyGenerator(domain, formula_template, refiner_model)
    sgen.generate()

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
