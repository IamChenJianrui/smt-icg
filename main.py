from utils.parser import PDDLParser
from generator import FormulaGenerator
from utils.refiner import Refiner
import time
import os


if __name__ == '__main__':
    start = time.time()
    domain = PDDLParser("./pddl/Empty_and_divide.pddl")
    # domain = PDDLParser("./pddl/two_piled_nim.pddl")
    gen = FormulaGenerator(domain)
    formula, model = gen.generate(5)
    refiner_model = Refiner(domain.variables).refine(model, domain.feasible_region)
    cost = time.time() - start

    if not os.path.exists("./log"):
        os.mkdir("./log")
    with open("./log/%s" % domain.name, "a") as f:
        print("\n*******************Finished*******************")
        print(refiner_model)
        print('N-formula:\n\t %s' % formula)
        print('Total time cost:\n\t %s' % cost)
        print('N-formula: %s' % formula, file=f)
        print('Total time cost: %s' % cost, file=f)
