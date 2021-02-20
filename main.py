from utils.parser import PDDLParser
from generator import FormulaGenerator
import time
import os


if __name__ == '__main__':
    start = time.time()
    domain = PDDLParser("./pddl/Take_Away.pddl")
    gen = FormulaGenerator(domain)
    formula = gen.generate()
    cost = time.time() - start

    if not os.path.exists("./log"):
        os.mkdir("./log")
    with open("./log/%s" % domain.name, "a") as f:
        print("\n*******************Finished*******************")
        print('N-formula:\n\t %s' % formula)
        print('Total time cost:\n\t %s' % cost)
        print('N-formula: %s' % formula, file=f)
        print('Total time cost: %s' % cost, file=f)
