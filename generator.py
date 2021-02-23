from template import FormulaTemplate
from z3 import *
from random import randint
from utils.refiner import Refiner

tmp_size = [(1, 1, 0), (1, 0, 1), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 0, 2), (2, 1, 1), (2, 2, 1), (2, 1, 2),
            (2, 1, 4)]


class FormulaGenerator:
    def __init__(self, domain):
        self.domain = domain
        self.transition_formula = domain.transition_formula()
        self.ending_state = [self.get_state_tuple(state) for state in domain.ending_states]
        self.constraint = self.domain.constraints
        self.p_demo = {*self.ending_state}
        self.n_demo = set()
        self.p_set = {*self.ending_state}
        self.n_set = set()
        self.not_equ_ending = False

        # 令P-state永远不能等于ending state
        for state in self.ending_state:
            for i, j in zip(domain.variables, state):
                self.not_equ_ending = Or(self.not_equ_ending, i != j)
        self.not_equ_ending = simplify(self.not_equ_ending)
        print("P-state constraint:", self.not_equ_ending)
        print("Transition formula of %s:" % domain.name)
        print(self.transition_formula)
        print("Ending states:", *self.ending_state)
        print("Constraint:", domain.constraints)

    def get_state_tuple(self, var_dict):
        return tuple(var_dict.values())

    def gen_eff(self, state):
        var_dict = dict(zip(self.domain.pddl2icg.keys(), state))
        for action in self.domain.actions:
            for k, range_list in action.get_all_params(var_dict).items():
                for param_range in range_list:
                    if param_range[0] <= param_range[1]:
                        for param in range(param_range[0], param_range[1] + 1):
                            param_dict = {k: param}
                            eff_dict = action.get_eff(var_dict, param_dict)
                            if eff_dict is not None:
                                yield self.get_state_tuple(eff_dict)

    def check_np(self, state):
        if state in self.p_demo:
            return False  # It is a P state
        elif state in self.n_demo:
            return True  # It is a N state
        for eff_tuple in self.gen_eff(state):
            if not self.check_np(eff_tuple):  # exits an eff that is a P state
                self.n_demo.add(state)
                return True
        self.p_demo.add(state)
        return False

    def generate(self, idx=0):
        print(tmp_size[idx])
        formula_template = FormulaTemplate(self.domain.variables, *tmp_size[idx])

        eff_var = list(self.domain.eff_mapper.values())

        def con1(nf, a_nf):
            # N-state的约束
            return Implies(nf, Exists(eff_var, And(self.transition_formula, Not(a_nf))))

        def con2(nf, a_nf):
            # P-state的约束
            return Implies(Not(nf), ForAll(eff_var, Implies(self.transition_formula, a_nf)))

        for state in self.p_set:
            formula_template.add(state, False)
        for state in self.n_set:
            formula_template.add(state, True)
        if formula_template.check() == unsat:
            return self.generate(idx + 1)

        while True:
            print("\n\nSP:", self.p_set)
            print("SN:", self.n_set)
            nf = formula_template.formula_model()
            a_nf = formula_template.formula_model(*eff_var)
            print("N-formula: \n", nf)

            s1 = Solver()
            s1.set("timeout", 60000)
            s1.add(self.constraint, Not(con1(nf, a_nf)))

            if s1.check() == sat:
                model = s1.model()
                example = [model[formula_template.vi[i]].as_long()
                           if model[formula_template.vi[i]] is not None
                           else 0 for i in range(formula_template.n)]
                example = tuple(example)
                n = len(example)
                while True:
                    try:
                        print("Find a counter example", example)
                        if not self.check_np(example):  # 这是一个P状态
                            print("This example belongs to P-state.")
                            formula_template.add(example, False)
                            self.p_set.add(example)
                        else:
                            print("This example belong to N-state. Need to find its eff which belongs to P-state.")
                            for eff in self.gen_eff(example):
                                if not self.check_np(eff):
                                    if bool(simplify(formula_template.formula_model(*eff))):
                                        print("find an eff", eff, ", which belongs to P-state.")
                                        formula_template.add(eff, False)
                                        self.p_set.add(eff)
                                        break
                        break
                    except RecursionError:
                        print('this example is to large')
                        example = tuple(randint(10, 100) for _ in range(n))
                        while example in self.p_set or example in self.n_set:
                            example = tuple(randint(10, 100) for _ in range(n))
            else:
                print("Condition1 sat.")
                s2 = Solver()
                s2.set("timeout", 60000)
                s2.add(self.constraint, self.not_equ_ending, Not(con2(nf, a_nf)))
                if s2.check() == sat:
                    model = s2.model()
                    example = [model[formula_template.vi[i]].as_long()
                               if model[formula_template.vi[i]] is not None
                               else 0 for i in range(formula_template.n)]
                    example = tuple(example)
                    n = len(example)
                    while True:
                        try:
                            print("Find a counter example", example)
                            if self.check_np(example):
                                print("This example belongs to N-state.")
                                formula_template.add(example, True)
                                self.n_set.add(example)
                            else:
                                print("This example belong to P-state. Need to find its eff which belongs to N-state.")
                                for eff in self.gen_eff(example):
                                    if self.check_np(eff):
                                        if not bool(simplify(formula_template.formula_model(*eff))):
                                            print("find an eff", eff, ", which belongs to P-state.")
                                            formula_template.add(eff, True)
                                            self.n_set.add(eff)
                                            break
                            break
                        except RecursionError:
                            print('this example is to large')
                            example = tuple(randint(10, 100) for _ in range(n))
                            while example in self.p_set or example in self.n_set:
                                example = tuple(randint(10, 100) for _ in range(n))
                else:
                    print("condition2 sat.")
                    break
            print('generating formula...')
            check = formula_template.check()
            if check == unknown:
                raise RuntimeError("z3 solver running out of time")
            elif check == unsat:
                print('extending...')
                return self.generate(idx + 1)

        return simplify(formula_template.formula_model()), formula_template.refine_model()


class StrategyGenerator:
    def __init__(self):
        pass
