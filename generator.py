from template import FormulaTemplate, EquTemplate
from domain.utils.refiner import Refiner
from z3 import *
from random import randint

tmp_size = [(1, 1, 0), (1, 0, 1), (1, 0, 2), (1, 1, 1), (2, 0, 1),
            (2, 0, 2), (2, 1, 1), (2, 2, 1), (2, 1, 2), (2, 1, 4), (4, 1, 4)]


class NormalGenerator:
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

        # 令P-state不能为ending state
        for state in self.ending_state:
            for i, j in zip(list(domain.pddl2icg.values()), state):
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
            param, param_set, ok = action.get_all_params(var_dict)
            if ok:
                if param_set is not None and len(param_set) > 0:
                    for k in param_set:
                        param_dict = {param: k}
                        eff_dict = action.get_eff(var_dict, param_dict)
                        if eff_dict is not None:
                            yield self.get_state_tuple(eff_dict)
                else:
                    param_dict = {param: 0}
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

    def generate_formula(self, idx=0):
        print("\n\nsize:", tmp_size[idx])
        self.formula_template = FormulaTemplate(list(self.domain.pddl2icg.values()), *tmp_size[idx])

        eff_var = list(self.domain.eff_mapper.values())

        def con1(nf, a_nf):  # N-state的约束
            return Implies(nf, Exists(eff_var, And(self.transition_formula, Not(a_nf))))

        def con2(nf, a_nf):  # P-state的约束
            return Implies(And(self.not_equ_ending, Not(nf)), ForAll(eff_var, Implies(self.transition_formula, a_nf)))

        for state in self.p_set:
            self.formula_template.add(state, False)
        for state in self.n_set:
            self.formula_template.add(state, True)
        if self.formula_template.check() == unsat:
            print("###unsat, extending...")
            return self.generate_formula(idx + 1)

        while True:
            print("\nSP:", self.p_set)
            print("SN:", self.n_set)
            nf = self.formula_template.formula_model()
            a_nf = self.formula_template.formula_model(*eff_var)
            print("N-formula: \n", nf)

            s1 = Solver()
            s1.set("timeout", 600000)
            s1.add(self.constraint, Not(con1(nf, a_nf)))

            if s1.check() == sat:
                model = s1.model()
                example = [model[self.formula_template.vi[i]].as_long()
                           if model[self.formula_template.vi[i]] is not None
                           else 0 for i in range(self.formula_template.n)]
                example = tuple(example)
                n = len(example)
                while True:  # 直到找到合适的反例
                    try:
                        print("Find a counter example", example)
                        if not self.check_np(example):  # 这是一个P状态
                            print("This example belongs to P-state.")
                            self.formula_template.add(example, False)
                            self.p_set.add(example)
                        else:
                            print("This example belong to N-state.")
                            for eff in self.gen_eff(example):
                                if not self.check_np(eff):
                                    if bool(self.formula_template.formula_model(*eff)):
                                        print("find an eff", eff, ", which belongs to P-state.")
                                        self.formula_template.add(eff, False)
                                        self.p_set.add(eff)
                                        break
                                elif not bool(self.formula_template.formula_model(*eff)):
                                    print("find an eff", eff, ", which belongs to N-state.")
                                    self.formula_template.add(eff, False)
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
                s2.set("timeout", 600000)
                s2.add(self.constraint, Not(con2(nf, a_nf)))
                if s2.check() == sat:
                    model = s2.model()
                    example = [model[self.formula_template.vi[i]].as_long()
                               if model[self.formula_template.vi[i]] is not None
                               else 0 for i in range(self.formula_template.n)]
                    example = tuple(example)
                    n = len(example)
                    while True:
                        try:
                            print("Find a counter example", example)
                            if self.check_np(example):
                                print("This example belongs to N-state.")
                                self.formula_template.add(example, True)
                                self.n_set.add(example)
                            else:
                                print("This example belong to P-state.")
                                for eff in self.gen_eff(example):
                                    if self.check_np(eff):
                                        if not bool(self.formula_template.formula_model(*eff)):
                                            print("find an eff", eff, ", which belongs to P-state.")
                                            self.formula_template.add(eff, True)
                                            self.n_set.add(eff)
                                            break
                                    elif bool(self.formula_template.formula_model(*eff)):
                                        print("find an eff", eff, ", which belongs to N-state.")
                                        self.formula_template.add(eff, True)
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
            check = self.formula_template.check()
            if check == unknown:
                raise RuntimeError("z3 solver running out of time")
            elif check == unsat:
                print('###unsat, extending...')
                return self.generate_formula(idx + 1)
            if len(self.p_set) > 4 * len(self.n_set):
                print('###extending...')
                for s in self.n_demo:
                    if s not in self.n_set:
                        self.n_set.add(s)
                        if len(self.p_set) < 2 * len(self.n_set):
                            break
                return self.generate_formula(idx + 1)
            if len(self.n_set) > 4 * len(self.p_set):
                print('###extending...')
                for s in self.p_demo:
                    if s not in self.p_set:
                        self.p_set.add(s)
                        if len(self.n_set) < 2 * len(self.p_set):
                            break
                return self.generate_formula(idx + 1)
        return self.formula_template

    def gen_example_of_cover(self, cover, demo):
        s = Solver()
        s.add(cover)
        s.add(self.domain.constraints)
        vi = list(self.domain.pddl2icg.values())
        for state in demo:
            s.add(*[vi[i] != state[i] for i in range(len(vi))])
        if s.check() == sat:
            model = s.model()
            example = [model[vi[i]].as_long()
                       if model[vi[i]] is not None else 0 for i in range(len(vi))]
            example = tuple(example)
            demo[example] = []
            return example
        else:
            raise RuntimeError("fail to generate state of cover:", cover)

    def gen_eff2(self, state, action):
        var_dict = dict(zip(self.domain.pddl2icg.keys(), state))
        param, param_set, ok = action.get_all_params(var_dict)
        if ok:
            if len(param_set) > 0:
                for k in param_set:
                    param_dict = {param: k}
                    eff_dict = action.get_eff(var_dict, param_dict)
                    if eff_dict is not None:
                        res = self.get_state_tuple(eff_dict)
                        if not self.check_np(res):
                            yield k, action.name, res
            else:
                param_dict = {param: 0}
                eff_dict = action.get_eff(var_dict, param_dict)
                if eff_dict is not None:
                    res = self.get_state_tuple(eff_dict)
                    if not self.check_np(res):
                        yield 0, action.name, res

    def combination_of_demo(self, state_list, demo, tmp, res):
        if len(state_list) == 0:
            res.append(list(tmp))
            return
        state = []
        state.extend(state_list[0])
        for b in demo[state_list[0]]:
            state.append(b)
            tmp.append(list(state))
            self.combination_of_demo(state_list[1:], demo, tmp, res)
            tmp.pop()
            state.pop()

    def generate_param(self, exam_set):
        rqu_template = EquTemplate(len(self.domain.pddl2icg))
        for vec in exam_set:
            rqu_template.add(vec)
        if rqu_template.check() == sat:
            return rqu_template.solve_model()
        return None

    def generate_strategy(self):
        model = self.formula_template.refine_model()
        refiner = Refiner(list(self.domain.pddl2icg.values()))
        refiner_model = refiner.refine(model, self.domain.feasible_region)
        print('*' * 50)
        print('refined model:', refiner_model)

        strategies = []
        find = [False for _ in refiner_model]
        for cover_idx, cover_list in enumerate(refiner_model):
            cover = simplify(And(*cover_list))
            print('-' * 50, "\ncover:", cover)
            for action in self.domain.actions:
                flag, demo = False, dict()
                for i in range(5):  # 生成5个用例
                    self.gen_example_of_cover(cover, demo)
                state_list = list(demo.keys())
                for state in state_list:
                    params = [param[0] for param in self.gen_eff2(state, action)]
                    if len(params) > 0:
                        demo[state] = [k for k in params]
                    else:
                        flag = True
                        break
                if flag:  # 找不到后继状态中的P状态
                    continue

                eff_var = list(self.domain.eff_mapper.values())

                while True:
                    print(action.name, demo)
                    state_list = list(demo.keys())
                    comb_list = []  # 当前action下可能的所有情况
                    self.combination_of_demo(state_list, demo, [], comb_list)
                    while len(comb_list) > 0:
                        # for example_set in comb_list:
                        example_set = comb_list[0]
                        print('example:', comb_list)
                        comb_list = comb_list[1:]
                        param_expr = self.generate_param(example_set)
                        if param_expr is None:
                            continue

                        print("param of action:", param_expr)
                        tf = action.trans_formula()
                        wf = self.formula_template.formula_model(*eff_var)
                        const = simplify(Implies(cover, ForAll(eff_var, Implies(tf, Not(wf)))))
                        free_p = list(action.params_mapper.values())[0]  # 动作的参数
                        s = Solver()
                        s.add(self.domain.constraints, free_p == param_expr, Not(const))
                        if s.check() == sat:
                            model = s.model()
                            example = [model[self.formula_template.vi[i]].as_long()
                                       if model[self.formula_template.vi[i]] is not None
                                       else 0 for i in range(self.formula_template.n)]
                            example = tuple(example)
                            print(model)
                            print("find a counterexample:", example)
                            params = [param[0] for param in self.gen_eff2(example, action)]
                            if len(params) > 0:
                                demo[example] = [k for k in params]
                                need_to_append_list = [[*example, k] for k in params]
                                k = len(comb_list)
                                for ntal in need_to_append_list:
                                    comb_list.append([*example_set, ntal])
                                while k > 0:
                                    example_set = comb_list[0]
                                    comb_list = comb_list[1:]
                                    k -= 1
                                    for ntal in need_to_append_list:
                                        comb_list.append([*example_set, ntal])
                            else:
                                break
                        else:
                            strategies.append((cover, action.name, param_expr))
                            find[cover_idx] = True
                            flag = True
                            break  # break for loop
                    if flag:
                        break  # break while loop
                if flag:
                    break  # break action loop
                # 遍历完了action也没有找到策略

        failed_cover_list = [simplify(And(*cover_list))
                             for i, cover_list in enumerate(refiner_model)
                             if not find[i]]
        if (len(failed_cover_list)) > 0:
            print('failed cover', failed_cover_list)
        return strategies


class MisereGenerator:
    def __init__(self, domain):
        self.domain = domain
        self.transition_formula = domain.transition_formula()
        self.ending_state = [self.get_state_tuple(state) for state in domain.ending_states]
        self.constraint = self.domain.constraints
        self.p_demo = set()
        self.n_demo = {*self.ending_state}
        self.p_set = set()
        self.n_set = {*self.ending_state}
        self.not_equ_ending = False

        # 令P-state不能为ending state
        for state in self.ending_state:
            for i, j in zip(list(domain.pddl2icg.values()), state):
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
            param, param_set, ok = action.get_all_params(var_dict)
            if ok:
                if param_set is not None and len(param_set) > 0:
                    for k in param_set:
                        param_dict = {param: k}
                        eff_dict = action.get_eff(var_dict, param_dict)
                        if eff_dict is not None:
                            yield self.get_state_tuple(eff_dict)
                else:
                    param_dict = {param: 0}
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

    def generate_formula(self, idx=0):
        print("\n\nsize:", tmp_size[idx])
        self.formula_template = FormulaTemplate(list(self.domain.pddl2icg.values()), *tmp_size[idx])

        eff_var = list(self.domain.eff_mapper.values())

        def con1(nf, a_nf):  # N-state的约束
            return Implies(And(self.not_equ_ending, nf), Exists(eff_var, And(self.transition_formula, Not(a_nf))))

        def con2(nf, a_nf):  # P-state的约束
            return Implies(Not(nf), ForAll(eff_var, Implies(self.transition_formula, a_nf)))

        for state in self.p_set:
            self.formula_template.add(state, False)
        for state in self.n_set:
            self.formula_template.add(state, True)
        if self.formula_template.check() == unsat:
            print("###unsat, extending...")
            return self.generate_formula(idx + 1)

        while True:
            print("\nSP:", self.p_set)
            print("SN:", self.n_set)
            nf = self.formula_template.formula_model()
            a_nf = self.formula_template.formula_model(*eff_var)
            print("N-formula: \n", nf)

            s1 = Solver()
            s1.set("timeout", 600000)
            s1.add(self.constraint, Not(con1(nf, a_nf)))

            if s1.check() == sat:
                model = s1.model()
                example = [model[self.formula_template.vi[i]].as_long()
                           if model[self.formula_template.vi[i]] is not None
                           else 0 for i in range(self.formula_template.n)]
                example = tuple(example)
                n = len(example)
                while True:  # 直到找到合适的反例
                    try:
                        print("Find a counter example", example)
                        if not self.check_np(example):  # 这是一个P状态
                            print("This example belongs to P-state.")
                            self.formula_template.add(example, False)
                            self.p_set.add(example)
                        else:
                            print("This example belong to N-state.")
                            for eff in self.gen_eff(example):
                                if not self.check_np(eff):
                                    if bool(self.formula_template.formula_model(*eff)):
                                        print("find an eff", eff, ", which belongs to P-state.")
                                        self.formula_template.add(eff, False)
                                        self.p_set.add(eff)
                                        break
                                elif not bool(self.formula_template.formula_model(*eff)):
                                    print("find an eff", eff, ", which belongs to N-state.")
                                    self.formula_template.add(eff, False)
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
                s2.set("timeout", 600000)
                s2.add(self.constraint, Not(con2(nf, a_nf)))
                if s2.check() == sat:
                    model = s2.model()
                    example = [model[self.formula_template.vi[i]].as_long()
                               if model[self.formula_template.vi[i]] is not None
                               else 0 for i in range(self.formula_template.n)]
                    example = tuple(example)
                    n = len(example)
                    while True:
                        try:
                            print("Find a counter example", example)
                            if self.check_np(example):
                                print("This example belongs to N-state.")
                                self.formula_template.add(example, True)
                                self.n_set.add(example)
                            else:
                                print("This example belong to P-state.")
                                for eff in self.gen_eff(example):
                                    if self.check_np(eff):
                                        if not bool(self.formula_template.formula_model(*eff)):
                                            print("find an eff", eff, ", which belongs to P-state.")
                                            self.formula_template.add(eff, True)
                                            self.n_set.add(eff)
                                            break
                                    elif bool(self.formula_template.formula_model(*eff)):
                                        print("find an eff", eff, ", which belongs to N-state.")
                                        self.formula_template.add(eff, True)
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
            check = self.formula_template.check()
            if check == unknown:
                raise RuntimeError("z3 solver running out of time")
            elif check == unsat:
                print('###unsat, extending...')
                return self.generate_formula(idx + 1)
            if len(self.p_set) > 4 * len(self.n_set):
                print('###extending...')
                for s in self.n_demo:
                    if s not in self.n_set:
                        self.n_set.add(s)
                        if len(self.p_set) < 2 * len(self.n_set):
                            break
                return self.generate_formula(idx + 1)
            if len(self.n_set) > 4 * len(self.p_set):
                print('###extending...')
                for s in self.p_demo:
                    if s not in self.p_set:
                        self.p_set.add(s)
                        if len(self.n_set) < 2 * len(self.p_set):
                            break
                return self.generate_formula(idx + 1)
        return self.formula_template

    def gen_example_of_cover(self, cover, demo):
        s = Solver()
        s.add(cover)
        s.add(self.domain.constraints)
        vi = list(self.domain.pddl2icg.values())
        for state in demo:
            s.add(*[vi[i] != state[i] for i in range(len(vi))])
        if s.check() == sat:
            model = s.model()
            example = [model[vi[i]].as_long()
                       if model[vi[i]] is not None else 0 for i in range(len(vi))]
            example = tuple(example)
            demo[example] = []
            return example
        else:
            raise RuntimeError("fail to generate state of cover:", cover)

    def gen_eff2(self, state, action):
        var_dict = dict(zip(self.domain.pddl2icg.keys(), state))
        param, param_set, ok = action.get_all_params(var_dict)
        if ok:
            if len(param_set) > 0:
                for k in param_set:
                    param_dict = {param: k}
                    eff_dict = action.get_eff(var_dict, param_dict)
                    if eff_dict is not None:
                        res = self.get_state_tuple(eff_dict)
                        if not self.check_np(res):
                            yield k, action.name, res
            else:
                param_dict = {param: 0}
                eff_dict = action.get_eff(var_dict, param_dict)
                if eff_dict is not None:
                    res = self.get_state_tuple(eff_dict)
                    if not self.check_np(res):
                        yield 0, action.name, res

    def combination_of_demo(self, state_list, demo, tmp, res):
        if len(state_list) == 0:
            res.append(list(tmp))
            return
        state = []
        state.extend(state_list[0])
        for b in demo[state_list[0]]:
            state.append(b)
            tmp.append(list(state))
            self.combination_of_demo(state_list[1:], demo, tmp, res)
            tmp.pop()
            state.pop()

    def generate_param(self, exam_set):
        rqu_template = EquTemplate(len(self.domain.pddl2icg))
        for vec in exam_set:
            rqu_template.add(vec)
        if rqu_template.check() == sat:
            return rqu_template.solve_model()
        return None

    def generate_strategy(self):
        model = self.formula_template.refine_model()
        refiner = Refiner(list(self.domain.pddl2icg.values()))
        refiner_model = refiner.refine(model, self.domain.feasible_region)
        print('*' * 50)
        print('refined model:', refiner_model)

        strategies = []
        find = [False for _ in refiner_model]
        for cover_idx, cover_list in enumerate(refiner_model):
            cover = simplify(And(*cover_list))
            print('-' * 50, "\ncover:", cover)
            for action in self.domain.actions:
                flag, demo = False, dict()
                for i in range(5):  # 生成5个用例
                    self.gen_example_of_cover(cover, demo)
                state_list = list(demo.keys())
                for state in state_list:
                    params = [param[0] for param in self.gen_eff2(state, action)]
                    if len(params) > 0:
                        demo[state] = [k for k in params]
                    else:
                        flag = True
                        break
                if flag:  # 找不到后继状态中的P状态
                    continue

                eff_var = list(self.domain.eff_mapper.values())

                while True:
                    print(action.name, demo)
                    state_list = list(demo.keys())
                    comb_list = []  # 当前action下可能的所有情况
                    self.combination_of_demo(state_list, demo, [], comb_list)
                    while len(comb_list) > 0:
                        # for example_set in comb_list:
                        example_set = comb_list[0]
                        print('example:', comb_list)
                        comb_list = comb_list[1:]
                        param_expr = self.generate_param(example_set)
                        if param_expr is None:
                            continue

                        print("param of action:", param_expr)
                        tf = action.trans_formula()
                        wf = self.formula_template.formula_model(*eff_var)
                        const = simplify(Implies(cover, ForAll(eff_var, Implies(tf, Not(wf)))))
                        free_p = list(action.params_mapper.values())[0]  # 动作的参数
                        s = Solver()
                        s.add(self.domain.constraints, free_p == param_expr, Not(const))
                        if s.check() == sat:
                            model = s.model()
                            example = [model[self.formula_template.vi[i]].as_long()
                                       if model[self.formula_template.vi[i]] is not None
                                       else 0 for i in range(self.formula_template.n)]
                            example = tuple(example)
                            print(model)
                            print("find a counterexample:", example)
                            params = [param[0] for param in self.gen_eff2(example, action)]
                            if len(params) > 0:
                                demo[example] = [k for k in params]
                                need_to_append_list = [[*example, k] for k in params]
                                k = len(comb_list)
                                for ntal in need_to_append_list:
                                    comb_list.append([*example_set, ntal])
                                while k > 0:
                                    example_set = comb_list[0]
                                    comb_list = comb_list[1:]
                                    k -= 1
                                    for ntal in need_to_append_list:
                                        comb_list.append([*example_set, ntal])
                            else:
                                break
                        else:
                            strategies.append((cover, action.name, param_expr))
                            find[cover_idx] = True
                            flag = True
                            break  # break for loop
                    if flag:
                        break  # break while loop
                if flag:
                    break  # break action loop
                # 遍历完了action也没有找到策略

        failed_cover_list = [simplify(And(*cover_list))
                             for i, cover_list in enumerate(refiner_model)
                             if not find[i]]
        if (len(failed_cover_list)) > 0:
            print('failed cover', failed_cover_list)
        return strategies