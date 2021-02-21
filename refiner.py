from z3 import *


class Refiner:
    def __init__(self, vi, model_arr, feasible_region=True):
        self.vi = vi
        self.model_arr = model_arr
        self.feasible_region = feasible_region

    def refine_model_arr(self):
        def dfs(idx, tmp_list):
            if idx >= len(or_clause):
                this_is_a_list.append(list(tmp_list))
                return
            for expr in or_clause[idx]:
                tmp_list.append(expr)
                dfs(idx + 1, tmp_list)
                tmp_list.pop()

        res = []
        for or_clause in self.model_arr:
            this_is_a_list = []
            dfs(0, [])
            res.extend(this_is_a_list)
        return res

    def detect_contradiction(self, res):
        res_without_contra = []
        for clause in res:
            clause.append(self.feasible_region)
            s = Solver()
            s.add(*clause)
            if s.check() == sat:
                res_without_contra.append(clause)
        return res_without_contra

    def detect_implic(self, res):
        def imply(expr1, expr2):
            s = Solver()
            s.add(ForAll(self.vi, Implies(expr1, expr2)))
            return s.check() == sat

        res_without_implic = []
        for clause in res:
            imply_matrix = [[False for _ in range(len(clause))] for _ in range(len(clause))]
            for i in range(len(clause)):
                for j in range(len(clause)):
                    if i != j and not imply_matrix[j][i]:
                        imply_matrix[i][j] = imply(clause[i], clause[j])
            for i in range(len(clause)):
                for j in range(len(clause)):
                    if imply_matrix[i][j]:
                        clause[j] = None
            res_without_implic.append([expr for expr in clause if expr is not None])
        return res_without_implic

    def refine(self):
        res = self.refine_model_arr()
        res_without_contra = self.detect_contradiction(res)
        res_without_implic = self.detect_implic(res_without_contra)
        return res_without_implic

if __name__ == '__main__':
    v1, v2 = Int('v1'), Int('v2')
    model = [[[1 * v1 + 1 * v2 < 4, 1 * v1 + 1 * v2 == 4],
              [1 * v1 + 1 * v2 < 3, 1 * v1 + 1 * v2 == 3],
              [(2 * v1 + 0 * v2) % 4 == 1, (2 * v1 + 0 * v2) % 4 == 2, (2 * v1 + 0 * v2) % 4 == 3]],
             [[1 * v1 + 1 * v2 == 4],
              [1 * v1 + 1 * v2 < 3],
              [(2 * v1 + 0 * v2) % 4 == 1, (2 * v1 + 0 * v2) % 4 == 2, (2 * v1 + 0 * v2) % 4 == 3]]]
    refiner = Refiner([v1, v2], model)

    # res = refiner.refine_model_arr()
    # for r in res:
    #     print(r)
    # print('-' * 50)
    # res_without_contra = refiner.detect_contradiction(res)
    # for r in res_without_contra:
    #     print(r)
    # print('-' * 50)
    # res_without_implic = refiner.detect_implic(res_without_contra)
    # for r in res_without_implic:
    #     print(r)
    # print('-' * 50)

    res_without_implic = refiner.refine()
    print(res_without_implic)
