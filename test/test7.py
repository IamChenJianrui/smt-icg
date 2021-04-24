comb_list = [[[0, 1, 1], [1, 2, 1]], [[2, 3, 1], [3, 4, 1], [4, 5, 1]]]
example_set = comb_list[0]
print('example:', comb_list)
comb_list = comb_list[1:]

params = [2, 3, 4]
example = (5, 5)
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

for cl in comb_list:
    print(cl)
