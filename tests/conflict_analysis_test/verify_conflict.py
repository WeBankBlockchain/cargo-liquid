import json

ground_true_dict = {
    "visit_val_container": [{'kind': 0, 'path': [], 'read_only': False, 'slot': 0}],
    "change_complex_data_structure": [{'kind': 1, 'path': [], 'read_only': False, 'slot': 7}],
    "test_env_caller": [{'kind': 2, 'path': [0], 'read_only': True, 'slot': 1}],
    "test_env_tx_origin": [{'kind': 2, 'path': [1], 'read_only': True, 'slot': 1}],
    "test_env_now": [{'kind': 2, 'path': [2], 'read_only': True, 'slot': 2}],
    "test_env_block_number": [{'kind': 2, 'path': [3], 'read_only': True, 'slot': 3}],
    "test_env_address": [{'kind': 2, 'path': [4], 'read_only': True, 'slot': 1}],
    "test_method_parameter":  [{'kind': 3, 'path': [0, 0], 'read_only': True, 'slot': 3}],
    "test_constant_positive": [{'kind': 4, 'path': [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'read_only': True, 'slot': 4}],
    "test_constant_zero": [{'kind': 4, 'path': [0], 'read_only': True, 'slot': 5}],
    "test_constant_negative": [{'kind': 4, 'path': [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255], 'read_only': True, 'slot': 6}],
    "test_interprocedural_calling": [{'kind': 3, 'path': [0, 0], 'read_only': True, 'slot': 3}],
    "test_branch_statement": [{'kind': 2, 'path': [0], 'read_only': True, 'slot': 1}, {'kind': 2, 'path': [1], 'read_only': True, 'slot': 1}]
}

with open("./contract/target/contract.abi", "r") as f:
    func_list = json.load(f)

index = 0
for i, func in enumerate(func_list):
    if "name" not in func.keys():
        continue
    if func["name"] not in ground_true_dict.keys():
        continue
    index += 1
    temp_ground_true_conflict_fields = ground_true_dict[func["name"]]
    if hash(str(temp_ground_true_conflict_fields)) == hash(str(func["conflictFields"])):
        print(func["name"] + " : pass")
    else:
        print(func["name"] + " : fail")
print("Passing Rate: " + str(index/len(ground_true_dict)) +
      " (" + str(index) + "/" + str(len(ground_true_dict)) + ")")
