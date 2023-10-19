import json
import sys

# Ground true of test cases
ground_true_dict = {
    "visit_val_container": [{'kind': 0, 'value': [], 'read_only': False, 'slot': 0}],
    "change_complex_data_structure": [{'kind': 1, 'value': [], 'read_only': False, 'slot': 7}],
    "test_env_caller": [{'kind': 2, 'value': [0], 'read_only': True, 'slot': 1}],
    "test_env_tx_origin": [{'kind': 2, 'value': [1], 'read_only': True, 'slot': 1}],
    "test_env_now": [{'kind': 2, 'value': [2], 'read_only': True, 'slot': 2}],
    "test_env_block_number": [{'kind': 2, 'value': [3], 'read_only': True, 'slot': 3}],
    "test_env_address": [{'kind': 2, 'value': [4], 'read_only': True, 'slot': 1}],
    "test_method_parameter":  [{'kind': 3, 'value': [0, 0], 'read_only': True, 'slot': 3}],
    "test_constant_positive": [{'kind': 4, 'value': [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'read_only': True, 'slot': 4}],
    "test_constant_zero": [{'kind': 4, 'value': [0], 'read_only': True, 'slot': 5}],
    "test_constant_negative": [{'kind': 4, 'value': [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255], 'read_only': True, 'slot': 6}],
    "test_interprocedural_calling": [{'kind': 3, 'value': [0, 0], 'read_only': True, 'slot': 3}],
    "test_branch_statement": [{'kind': 2, 'value': [0], 'read_only': True, 'slot': 1}, {'kind': 2, 'value': [1], 'read_only': True, 'slot': 1}]
}

# Compare two conflict domain results
def cmp(test_case_data, ground_true_data):
    if isinstance(test_case_data, dict):
        for key in ground_true_data:
            if key not in test_case_data:
                print("Attribute %s does not exist in the test case" % (key))
                #sys.exit(1)
        for key in test_case_data:
            if key in ground_true_data:
                print("Comparing attribute: %s" % (key))
                cmp(test_case_data[key], ground_true_data[key])
    elif isinstance(test_case_data, list):
        if len(test_case_data) != len(ground_true_data):
            print("Error message: the number of conflict domains is not equal.")
            print("  Number of conflict domains for test case: %d" % (len(test_case_data)))
            print("  Number of conflict domains for ground true: %d" % (len(ground_true_data)))
            #sys.exit(1)
        else:
            for test_case, ground_true in zip(test_case_data, ground_true_data):
                if isinstance(test_case, dict):
                    #//print("--------------------------------------------------------")
                    global conflict_index
                    conflict_index += 1
                    print("Processing conflict %d" % (conflict_index))
                cmp(test_case, ground_true)
    else:
        if str(test_case_data) != str(ground_true_data):
            print("  Error message: attribute values are not equal.")
            print("    Attribute value of test case: %s" % (test_case_data))
            print("    Attribute value of ground true: %s" % (ground_true_data))
            #sys.exit(1)

# Open the abi file of the contract under test
with open("./contract/target/contract.abi", "r") as f:
    func_list = json.load(f)

# Recorder of triggered test cases
triggered_test_cases_record = [0]*len(ground_true_dict)

# Analyze test cases one by one
for i, func in enumerate(func_list):
    # Ignore the constructor
    if "name" not in func.keys():
        continue

    # Ignore functions outside the scope of the test
    if func["name"] not in ground_true_dict.keys():
        continue

    # Record processed test cases
    temp_index = list(ground_true_dict.keys()).index(func["name"])
    triggered_test_cases_record[temp_index] = 1

    # Compare conflict result
    #print("--------------------------------------------------------")
    print("Processing test case: %s" % (func["name"]))
    conflict_index = 0
    cmp(func["conflictFields"], ground_true_dict[func["name"]])
    #print("--------------------------------------------------------")
    print()


# If there is an untriggered test case, exit the program abnormally, otherwise exit normally
if 0 in triggered_test_cases_record:
    print("Error message: not all test cases are triggered.")
    sys.exit(1)
else:
    sys.exit(0)