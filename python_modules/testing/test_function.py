""" This module tests a function that is generated using gcc"""
import os
import sys

def test_generated_code(path_file, path_test):
    """ Function that tests a generated file
    Args:
        path_file: The path to the generated file
        path_test: The path to the test file
    Returns:
        The amount of tests that passed
        The total amount of tests"""

    # Run the test cases
    os.system(f"gcc {path_file} {path_test} -o test")
    output = os.popen("./test").read()
    os.system("rm test")

    # Filter the output by extracting the values from the following format: 
    #   "Passed %d out of %d tests"
    output = output.split("Passed ")[1].split(" out of ")
    passed = int(output[0])
    total = int(output[1].split(" tests")[0])

    return passed, total
