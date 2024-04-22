""" This module tests a function that is generated using gcc"""
import os
import subprocess

def test_generated_code(path_file, path_test):
    """ Function that tests a generated file
    Args:
        path_file: The path to the generated file
        path_test: The path to the test file
    Returns:
        The amount of tests that passed
        The total amount of tests"""

    # Remove ../ from the paths
    path_file = os.path.normpath(path_file)
    path_test = os.path.normpath(path_test)

    # Create the output directory if it does not exist
    output_path = os.path.join(*path_file.split("/")[:-1])
    if not os.path.exists(output_path):
        os.makedirs(output_path)
    
    path_to_executable = os.path.join(output_path, f"test")
    
    # Compile the file and the test cases
    subprocess.Popen(["gcc", path_file, path_test, "-o", path_to_executable],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    
    # Run the test cases
    result = subprocess.Popen([path_to_executable],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    
    stdout, stderr = result.communicate()
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    os.system(f"rm '{path_to_executable}'")

    # Filter the output by extracting the values from the format
    result = stdout.split("Passed ")[1].split(" out of ")
    passed = int(result[0])
    total = int(result[1].split(" tests")[0])

    return passed, total
