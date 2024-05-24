""" This module tests a function that is generated using gcc"""
import os
import subprocess
from io import StringIO
import json
import time

def test_generated_code(path_file, path_test, test_file_name, output_path, debug):
    """ Function that tests a generated file
    Args:
        path_file: The path to the generated file
        path_test: The path to the test file
    Returns:
        The amount of tests that passed
        The total amount of tests"""

    # If debugging is true then print information that the file will be tested
    if debug:
        print(f"Testing the file {path_file} with the test file {path_test}")

    # Remove ../ from the paths
    path_file = os.path.normpath(path_file)
    path_test = os.path.normpath(path_test)

    # Create the output directory if it does not exist
    if not os.path.exists(output_path):
        os.makedirs(output_path)

    path_to_executable = os.path.join(output_path, test_file_name)

    # Compile the file and the test cases, if the compilation fails then return 0 tests passed
    process = subprocess.Popen(
    ["gcc", path_file, path_test, "-o", path_to_executable],
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE
    )
    
    stdout, stderr = process.communicate()
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    
    
    # If the executable does not exist then wait, since the compilation might still be running
    while not os.path.exists(path_to_executable):
        time.sleep(0.3)
        print("Waiting for the compilation to finish...")
        print(f"stdout: {stdout}")
        print(f"stderr: {stderr}")


    # Run the test cases
    try:
        subprocess.Popen([path_to_executable, f"{path_to_executable}.json"],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError:
        print("Error: The test cases could not be run. The file might not be compiled correctly.")
        time.sleep(0.5)
        subprocess.Popen([path_to_executable, path_to_executable + ".json"],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # If debugging is true then print information that the file will be tested
    if debug:
        print(f"Compiled the file {path_file} with the test file " +
              f"{path_test} to {path_to_executable}")

    # Wait until the test cases are done and the json is created
    while not os.path.exists(path_to_executable + ".json"):
        time.sleep(0.3)
        print("Waiting for the test cases to finish...")

    # Remove the executable
    os.system(f"rm '{path_to_executable}'")

    # Print the output of the test cases by reading the output file
    with open(path_to_executable + ".json", "r", encoding="utf-8") as file:
        # Read the test output as a pandas json
        tests_output = json.load(StringIO(file.read()))

        # Print the last row
        test_information = tests_output[-1]['summary']
        passed = test_information['passed']
        total = test_information['total']

    # Remove the json test file
    os.system(f"rm '{path_to_executable}.json'")
    return passed, total, tests_output
