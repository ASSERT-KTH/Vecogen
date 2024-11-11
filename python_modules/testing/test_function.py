import os
import subprocess
import json

def execute_command_with_timeout(command, timeout):
    """
    Executes a shell command with a specified timeout.
    
    Parameters:
    - command: list or str, the command to execute.
    - timeout: int or float, the timeout duration in seconds.
    
    Returns:
    - stdout: str, the standard output from the command.
    - stderr: str, the standard error from the command.
    - returncode: int, the return code from the command execution.
    
    Raises:
    - subprocess.TimeoutExpired: if the command execution exceeds the timeout.
    - subprocess.CalledProcessError: if the command exits with a non-zero status.
    - Exception: for any other exceptions that occur.
    """
    try:
        # Execute the command with the specified timeout
        result = subprocess.run(
            command,
            check=True,                # Raises CalledProcessError if return code is non-zero
            capture_output=True,       # Captures stdout and stderr
            text=True,                 # Returns output as text strings
            stdin=subprocess.DEVNULL,  # Prevents the subprocess from waiting for input
            timeout=timeout            # Timeout for the command execution
        )
        # Return the output and return code
        return result.stdout, result.stderr, result.returncode

    except subprocess.TimeoutExpired as e:
        print(f"Command '{e.cmd}' timed out after {timeout} seconds.")
        # Re-raise the exception if you want the calling code to handle it
        raise

    except subprocess.CalledProcessError as e:
        print(f"Command '{e.cmd}' exited with non-zero status {e.returncode}.")
        print(f"Standard Error Output:\n{e.stderr}")
        # Re-raise the exception if you want the calling code to handle it
        raise

    except Exception as e:
        print(f"An unexpected error occurred: {e}")
        # Re-raise the exception if you want the calling code to handle it
        raise

def test_generated_code(path_file, path_test, test_file_name, output_path, debug):
    """ Function that tests a generated file
    Args:
        path_file: The path to the generated file
        path_test: The path to the test file
        test_file_name: The name of the test executable
        output_path: The directory where the executable and output will be placed
        debug: Boolean flag for printing debug information
    Returns:
        passed: The number of tests that passed
        total: The total number of tests
        tests_output: The output from the tests, typically a summary dictionary
    """

    # If debugging is true then print information that the file will be tested
    if debug:
        print(f"Testing the file {path_file}\n      using the test file {path_test}")

    # Normalize paths
    path_file = os.path.normpath(path_file)
    path_test = os.path.normpath(path_test)

    # Create the output directory if it does not exist
    if not os.path.exists(output_path):
        os.makedirs(output_path)

    path_to_executable = os.path.normpath(os.path.join(output_path, test_file_name))

    # Compile the file and the test cases
    print("Step 1. Compiling the test function")
    command = [
        "gcc",
        path_file,
        path_test,
        "-o",
        path_to_executable
    ]

    try:
        # Use the execute_command_with_timeout function
        stdout, stderr, returncode = execute_command_with_timeout(command, timeout=120)
        if debug:
            print("Compilation output:", stdout)
        print("Compilation complete!")
    except subprocess.TimeoutExpired as e:
        print("Compilation timed out!")
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": f"Compilation timed out: {str(e)}"}}
    except subprocess.CalledProcessError as e:
        print("Compilation failed!")
        print(e.stderr)
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": f"Compilation failed: {e.stderr}"}}
    except Exception as e:
        print(f"An unexpected error occurred during compilation: {e}")
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": f"Compilation error: {str(e)}"}}

    print("Step 2. Compiled. Now running the test cases")

    # Run the test cases
    command = [path_to_executable, f"{path_to_executable}.json"]
    try:
        # Use the execute_command_with_timeout function
        stdout, stderr, returncode = execute_command_with_timeout(command, timeout=1200)
        if stderr:
            print("Test execution failed!")
            print(stderr)
    except subprocess.TimeoutExpired as e:
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": f"Test execution timed out: {str(e)}"}}
    except subprocess.CalledProcessError as e:
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": f"Test execution failed: {e.stderr}"}}
    except OSError as e:
        print(f"Error: The test cases could not be run. {str(e)}")
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": f"Execution error: {str(e)}"}}
    except Exception as e:
        print(f"An unexpected error occurred during test execution: {e}")
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": f"Execution error: {str(e)}"}}

    print("Step 3. Test cases run. Now reading the output")

    # Verify the JSON file existence
    json_file_path = path_to_executable + ".json"
    if not os.path.exists(json_file_path):
        print(f"Error: The output JSON file '{json_file_path}' was not created.")
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": "Output JSON file missing."}}

    # Read the output JSON file
    try:
        with open(json_file_path, "r", encoding="utf-8") as file:
            tests_output = json.load(file)
            test_information = tests_output[-1]['summary']
            passed = test_information['passed']
            total = test_information['total']
    except (json.JSONDecodeError, KeyError, IndexError) as e:
        print(f"Error reading JSON file: {str(e)}")
        return 0, 0, {"summary": {"passed": 0, "failed": 0, "total": 0, "information": "Invalid JSON format."}}

    # Clean up
    try:
        os.remove(path_to_executable)
        os.remove(json_file_path)
    except OSError as e:
        print(f"Error during cleanup: {str(e)}")

    return passed, total, tests_output
