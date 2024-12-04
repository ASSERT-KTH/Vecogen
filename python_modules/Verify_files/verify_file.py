"""This module is used to verify a C file using Frama-C"""
import subprocess
import re
import time
from Frama_C.frama_c_parser import get_line_number_in_parsed_code
from helper_files.debug import debug_to_file

def verify_file(args):
    """Verify a C file using Frama-C
    Args:
        args: The arguments given to the program
    Returns:
        True if the C file verified successfully, False otherwise
        A message that indicates the problem
        The amount of verified goals
        The verification time
        """
    # If debugging is enabled then print the folder that the file is being verified in
    if args.debug:
        print("Verifying file...")

    # Start the timer
    start_time = time.time()

    # Create the prompt that is used for frama c
    prompt = f"frama-c  -wp '{args.absolute_c_path}'  -wp-prover {args.solver} -wp-steps {args.wp_steps} -wp-timeout {args.wp_timeout} -wp-rte {'-wp-smoke-tests' if args.smoke_detector else ''} -wp-status"

    # Call a subroutine to use Frama-C to verify the C file
    result = subprocess.Popen(prompt, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)

    # Wait for the process to complete
    try:
        result.wait(600)
    except subprocess.TimeoutExpired:
        print("Timeout expired. Killing the process.")
        result.kill()
        return False, "Timeout", "0 / 0", 600

    # End the timer
    end_time = time.time()

    # Calculate the elapsed time
    elapsed_time = end_time - start_time

    # Capture the command prompt output
    stdout, stderr = result.communicate()
    stdout_str = stdout.decode("utf-8")
    stderr_str = stderr.decode("utf-8")

    # See if there was an error in the command prompt
    if args.debug:
        if stderr_str:
            print(f"Verification error: {stderr_str}")
        if stdout_str:
            print(f"Verification output: {stdout_str}")
        debug_to_file(args, "../tmp/", "errors", stderr_str)
        debug_to_file(args, "../tmp/", "output", stdout_str)

    # Get the error cause and the strategy to solve the error
    verified, error_cause, verified_goals_amount = get_error_cause_and_strategy(
        stdout_str, args.absolute_c_path)

    return verified, error_cause, verified_goals_amount, elapsed_time

causes = ["Timeout", "Syntax Error", "Fatal Error", "Valid"]

def get_error_cause_and_strategy(output: str, absolute_c_path: str):
    """ Looks at a string that has the output of the verication. It returns the causes
    of the errors. Within the output also a strategy is given to solve the error.
    Args:
        output: The output of the verification
        absolute_c_path: The absolute path of the C file
    Returns:
        A tuple with the following elements:
        - A boolean that indicates if the file is valid
        - A list of the problem and the strategy to solve the problem
        - A string that contains the amount of verified goals
        
        """

    # Check if the output has a syntax error
    if "Syntax error" in output or "syntax error" in output or "invalid user input" in output:
        # Remove the lines with [kernel] in the output
        output = re.sub(r'\[kernel\].*?\n', '', output)

        return False, [("There is a syntax error in the code. The following output was generated:\n"
                        f"{output}")], "0 / 0"
    # Check if the output has a fatal error
    elif "fatal error" in output:
        return False, [("There is a fatal error in the code. The following output was generated:\n"
                        f"{output}")], "0 / 0"
    # Check if the output has a timeout
    elif "Timeout" in output:
        # Get the amount of verified goals by querying for " [wp] Proved goals:   19 / 22"
        verified_goals = output.split("Proved goals:")[1].split("/")[0].strip()
        total_goals = output.split("Proved goals:")[1].split("/")[1].strip()
        total_goals = total_goals.split("\n")[0].strip()

        # Print the amount of verified goals
        total_timeouts = output.split("Timeout:")[1]
        total_timeouts = total_timeouts.split("\n")[0].strip()

        # A string that contains the information about timeouts
        timeout_string = (
            f"The verification timed out. Timeouts: {total_timeouts} of {total_goals}.\n"
            " The following lines caused the timeouts:\n"
        )

        # Get the lines that caused timeouts
        for line in output.split("\n"):
            if "Goal" in line  and "*" not in line and "(file " in line:
                # Remove the path from the line, thus remove everything between / and /
                pattern = r'\(file\s+\/.*?\/tmp\/'
                line_without_path = re.sub(pattern, '(file ', line)

                # Get the line of code that caused the timeout, which comes after "line .."
                line_number = int(re.search(r'line\s+(\d+)', line_without_path).group(1))

                # Find the line number in the parsed Frama-C code
                code_line = get_line_number_in_parsed_code(absolute_c_path, line_number)

                # Add the line in the file
                timeout_string += f"{line_without_path.split('(')[0]} does not hold: {code_line}"

        return False, (f"{timeout_string}. Please try to solve the problem."), \
            f"{verified_goals} / {total_goals}"

    # Otherwise the file is valid
    else:
        # Get the amount of verified goals
        verified_goals = output.split("Proved goals:")[1].split("/")[0].strip()
        total_goals = output.split("Proved goals:")[1].split("/")[1].strip()
        total_goals = total_goals.split("\n")[0].strip()
        verified = verified_goals == total_goals
        return verified, ["The file is valid"], f"{verified_goals} / {total_goals}"

__all__ = ["verify_file"]
