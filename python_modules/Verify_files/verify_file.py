"""This module is used to verify a C file using Frama-C"""
import subprocess
import re
import random
from helper_files.change_header import get_line_in_code
from helper_files.debug import debug_to_file

def verify_file(args, path_to_c_file):
    """Verify a C file using Frama-C
    Args:
        args: The arguments given to the program
        path_to_c_file: The path to the C file to verify
    Returns:
        True if the C file verified successfully, False otherwise
        If the file did not verify, the output of the verification"""
    # Create the prompt that is used for frama c
    prompt = f'frama-c  -wp "{path_to_c_file}"                                  \
                        -wp-prover {args.solver}                                \
                        -wp-steps {args.wp_steps}                               \
                        -wp-timeout {args.wp_timeout}                           \
                        -wp-rte                                                 \
                        {"-wp-smoke-tests" if args.smoke_detector else ""}      \
                        -wp-status'

    # Call a subroutine to use Frama-C to verify the C file
    result = subprocess.Popen(prompt, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)

    # Capture the command prompt output
    stdout, stderr = result.communicate()
    stdout_str = stdout.decode("utf-8")
    stderr_str = stderr.decode("utf-8")

    # See if there was an error in the command prompt
    if args.debug:
        debug_to_file(args, "../tmp/", "errors", stderr_str)

    # If the debug is enabled, print the output of the command prompt
    if args.debug:
        print(stdout_str, stderr_str)

    # Get the error cause and the strategy to solve the error
    return get_error_cause_and_strategy(stdout_str, path_to_c_file)

causes = ["Timeout", "Syntax Error", "Fatal Error", "Valid"]
def get_error_cause_and_strategy(output: str, file_path: str):
    """ Looks at a string that has the output of the verication. It returns the causes
    of the errors. Within the output also a strategy is given to solve the error.
    Args:
        output: The output of the verification
    Returns:
        A list of the problem and the strategy to solve the problem"""

    # Check if the output has a syntax error
    if "Syntax error" in output or "syntax error" in output:
        # Remove the lines with [kernel] in the output
        output = re.sub(r'\[kernel\].*?\n', '', output)
        return False, [("There is a syntax error in the code. The following output was generated:\n"
                        f"{output}")]
    # Check if the output has a fatal error
    elif "fatal error" in output:
        return False, [("There is a fatal error in the code. The following output was generated:\n"
                        f"{output}")]
    # Check if the output has a timeout
    elif "Timeout" in output:
        # We filter the timeouts in the output to make it more readable

        # Get the amount of verified goals by querying for " [wp] Proved goals:   19 / 22"
        verified_goals = output.split("Proved goals:")[1].split("/")[0].strip()
        total_goals = output.split("Proved goals:")[1].split("/")[1].strip()
        total_goals = total_goals.split("\n")[0].strip()

        # Print the amount of verified goals
        print(f"Verified goals: {verified_goals} of {total_goals}")
        total_timeouts = output.split("Timeout:")[1]
        total_timeouts = total_timeouts.split("\n")[0].strip()

        # A string that contains the information about timeouts
        timeout_string = (
            f"The verification timed out. Timeouts: {total_timeouts} of {total_goals}.\n"
            " The following lines caused the timeouts:\n"
        )

        # Get the lines that caused timeouts
        for line in output.split("\n"):
            if "Goal" in line  and "*" not in line:
                # Remove the path from the line, thus remove everything between / and /
                pattern = r'\(file\s+\/.*?\/tmp\/'
                line_without_path = re.sub(pattern, '(file ', line)

                # Get the line of code that caused the timeout, which comes after "line .."
                line_number = int(re.search(r'line\s+(\d+)', line_without_path).group(1))
                code_line = get_line_in_code(file_path, line_number)

                # Replace everything in the brackets with the code in the line
                line_without_path = re.sub(r'\([^)]*\)', code_line, "(" + line_without_path + ")")

                # Add the line in the file
                timeout_string += line_without_path

        # Get a random strategy to solve the problem
        # possible_strategies = [
        #     "Simplify the code",
        #     "Add invariants to the code",
        #     "Make the invariants stronger",
        #     "Remove an invariant",
        #     "Add assertions within the code. "  +
        #     " Use the defined predicates and put the assertions as deep as possible.",
        #     ]
        possible_strategies = ["Improve the code"]

        return False, [f"{timeout_string}. Please try to solve the problem with the following" + 
        f"strategy: {possible_strategies[random.randint(0, len(possible_strategies) - 1)]}"]

    # Otherwise the file is valid
    else:
        return True, ["The file is valid"]

__all__ = ["verify_file"]
