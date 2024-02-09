"""This module is used to verify a C file using Frama-C"""
import subprocess
import re

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
    with open("errors.txt", "a", encoding="utf-8") as f:
        f.write(stdout_str)
        f.write("\n" * 5)

    # If there was a fatal error, return False and the output
    if "fatal error" in stdout_str:
        return False, stdout_str

    # Get the amount of verified goals by querying for " [wp] Proved goals:   19 / 22"
    verified_goals = stdout_str.split("Proved goals:")[1].split("/")[0].strip()
    total_goals = stdout_str.split("Proved goals:")[1].split("/")[1].strip()
    total_goals = total_goals.split("\n")[0].strip()
    print(f"Verified goals: {verified_goals} of {total_goals}")

    # Get the amount of timeouts by querying for "Timeouts: 3 / 22"
    if "Timeout" in stdout_str:
        total_timeouts = stdout_str.split("Timeout:")[1]
        total_timeouts = total_timeouts.split("\n")[0].strip()

        # A string that contains the information about timeouts
        timeout_string = f"Timeouts: {total_timeouts} of {total_goals}\n"

        # Add the lines that caused the timeouts
        timeout_string += "Lines that caused timeouts:\n"

        # Get the lines that caused timeouts
        for line in stdout_str.split("\n"):
            if "Goal" in line  and "*" not in line:
                # Remove the path from the line, thus remove everything between / and /
                pattern = r'\(file\s+\/.*?\/tmp\/'
                line_without_path = re.sub(pattern, '(file ', line)
                timeout_string += line_without_path + "\n"

    # If the debug is enabled, print the output of the command prompt
    if args.debug:
        print(stdout_str, stderr_str)

    # Return the result and command prompt output
    if verified_goals == total_goals and "Timeout" not in stdout_str:
        return True, "All goals verified successfully"
    elif "Timeout" in stdout_str:
        return False, timeout_string
    else:
        return False, stderr_str

__all__ = ["verify_file"]
