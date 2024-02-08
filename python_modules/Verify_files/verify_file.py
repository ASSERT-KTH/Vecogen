import subprocess
import re

## Helper function that uses Frama-C to verify a C file
# @param args The arguments given to the program
# @param path_to_c_file The path to the C file to verify
# @param path_to_h_file The path to the header file to verify
# @return True if the C file verified successfully, False otherwise
# @return The result of the verification

# Function that uses Frama-C to verify a C file
def verify_file(args, path_to_c_file, path_to_h_file):
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

    # Get the amount of verified goals by querying for " [wp] Proved goals:   19 / 22"
    verified_goals = stdout_str.split("Proved goals:")[1].split("/")[0].strip()
    total_goals = stdout_str.split("Proved goals:")[1].split("/")[1].strip()
    total_goals = total_goals.split("\n")[0].strip()
    print(f"Verified goals: {verified_goals} of {total_goals}")

    # Get the amount of timeouts by querying for "Timeouts: 3 / 22"
    if "Timeout" in stdout_str:
        total_timeouts = stdout_str.split("Timeout:")[1]
        total_timeouts = total_timeouts.split("\n")[0].strip()
        print(f"Timeouts: {total_timeouts} of {total_goals}\n")

        # Print the lines that caused the timeouts
        print("Lines that caused timeouts:")
        for line in stdout_str.split("\n"):
            if "Goal" in line  and "*" not in line:
                # Remove the path from the line, thus remove everything between / and /
                pattern = r'\(file\s+\/.*?\/tmp\/'
                line_without_path = re.sub(pattern, '(file ', line)
                print(line_without_path)
    # If the debug is enabled, print the output of the command prompt
    if args.debug:
        print(stdout_str, stderr_str)

    # Return the result and command prompt output
    if result.returncode == 0:
        return True, stdout_str
    else:
        return False, stderr_str

__all__ = ["verify_file"]
