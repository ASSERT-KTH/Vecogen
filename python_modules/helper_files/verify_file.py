import subprocess

## Helper function that uses Frama-C to verify a C file
# @param path_to_c_file The path to the C file to verify
# @return True if the C file verified successfully, False otherwise
# @return The result of the verification

# Function that uses Frama-C to verify a C file
def verify_file(path_to_c_file, path_to_h_file):
    # Call a subroutine to use Frama-C to verify the C file
    result = subprocess.Popen(f'frama-c -wp "{path_to_c_file}" "{path_to_h_file}"',
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    
    # Capture the command prompt output
    stdout, stderr = result.communicate()
    stdout_str = stdout.decode("utf-8")
    stderr_str = stderr.decode("utf-8")

    # Print the output of the verification
    print(stdout_str)
    print(stderr_str)

    # Return the result and command prompt output
    if result.returncode == 0:
        return True, stdout.decode("utf-8")
    else:
        return False, stderr.decode("utf-8")

__all__ = ["verify_file"]