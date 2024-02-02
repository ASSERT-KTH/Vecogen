import subprocess

## Helper function that uses Frama-C to verify a C file
# @param path_to_c_file The path to the C file to verify
# @return True if the C file verified successfully, False otherwise
# @return The result of the verification

# Function that uses Frama-C to verify a C file
def verify_file(path_to_c_file):
    # Get the header path
    path_to_h_file = path_to_c_file.split(".")[0] + ".h"

    # Call a subroutine to use Frama-C to verify the C file
    result = subprocess.Popen(f"frama-c -wp {path_to_c_file} {path_to_h_file}", stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)

    # Return the result
    if result == 0:
        return True, result
    else:
        return False, result

__all__ = ["verify_file"]