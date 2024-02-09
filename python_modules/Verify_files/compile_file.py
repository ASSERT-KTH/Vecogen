""" This module contains a function to compile a C file using the gcc compiler"""
import subprocess
import os

def compile_c(path_to_c_file):
    """Compile a C file using the gcc compiler
    Args:
        path_to_c_file: The path to the C file
    Returns:
        True if the C file compiled successfully, False otherwise
        The output of the compiler"""

    # Have the output of the gcc compiler go to the /tmp folder
    tmp_path = os.path.join(os.getcwd(), "../tmp")

    # Create the output directory if it does not exist
    if not os.path.exists(tmp_path):
        os.makedirs(tmp_path)

    # Set the path to the executable file
    file_name = path_to_c_file.split("/")[-1].split(".")[0]
    path_to_executable = os.path.join(tmp_path, f"{file_name}")

    # Run the gcc compiler on the C file
    result = subprocess.Popen(["gcc", path_to_c_file, "-o", path_to_executable, "-c"],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # Capture the command prompt output
    stdout, stderr = result.communicate()

    # Return the result and command prompt output
    if result.returncode == 0:
        return True, stdout.decode("utf-8")
    else:
        return False, stderr.decode("utf-8")

__all__ = ["compile_c"]
