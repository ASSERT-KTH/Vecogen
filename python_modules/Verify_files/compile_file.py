""" This module contains a function to compile a C file using the gcc compiler"""
import subprocess
import os

def compile_c(args, absolute_path_to_c_file, absolute_path_temp_folder):
    """Compile a C file using the gcc compiler
    Args:
        absolute_path_to_c_file: The path to the C file
        path_to_output: The path to the output file
    Returns:
        True if the C file compiled successfully, False otherwise
        The output of the compiler"""

    # Create the output directory if it does not exist
    if not os.path.exists(absolute_path_temp_folder):
        os.makedirs(absolute_path_temp_folder)

    # Set the path to the executable file
    file_name = absolute_path_to_c_file.split("/")[-1].split(".")[0]
    path_to_executable = os.path.join(absolute_path_temp_folder, f"{file_name}")

    # Run the gcc compiler on the C file
    result = subprocess.Popen(["gcc", absolute_path_to_c_file, "-o", path_to_executable, "-c"],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # If debugging is enabled then print the folder that the file is being compiled to
    if args.debug:
        print(f"Compiling file {absolute_path_to_c_file.split('/')[-1]} to {path_to_executable}")

    # Capture the command prompt output
    stdout, stderr = result.communicate()

    # # Remove the compiled file 
    # if os.path.exists(path_to_executable):
    #     os.remove(path_to_executable)

    # Return the result and command prompt output
    if result.returncode == 0:
        return True, stdout.decode("utf-8")
    else:
        return False, stderr.decode("utf-8")

__all__ = ["compile_c"]
