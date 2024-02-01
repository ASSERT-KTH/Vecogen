## This file lists all the files in a given directory
import os
import sys
from helper_files.compile_c import compile_c
import subprocess

# Function to list all the files in a given directory
def list_files_in_directory(directory):
    # Set the path to the directory
    path_to_directory = os.path.join(os.getcwd(), "..", directory)

    # List all the files in the directory
    files = os.listdir(path_to_directory)

    # Return the list of files
    print(files)

# Function that uses Frama-C to verify a C file
def verify_c_file(path_to_c_file):
    # Get the header path
    path_to_h_file = path_to_c_file.split(".")[0] + ".h"

    # Call a subroutine to use Frama-C to verify the C file
    result = subprocess.Popen(f"frama-c -wp {path_to_c_file} {path_to_h_file}", stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)

    # Return the result
    if result == 0:
        return True, result
    else:
        return False, result


# Verifies a file in a given directory
def verify_files(directory, file_name_c):
    # Get the path to the file
    path_to_directory = os.path.join(os.getcwd(), "..", directory)
    path_to_file = os.path.join(path_to_directory, file_name_c)

    # Check if the file exists
    if not os.path.exists(path_to_file):
        print("File does not exist")
        sys.exit()

    # Compile the file
    result, path_to_executable, result = compile_c(path_to_file)
    if result == False:
        print(f"File {file_name_c} did not compile successfully")
        sys.exit()
    else: 
        print(f"File {file_name_c} compiled successfully")

    # Verify the file
    result, result_of_verification = verify_c_file(path_to_file)
        
        

__all__ = ["list_files_in_directory", "verify_files"]