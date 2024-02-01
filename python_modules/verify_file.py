## This file lists all the files in a given directory
import os
import sys
from helper_files.compile_c import compile_c

# Function to list all the files in a given directory
def list_files_in_directory(directory):
    # Set the path to the directory
    path_to_directory = os.path.join(os.getcwd(), "..", directory)

    # List all the files in the directory
    files = os.listdir(path_to_directory)

    # Return the list of files
    print(files)

# Verifies a file in a given directory
def verify_files(directory, file_name_c):
    path_to_directory = os.path.join(os.getcwd(), "..", directory)

    # Set the path to the file
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

__all__ = ["list_files_in_directory", "verify_files"]