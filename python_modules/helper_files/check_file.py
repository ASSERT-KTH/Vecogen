import os
import sys
from helper_files.compile_file import compile_c
from helper_files.verify_file import verify_file

## Helper function that checks a C file in a given directory
# @param directory The directory to check the C file in
# @param file_name_c The name of the C file to check
# @return None

# Checks a file in a given directory
def check_file(directory, file_name_c):
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
    result, result_of_verification = verify_file(path_to_file)