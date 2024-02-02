import os
import sys
from helper_files.compile_file import compile_c
from helper_files.verify_file import verify_file

## Helper function that checks a C file in a given directory
# @param directory The directory to check the C file in
# @param file_name_c The name of the C file to check
# @param file_name_h The name of the header file to check
# @return None

# Checks a file in a given directory
def check_file(directory, file_name_c, file_name_h):
    # Get the path to the file
    path_to_directory = os.path.join(os.getcwd(), "..", directory)
    path_to_c_file = os.path.join(path_to_directory, file_name_c)
    path_to_h_file = os.path.join(path_to_directory, file_name_h)

    # Check if the file exists
    if not os.path.exists(path_to_c_file):
        print("File does not exist")
        sys.exit()

    print(f"File {file_name_c} exists, starting to compile...")

    # Compile the file
    result, path_to_executable, output = compile_c(path_to_c_file)
    if result is False:
        print(f"Compilation of file {file_name_c} Error: {output}")
        sys.exit()
    else:
        print(f"File {file_name_c} compiled successfully")

    print(f"File {file_name_c} will be verified...")

    # Verify the file
    result, result_of_verification = verify_file(path_to_c_file, path_to_h_file)