""" This module is used to check a C file in a given directory"""
import sys
from Verify_files.compile_file import compile_c
from Verify_files.verify_file import verify_file

def check_file(args):
    """Check a C file in a given directory
    Args:
        args: The arguments given to the program
    Returns:
        True if the C file verified successfully, False otherwise
        If the file did not verify, the output of the verification"""
    # Get juts the name of the C and the header file
    file_name_c = args.c_file.split("/")[-1]
    file_name_h = args.header_file.split("/")[-1]

    print(f"Files {file_name_c} and {file_name_h} exists, starting to compile...")

    # Compile the file
    result, output = compile_c(args.c_file)
    if result is False:
        print(f"Compilation of file {file_name_c} failed, Error:\n {output}")
        sys.exit()
    else:
        print(f"File {file_name_c} compiled successfully")

    print(f"File {file_name_c} will be verified...")

    # Verify the file
    return verify_file(args, args.c_file)
