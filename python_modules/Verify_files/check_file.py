""" This module is used to check a C file in a given directory"""
from Verify_files.compile_file import compile_c
from Verify_files.verify_file import verify_file

def check_file(absolute_path_to_c_file, args):
    """Check a C file in a given directory"""

    if args.debug:
        print("Specification and generated file exists, starting to compile...")

    # Compile the file
    result, output = compile_c(args, absolute_path_to_c_file, args.temp_folder)

    # If the compilation failed, return False and the output
    if result is False:
        if args.debug:
            print(f"Compilation failed, Error:\n {output}")
        return False, output, None, 0
    elif args.debug:
        print("File compiled successfully")

    # Verify the file and return it
    return verify_file(args)
