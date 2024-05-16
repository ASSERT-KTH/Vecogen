""" This module is used to check a C file in a given directory"""
from Verify_files.compile_file import compile_c
from Verify_files.verify_file import verify_file

def check_file(absolute_path_to_c_file, absolute_path_to_h_file, args):
    """Check a C file in a given directory
    Args:
        args: The arguments given to the program
        file_name_c: The name of the C file
        file_name_h: The name of the header file
    Returns:
        True if the C file verified successfully, False otherwise
        If the file did not verify, the output of the verification"""

    if args.debug:
        print(f"Files {absolute_path_to_c_file.split('/')[-1]} and " +
          f"{absolute_path_to_h_file.split('/')[-1]} exists, starting to compile...")

    # Compile the file
    # Get the directory of absolute_path_to_c_file

    result, output = compile_c(args, absolute_path_to_c_file, args.temp_folder)
    if result is False:
        if args.debug:
            print(f"Compilation of file {absolute_path_to_c_file.split('/')[-1]} failed," +
              f"Error:\n {output}")
            return False, output, None
    elif args.debug:
        print(f"File {absolute_path_to_c_file.split('/')[-1]} compiled successfully" +
              " and will be verified...")

    # Verify the file and return it
    return verify_file(args)
