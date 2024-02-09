import sys
from Verify_files.compile_file import compile_c
from Verify_files.verify_file import verify_file

## Helper function that checks a C file in a given directory
# @param directory The directory to check the C file in
# @param file_name_c The name of the C file to check
# @param file_name_h The name of the header file to check
# @return True if the C file verified successfully, False otherwise

# Checks a file in a given directory
def check_file(args):
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
