import sys
import os
import argparse
from helper_files.list_files import list_files_directory
from helper_files.verify_input import require_directory, require_directory_exists, require_header_file, require_c_file
from Verify_files.check_file import check_file
from Frama_C.solvers import solvers
from LLM.prompts import initial_prompt

# Function to list the files in a directory
def list_files(args):
    require_directory_exists(args)
    
    print(list_files_directory(args.directory))

# Function to verify a C file and a header file
def verify(args):
    # Make sure the header and C file are given in the arguments
    require_header_file(args)
    require_c_file(args)
    
    # Verify the file
    check_file(args, args.c_file, args.header_file)
        
# Function to verify a C file and a header file in a directory
def verify_dir(args):
    require_directory(args)

    # Get the files in the directory
    files = list_files_directory(args.directory)

    # Get the C and header file
    c_file = None
    h_file = None

    for file in files:
        if file.endswith(".c"):
            c_file = file
        if file.endswith(".h"):
            h_file = file

    # Check that the C and header file exist
    if c_file is None:
        print("No C file found in the directory")
        sys.exit()
    if h_file is None:
        print("No header file found in the directory")
        sys.exit()

    # Call the function
    check_file(args, c_file, h_file)
        
# Function that generates a prompt for the user
def generate_initial_prompt(args):
    require_header_file(args)
    print(initial_prompt(args.header_file))

# Function to parse arguments
def parse_arguments(functions_list):
    # Create argument parser
    parser = argparse.ArgumentParser()

    # Positional mandatory arguments
    parser.add_argument("function", help="The function to call", type=str, 
                        choices=functions_list)

    # Optional arguments
    parser.add_argument("-d", "--directory", help="The directory to use", type=str)
    parser.add_argument("-c", "--c_file", help="The C file to use", type=str)
    parser.add_argument("-he", "--header_file", help="The header file to use", type=str)
    parser.add_argument("-wpt", "--wp-timeout", help="The timeout to use for the wp-prover", type=int, default=90)
    parser.add_argument("-wps", "--wp-steps", help="The steps to use for the wp-prover", type=int, default=1500)
    parser.add_argument("-solver", "--solver", help="The solver to use for the formal verification", 
                        type=str)
    
    # Print the version of the tool
    parser.add_argument("--version", action="version", version='%(prog)s - Version 1.0')

    # Parse arguments
    return parser.parse_args()

# Main function
if __name__ == "__main__":
    # Dictionary that maps the function to the function to call
    switcher = {
        "list_files": list_files,
        "verify": verify,
        "verify_dir": verify_dir,
        "generate_prompt": generate_initial_prompt,
        "detect_solvers": detect_solvers
    }
    
    # Get a list of the functions
    args = parse_arguments(list(switcher.keys()))

    # Get the function from switcher dictionary
    switcher.get(args.function, lambda: "Invalid function")(args)