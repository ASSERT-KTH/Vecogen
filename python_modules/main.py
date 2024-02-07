import sys
import os
from dotenv import load_dotenv
import argparse
from helper_files.list_files import list_files_directory
from helper_files.verify_input import require_directory, require_directory_exists, require_header_file, require_c_file, require_solver, require_api_key_gpt
from Verify_files.check_file import check_file
from LLM.prompts import initial_prompt
from LLM.pipeline import generate_code as generate_code_pipeline

# Function to list the files in a directory
def list_files(args):
    require_directory_exists(args)
    
    print(list_files_directory(args.directory))

# Function to verify a C file and a header file
def verify(args):
    # Make sure the header and C file are given in the arguments
    require_header_file(args)
    require_c_file(args)
    require_solver(args)
    
    # Verify the file
    check_file(args)
        
# Function to verify a C file and a header file in a directory
def verify_dir(args):
    require_directory_exists(args)
    require_solver(args)

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
        
    # Get the paths to the files
    c_file = os.path.join(args.directory, c_file)
    h_file = os.path.join(args.directory, h_file)

    # Call the function
    check_file(args, c_file, h_file)
        
# Function that generates a prompt for the user
def generate_initial_prompt(args):
    require_header_file(args)
    print(initial_prompt(args.header_file))

# Function that uses the code generation pipeline based on a header file
def generate_code(args):
    require_header_file(args)
    require_api_key_gpt()
    generate_code_pipeline(args)
    
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
    parser.add_argument("-wpt", "--wp_timeout", help="The timeout to use for the wp-prover", type=int, default=90)
    parser.add_argument("-wps", "--wp_steps", help="The steps to use for the wp-prover", type=int, default=1500)
    parser.add_argument("-s", "--solver", help="The solver to use for the formal verification", type=str)
    parser.add_argument("-sd", "--smoke_detector", help="The smoke detector to use for the formal verification", type=bool, action=argparse.BooleanOptionalAction, default=False)
    parser.add_argument("-iter", "--iterations", help="The number of iterations to use for the code generation", type=int, default=1)
    
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
        "generate_code": generate_code,
    }
    
    # Load the environment variables
    load_dotenv()
    
    # Get a list of the functions
    args = parse_arguments(list(switcher.keys()))

    # Get the function from switcher dictionary
    switcher.get(args.function, lambda: "Invalid function")(args)