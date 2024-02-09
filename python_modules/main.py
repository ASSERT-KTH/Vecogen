""" This is the main file for the tool. It contains the main function that is called 
    when the tool is run. It also contains the functions that are called based on the 
    arguments given to the tool. """
import sys
import os
import argparse
from dotenv import load_dotenv
from helper_files.list_files import list_files_directory
from helper_files.verify_input import require_directory_exists, require_header_file, \
    require_c_file, require_solver, require_api_key_gpt
from Verify_files.check_file import check_file
from LLM.prompts import initial_prompt
from LLM.pipeline import generate_code as generate_code_pipeline

def list_files(args):
    """List the files in a directory"""
    require_directory_exists(args)
    
    print(list_files_directory(args.directory))

def verify(args):
    """Verify a C file and a header file"""
    # Make sure the header and C file are given in the arguments
    require_c_file(args)
    require_solver(args)

    # Verify the file
    check_file(args)

def verify_dir(args):
    """Verify a directory""" 
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
    check_file(args)

def generate_initial_prompt(args):
    """ Generate the initial prompt for the code generation"""
    require_header_file(args)
    print(initial_prompt(args.header_file, args.model_name, args.max_tokens))

def generate_code(args):
    """ Generate code using the pipeline and the LLM model"""
    require_solver(args)
    require_header_file(args)
    require_api_key_gpt()
    generate_code_pipeline(args)

def parse_arguments(functions_list):
    """Parse the arguments given to the tool"""
    # Create argument parser
    parser = argparse.ArgumentParser()

    # Positional mandatory arguments
    parser.add_argument("function", help="The function to call", type=str, 
                        choices=functions_list)

    # Optional arguments
    parser.add_argument("-d", "--directory", help="The directory to use", type=str)
    parser.add_argument("-c", "--c_file", help="The C file to use", type=str)
    parser.add_argument("-he", "--header_file", help="The header file to use", type=str)
    parser.add_argument("-wpt", "--wp_timeout", help="The timeout to use for the wp-prover",
                        type=int, default=90)
    parser.add_argument("-wps", "--wp_steps", help="The steps to use for the wp-prover",
                        type=int, default=1500)
    parser.add_argument("-s", "--solver", help="The solver to use for the formal verification",
                        type=str)
    parser.add_argument("-sd", "--smoke_detector", help="The smoke detector to use for the \
                        formal verification", type=bool, action=argparse.BooleanOptionalAction,
                        default=False)
    parser.add_argument("-iter", "--iterations", help="The number of iterations to use for \
                        the code generation", type=int, default=1)
    parser.add_argument('-temp', '--temperature', help="The temperature to use for the code \
                        generation", type=float, default=0)
    parser.add_argument('-mt', '--max_tokens', help="The maximum tokens to use for the code \
                        generation", type=int, default=2048)
    parser.add_argument('-o', '--output_path', help="The output path to use for the code \
                        generation", type=str, default="tmp")
    parser.add_argument('-debug', '--debug', help="The debug mode, outputs more information \
                        to the console", type=bool, action=argparse.BooleanOptionalAction, \
                        default=False)
    parser.add_argument('-model', '--model_name', help="The model name to use for the \
                        code generation", type=str, default="gpt-3.5-turbo")

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
    arguments = parse_arguments(list(switcher.keys()))

    # Get the function from switcher dictionary
    switcher.get(arguments.function, lambda: "Invalid function")(arguments)
