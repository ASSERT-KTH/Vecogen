""" This module contains functions that verify the input given by the user. 
    The functions check if the input is valid and if the files and directories exist."""
import sys
import os
from helper_files.list_files import get_absolute_path
from Frama_C.solvers import solvers

def require_directory(args):
    """Function to check if a directory is given in the arguments
    Args:
        args: The arguments given by the user
    Returns:
        None"""
    if not args.directory:
        print("Please insert a directory using the -d or --directory option")
        sys.exit()

def require_directory_exists(args):
    """Function to check if a directory exists
    Args:
        args: The arguments given by the user
    Returns:
        None"""

    # Make sure a directory is given in the arguments
    require_directory(args)

    # Change the relative path to the absolute path
    old_directory = args.directory
    args.directory = get_absolute_path(args.directory)

    # Make sure the directory exists
    if not os.path.isdir(args.directory):
        print(f"Please insert a valid directory, {old_directory} is not a directory")
        sys.exit()

def require_header_file(args):
    """Function to check if a header file is given in the arguments
    Args:
        args: The arguments given by the user
    Returns:
        None"""

    if not args.header_file:
        print("Please insert a header file using the -he or --header_file option")
        sys.exit()
        
    # See if the header path is relative or absolute
    if not os.path.isabs(args.header_file):
        args.relative_header_path = args.header_file
        args.absolute_header_path = os.path.join(os.getcwd(), args.header_file)
        args.header_file_name = os.path.basename(args.header_file)
    else:
        args.absolute_header_path = args.header_file
        args.relative_header_path = os.path.relpath(args.header_file)
        args.header_file_name = os.path.basename(args.header_file)

    # Make sure the header file exists
    if not os.path.isfile(args.absolute_header_path):
        print(f"Please insert a valid header file, {args.header_file} is not a file")
        sys.exit()	

def require_c_file(args):
    """Function to check if a C file is given in the arguments
    Args:
        args: The arguments given by the user
    Returns:
        None"""

    if not args.c_file:
        print("Please insert a C file using the -c or --c_file option")
        sys.exit()

    # See if the C path is relative or absolute
    if not os.path.isabs(args.c_file):
        args.relative_c_path = args.c_file
        args.absolute_c_path = os.path.join(os.getcwd(), args.c_file)
        args.c_file_name = os.path.basename(args.c_file)
    else:
        args.absolute_c_path = args.c_file
        args.relative_c_path = os.path.relpath(args.c_file)
        args.c_file_name = os.path.basename(args.c_file)
        
    # Make sure the C file exists
    if not os.path.isfile(args.absolute_c_path):
        print(f"Please insert a valid C file, {args.c_file} is not a file")
        sys.exit()

def require_solver(args):
    """Function to check if the solver in the arguments is available
    Args:
        args: The arguments given by the user
    Returns:
        None"""

    # Get the solvers
    available_solvers = solvers()

    # If no solver is present then use all the solvers available
    if args.solver is None:
        args.solver = ",".join(available_solvers)
    # If the solver is not available then exit
    elif args.solver not in available_solvers:
        print(f"The solver {args.solver} is not available, please use one of the  \
              following solvers: {available_solvers}")
        sys.exit()

def require_api_key_gpt():
    """Function to check if the API key for the OPENAI GPT is set
    Args:
        None
    Returns:
        None"""
    API_KEY_GPT = os.getenv("OPENAI_API_KEY")

    if API_KEY_GPT is None:
        print("API key not set")
        sys.exit()
        
def check_output_path(args):
    """Function to check if the output path is set
    Args:
        args: The arguments given by the user
    Returns:
        None"""
    if not args.output_path:
        print("Please insert an output path using the -o or --output_path option")
        sys.exit()

    # Only do this if the file is not to be updated
    if args.output_path.endswith(".c"):
        args.output_path = args.output_path[:-2]
    args.output_path = get_absolute_path(args.output_path)

    # Check if the output path is a director, if not then createi t 
    if not os.path.isdir(args.output_path):
        os.makedirs(args.output_path)

def ensure_integers(args):
    """ Function to ensure that the integers are valid. 
    Here one can define the minimum and maximum values of the integers
    Args:
        args: The arguments given by the user
    Returns:
        None"""

    # Ensure that the weakest precondition timeout is a positive integer
    if args.wp_timeout is not None and args.wp_timeout <= 0:
        print("The weakest precondition timeout must be a strictly positive integer")
        sys.exit()

    # Ensure that the number of iterations is a positive integer
    if args.iterations is not None and args.iterations <= 0:
        print("The number of iterations must be a strictly positive integer")
        sys.exit()

    # Ensure that the maximum tokens is a positive integer
    if args.max_tokens is not None and args.max_tokens <= 0:
        print("The maximum tokens must be a strictly positive integer")
        sys.exit()

    # Ensure that the temperature is a positive value between 0 and 1
    if args.temperature is not None and args.temperature < 0:
        print("The temperature must be a positive value")
        sys.exit()
    elif args.temperature > 1:
        print("The temperature must be a value between 0 and 1")
        sys.exit()

    # Ensure that the weakest precondition steps is a positive integer
    if args.wp_steps is not None and args.wp_steps <= 0:
        print("The weakest precondition steps must be a positive integer")
        sys.exit()

    # Ensure that the reboot is a positive integer
    if args.reboot is not None and args.reboot <= 0:
        print("The reboot must be a positive integer")
        sys.exit()
