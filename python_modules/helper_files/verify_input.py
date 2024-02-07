# Helper functions for the main.py file
# here input validation is done

import sys
import os
from helper_files.list_files import get_absolute_path
from Frama_C.solvers import solvers

# Function to check if a directory is given in the arguments
def require_directory(args):
    if not args.directory:
        print("Please insert a directory using the -d or --directory option")
        sys.exit()
        
# Function that checks if a directory is valid and exists
def require_directory_exists(args):
    # Make sure a directory is given in the arguments
    require_directory(args)
    
    # Change the relative path to the absolute path
    old_directory = args.directory
    args.directory = get_absolute_path(args.directory)

    # Make sure the directory exists
    if not os.path.isdir(args.directory):
        print(f"Please insert a valid directory, {old_directory} is not a directory")
        sys.exit()
    
# Function to check if a header file is given in the arguments
def require_header_file(args):
    if not args.header_file:
        print("Please insert a header file using the -he or --header_file option")
        sys.exit()
        
    # Make the relative path to the absolute path
    old_header_file = args.header_file
    args.header_file = get_absolute_path(args.header_file)
    
    # Make sure the header file exists
    if not os.path.isfile(args.header_file):
        print(f"Please insert a valid header file, {old_header_file} is not a file")
        sys.exit()	
        
# Function to check if a C file is given in the arguments
def require_c_file(args):
    if not args.c_file:
        print("Please insert a C file using the -c or --c_file option")
        sys.exit()
        
    # Make the relative path to the absolute path
    old_c_file = args.c_file
    args.c_file = get_absolute_path(args.c_file)
    
    # Make sure the C file exists
    if not os.path.isfile(args.c_file):
        print(f"Please insert a valid C file, {old_c_file} is not a file")
        sys.exit()
        
# Function that checks if the solvers are present
def require_solver(args):
    # Get the solvers
    available_solvers = solvers()
    
    # If no solver is present then use all the solvers available    
    if args.solver is None:
        args.solver = ",".join(available_solvers)
    # If the solver is not available then exit
    elif args.solver not in available_solvers:
        print(f"The solver {args.solver} is not available, please use one of the following solvers: {available_solvers}")
        sys.exit()