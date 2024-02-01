import sys
import os
from verify_file import list_files_in_directory, verify_files

def hello_world():
    print("Hello world!")

def list_files():
    # Make sure a directory is given as second argument
    if len(sys.argv) < 3:
        print("Please insert a directory as second argument")
        sys.exit()

    # Get the directory from the second argument
    directory = sys.argv[2]

    # Make sure the directory exists
    if not os.path.exists("../"+directory):
        print(directory)
        print("Directory does not exist")
        sys.exit()

    # Call the function
    list_files_in_directory(directory)

def verify_file():
    # Make sure a directory is given as second argument
    if len(sys.argv) < 3:
        print("Please insert a directory as second argument")
        sys.exit()
    
    # Make sure the second argument is a directory
    if not os.path.isdir("../"+sys.argv[2]):
        print(f"Please insert a directory as second argument, {sys.argv[2]} is not a directory")
        sys.exit()

    # Make sure a C file is given as third argument
    if len(sys.argv) < 4 and not sys.argv[3].endswith(".c"):
        print("Please insert a C file as third argument")
        sys.exit()

    # Get the directory from the second argument
    directory = sys.argv[2]

    # Make sure the directory exists
    if not os.path.exists("../"+directory):
        print(f"Directory {directory} does not exist")
        sys.exit()

    # Call the function
    verify_files(directory, sys.argv[3])

if __name__ == "__main__":
    # Implemented functions
    imp_functions = ["hello_world", "list_files", "verify_file"]

    # Get the user input argument
    if len(sys.argv) > 1:
        user_input = sys.argv[1]
    else:
        print("No input arguments, please insert one of the following: ", imp_functions)
        sys.exit()

    # Check if user input is in implemented functions
    if user_input in imp_functions:
        # Call the function
        globals()[user_input]()
    else:
        print("Invalid implemented function, please insert one of the following: ", imp_functions)


