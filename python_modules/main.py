import sys
import os
import argparse
from helper_files.list_files import list_files_directory
from helper_files.check_file import check_file

def parseArguments():
    # Create argument parser
    parser = argparse.ArgumentParser()

    # Positional mandatory arguments
    parser.add_argument("function", help="The function to call", type=str, choices=["hello_world", "list_files", "verify", "verify_dir"])

    # Optional arguments
    parser.add_argument("-d", "--directory", help="The directory to use", type=str)
    parser.add_argument("-c", "--c_file", help="The C file to use", type=str)
    parser.add_argument("-he", "--header_file", help="The header file to use", type=str)
    
    # Print the version of the tool
    parser.add_argument("--version", action="version", version='%(prog)s - Version 1.0')

    # Parse arguments
    return parser.parse_args()

def list_files(args):
    # Make sure a directory is given in the arguments
    if not args.directory:
        print("Please insert a directory using the -d or --directory option")
        sys.exit()
    # Make sure the directory exists
    elif not os.path.isdir("../"+args.directory):
        print(f"Please insert a valid directory, {args.directory} is not a directory")
        sys.exit()
    else:
        print(list_files_directory(args.directory))

def verify(args):
    # Make sure the directory is given in the arguments
    if not args.directory:
        print("Please insert a directory using the -d or --directory option")
        sys.exit()
    # Make sure the directory exists
    elif not os.path.isdir("../"+args.directory):
        print(f"Please insert a valid directory, {args.directory} is not a directory")
        sys.exit()
    # Make sure the C file is given in the arguments
    elif not args.c_file:
        print("Please insert a C file using the -c or --c_file option")
        sys.exit()
    # Make sure the C file exists
    elif not os.path.isfile("../"+args.directory+"/"+args.c_file):
        print(f"Please insert a valid C file, {args.c_file} is not a file")
        sys.exit()
    # Make sure the header file is given in the arguments
    elif not args.header_file:
        print("Please insert a header file using the -he or --header_file option")
        sys.exit()
    # Make sure the header file exists
    elif not os.path.isfile("../"+args.directory+"/"+args.header_file):
        print(f"Please insert a valid header file, {args.header_file} is not a file")
        sys.exit()
    else:
        check_file(args.directory, args.c_file, args.header_file)

def verify_dir(args):
    # Make sure the directory is given in the arguments
    if not args.directory:
        print("Please insert a directory using the -d or --directory option")
        sys.exit()
    # Make sure the directory exists
    if not os.path.isdir("../"+args.directory):
        print(f"Please insert a valid directory, {args.directory} is not a directory")
        sys.exit()
    else:
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
        check_file(args.directory, c_file, h_file)

if __name__ == "__main__":
    args = parseArguments()

    switcher = {
        "list_files": list_files,
        "verify": verify,
        "verify_dir": verify_dir
    }

    # Get the function from switcher dictionary
    switcher.get(args.function, lambda: "Invalid function")(args)