## This file lists all the files in a given directory

import os

# Function to list all the files in a given directory
def list_files_in_directory(directory):
    # Get the current working directory
    cwd = os.getcwd()

    # Set the path to the directory
    path_to_directory = os.path.join(cwd, "..", directory)

    print(path_to_directory)

    # List all the files in the directory
    files = os.listdir(path_to_directory)

    # Return the list of files
    print(files)

__all__ = ["list_files_in_directory"]