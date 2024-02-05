import os
## Helper function to list all the files in a given directory
# @param directory The directory to list the files in
# @return The list of files in the directory

# Function to list all the files in a given directory
def list_files_directory(directory):
    return os.listdir(directory)

# Function that gets the absolute path to the files
def get_absolute_path(relative_path):
    return os.path.join(os.getcwd(), "..", relative_path)

__all__ = ["list_files_directory", "get_absolute_path"]