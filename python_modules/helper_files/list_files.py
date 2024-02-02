import os
## Helper function to list all the files in a given directory
# @param directory The directory to list the files in
# @return None

# Function to list all the files in a given directory
def list_files_directory(directory):
    # Set the path to the directory
    path_to_directory = os.path.join(os.getcwd(), "..", directory)

    # List all the files in the directory
    files = os.listdir(path_to_directory)

    # Return the list of files
    print(files)

__all__ = ["list_files_directory"]
