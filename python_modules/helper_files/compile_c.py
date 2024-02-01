import subprocess
## Helper function that tries to compile a C file
# @param file_name The name of the C file to compile
# @return True if the C file compiled successfully, False otherwise
# @return The path to the executable file if the C file compiled successfully, None otherwise

def compile_c(path_to_c_file):
    # Have the output of the gcc compiler go to the /tmp folder
    path_to_executable = "/tmp/" + path_to_c_file[:-2]

    # Run the gcc compiler on the C file
    result = subprocess.call(["gcc", path_to_c_file, "-o", path_to_c_file[:-2]]) 

    # Return the result
    if result == 0:
        return True, path_to_executable
    else:
        return False, None
    
__all__ = ["compile_c"]