import subprocess
import os

## Helper function that tries to compile a C file
# @param file_name The name of the C file to compile
# @return True if the C file compiled successfully, False otherwise
# @return The path to the executable file if the C file compiled successfully, None otherwise

def compile_c(path_to_c_file):
    # Have the output of the gcc compiler go to the /tmp folder
    tmp_path = os.path.join(os.getcwd(), "../tmp")

    # Create the output directory if it does not exist
    if not os.path.exists(tmp_path):
        print("make")
        os.makedirs(tmp_path)

    # Set the path to the executable file
    file_name = path_to_c_file.split("/")[-1].split(".")[0]
    path_to_executable = os.path.join(tmp_path, f"{file_name}")

    # Run the gcc compiler on the C file
    result = subprocess.Popen(["gcc", path_to_c_file, "-o", path_to_executable], 
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # Capture the command prompt output
    stdout, stderr = result.communicate()

    # Return the result and command prompt output
    if result.returncode == 0:
        return True, path_to_executable, stdout.decode("utf-8")
    else:
        print(f"Compilation of file {file_name} Error: {stderr.decode('utf-8')}")
        return False, None, stderr.decode("utf-8")

__all__ = ["compile_c"]