import subprocess
import re
## Function that gets the solvers available in why3
# @return List of solvers available in why3
def solvers():
    # Create a subprocess to get the solvers available in why3
    result = subprocess.Popen("why3 config detect", stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    
    # Get the output of the detection of the solvers
    std_out_list = result.communicate()[0].decode("utf-8").split("\n")
    
    # Get the resulting solvers from the last line, everything after the first "/"
    solvers_path = std_out_list[-2].partition("/")[1:3]
    
    # Merge the "/" and the directory into one string
    solvers_path = solvers_path[0] + solvers_path[1]
    
    solver_names = []
    # Read the file path
    with open(solvers_path, "r") as file:
        solvers = file.read()
        
        # Filter the file based on "[partial_prover]"
        solvers = solvers.split("[partial_prover]")[1:]
        
        # Use a regular expression to find the solvers
        for i in range(len(solvers)):
            match = re.search(r'name = "(.*?)"', solvers[i])
            if match:
                solver_names.append(match.group(1))
        
    return solver_names

    
__all__ = ["solvers"]

    