""" Module to analyze the header of a file """
import os

def get_functions(file_path):
    """ Get the functions in a C file """
    with open(file_path, 'r') as file:
        lines = file.readlines()
    
    # Get the functions, and store a tuple of line number and function content
    functions = []


    for i, line in enumerate(lines):
        # If the line is a function, store the line number and the function
        if line.strip().startswith("void ") or line.strip().startswith("int ") or line.strip().startswith("double ") or line.strip().startswith("float ") or line.strip().startswith("char ") or line.strip().startswith("long ") or line.strip().startswith("short ") or line.strip().startswith("unsigned ") or line.strip().startswith("signed ") or line.strip().startswith("static ") or line.strip().startswith("ulong ") or line.strip().startswith("uint "):
            # Get the function name
            function = line.strip().split("(")[0].split(" ")[-1]
            functions.append((i + 1, line))
        elif line.strip().startswith("struct"):
            # Get the function name
            function = line.strip().split(" ")[-1]
            functions.append((i + 1, function))

    return functions