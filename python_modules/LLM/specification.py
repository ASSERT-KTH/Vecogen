""" This module contains the functions that help with the specification handling
    in the tool. """
from helper_files.analyse_specification import get_functions

def add_specification_to_code(header_file_path: str, code):
    """Add the specification to the code. It makes sure to remove an existing specification
    Args:
        
    Returns:
        None"""
    # Get the specification code from the header file path
    specification_code = ""
    with open(header_file_path, "r", encoding="utf-8") as f:
        specification_code = f.read()

    # Every line before the first function is the specification
    specification_code = specification_code.split("\n")[:-1]
    specification_code = "\n".join(specification_code) + "\n"

    # Turn the code into a list for each row
    code_split = [x + "\n" for x in code.split("\n")]

    # Get the line of the first function
    function_start_line = get_functions(code_split)[0][0] - 1

    # Remove everything from the beginning to function_start_line
    code = code.split("\n")[function_start_line:]

    # Convert the list back to a string
    code = "\n".join(code)

    # Add the header code to the generated code if it is not already there
    if specification_code not in code:
        code = specification_code + code

    return code
