""" This module contains the functions that help with the specification handling
    in the tool. """
from helper_files.analyse_specification import get_functions

def add_specification_to_code(absolute_header_path: str, code, improve):
    """Add the specification to the code. It makes sure to remove an existing specification
    Args:
        header_file_path: The path to the header file
        code: The code to add the specification to
    Returns:
        None"""
    # Get the specification code from the header file path
    specification_code = ""
    with open(absolute_header_path, "r", encoding="utf-8") as f:
        specification_code = f.read()

    # Replace the last semicolumn in the specification with an opening curly bracket
    if (improve):
        specification_code = specification_code[::-1].replace(";", "\n", 1)[::-1]
    else:
        specification_code = specification_code[::-1].replace(";", "{\n", 1)[::-1]

    

    # Turn the code into a list for each row
    code_split = [x + "\n" for x in code.split("\n")]

    # Get the line of the first function
    function_start_line = get_functions(code_split)[0][0]

    # Remove everything before and including the beginning to function_start_line
    code = code.split("\n")[function_start_line:]

    # Convert the list back to a string
    code = "\n".join(code)

    # Add the header code to the generated code if it is not already there
    if specification_code not in code:
        code = specification_code + code

    return code
