""" This module contains the functions that help with the specification handling
    in the tool. """
import os
from helper_files.analyse_specification import get_functions

def add_specifications_to_code( absolute_formal_specification_path: str, 
                                absolute_natural_language_path: str, 
                                absolute_function_signature_path: str, code):
    """Add the specifications to the code. This adds the formal specification and function signature. If the natural language is enabled, then this is added as well.
        absolute_formal_specification_path: The path to the formal specification file
        absolute_natural_language_path: The path to the natural language specification file
        absolute_function_signature_path: The path to the function signature file
        code: The code to add the specification to
    Returns:
        None"""

    # Get the natural language code from the natural language file (if it exists)
    natural_language_code = ""
    if absolute_natural_language_path != "" and os.path.exists(absolute_natural_language_path):
        with open(absolute_natural_language_path, "r", encoding="utf-8") as f:
            natural_language_code = f.read()

    # Get the specification code from the formal specification file path
    formal_specification_code = ""
    with open(absolute_formal_specification_path, "r", encoding="utf-8") as f:
        formal_specification_code = f.read()
    
    # Get the function signature code from the function signature file path
    function_signature_code = ""
    with open(absolute_function_signature_path, "r", encoding="utf-8") as f:
        function_signature_code = f.read()

    # Replace the last semicolumn in the function signature with an opening curly bracket
    function_signature_code = function_signature_code.replace(";", " {\n", 1)

    # Create the whole specification code including the function signature
    problem_description = natural_language_code + "\n" + formal_specification_code + "\n" + function_signature_code

    code_split = [x + "\n" for x in code.split("\n")]

    # Get the line of the first function
    try:
        function_start_line = get_functions(code_split)[0][0]

        # See if the first function contains a bracket
        contains_bracket = "{" in code_split[function_start_line - 1]

        # Remove everything before and including the beginning to function_start_line
        if contains_bracket:
            code = code.split("\n")[function_start_line:]
        else:
            code = code.split("\n")[function_start_line + 1:]

        # Convert the list back to a string
        code = "\n".join(code)
        
        # Add the problem description to the code
        code = problem_description + code
    except:
        # The code does not contain a function
        print(f"ERROR {code}\n\n\n\n\n")
        function_start_line = 0

        # Recover by adding a final bracket
        code = formal_specification_code + "\n" + code
        code += "\n}"

    return code
