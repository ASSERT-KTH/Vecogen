""" This module contains the functions that generate prompts for the OPENAI models"""
import os
from GPT.check_tokens import num_tokens_from_string
from helper_files.analyse_specification import get_functions
from helper_files.change_specification import add_line_in_code

def replace_loops(use_loops):
    """ Function that returns a string based on the use_loops boolean
    Args:
        use_loops: Boolean that indicates if the code should use loops
    Returns:
        A string that indicates if the code should use loops or not"""

    if use_loops:
        return "for, while, do-while or recursive loops"
    else:
        return "no loops"

def initial_prompt(header_file_path, model, max_token_size, use_loop):
    """Function that generates a prompt based on a header file
    Args:
        header_file_path: The path to the header file
        model: The model to use
        max_token_size: The maximum token size allowed
        use_loop: Boolean that indicates if the code should use loops
    Returns:
        The prompt as a string"""

    # Get the text from the header file
    with open(os.path.join(os.getcwd(), "..", header_file_path), "r", encoding="utf-8")  \
            as header_file:
        header_text = header_file.read()

    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..",  "prompts/initial_prompt_template.txt")

    # Get the template for the prompt
    with open(template_path, "r", encoding="utf-8") as template:
        prompt_template = template.read()

    # Get the functions from the header file
    with open(header_file_path, 'r', encoding='utf-8') as file:
        functions = get_functions(file.readlines())

    # For each function, add a line with "  // TODO: ADD CODE HERE"
    # We iterate backwards to avoid changing the line numbers
    for (line_number, _) in functions[::-1]:
        header_text = add_line_in_code(header_text, line_number + 1,
                                       "  // TODO: ADD CODE HERE\n")

    header_file_name = header_file_path.split("/")[-1]

    # Mapping that replaces the text in the template
    prompt_replacement_mapping = {
        "HEADER_FILE_TEXT": header_text,
        "HEADER_FILE_NAME": header_file_name,
        "ALLOW_LOOPS": replace_loops(use_loop),
    }

    # Apply the map to the template
    prompt_mapped = prompt_template.format(**prompt_replacement_mapping)

    # Make sure that the token size is not too large
    prompt_size = num_tokens_from_string(prompt_mapped, model)
    if prompt_size > max_token_size:
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, \
                        the maximum is {max_token_size}")

    return prompt_mapped

def compilation_error_prompt(header_file_path, previous_attempt, error_message,
                             model, max_token_size, use_loop):
    """Function that generates a prompt based on a compilation error message
    Args:
        header_file_path: The path to the header file
        previous_attempt: The previous attempt at the code
        error_message: The error message from the compilation
        model: The model to use
        max_token_size: The maximum token size allowed
        use_loop: Boolean that indicates if the code should use loops
    Returns:
        The prompt as a string"""

    # Get the text from the header file
    with open(os.path.join(os.getcwd(), "..", header_file_path), "r", encoding="utf-8") \
            as header_file:
        header_text = header_file.read()

    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..", \
                                "prompts/compilation_error_prompt_template.txt")

    # Get the template for the prompt
    with open(template_path, "r", encoding="utf-8") as template:
        prompt_template = template.read()

    header_file_name = header_file_path.split("/")[-1]

    # Mapping that replaces the text in the template
    prompt_replacement_mapping = {
        "HEADER_FILE_TEXT": header_text,
        "CODE_ATTEMPT": previous_attempt,
        "COMPILATION_ERROR_MESSAGE": error_message,
        "HEADER_FILE_NAME": header_file_name,
        "ALLOW_LOOPS": replace_loops(use_loop),
    }

    # Apply the map to the template
    prompt_mapped = prompt_template.format(**prompt_replacement_mapping)

    # Make sure that the token size is not too large
    prompt_size = num_tokens_from_string(prompt_mapped, model)
    if prompt_size > max_token_size:
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, \
                        the maximum is {max_token_size}")

    return prompt_mapped

def verification_error_prompt(header_file_path, previous_attempt, error_message,
                              model, max_token_size, use_loop):
    """Function that generates a prompt based on a verification error message
    Args:
        header_file_path: The path to the header file
        previous_attempt: The previous attempt at the code
        error_message: The error message from the verification
        model: The model to use
        max_token_size: The maximum token size allowed
    Returns:
        The prompt as a string"""

    # Get the text from the header file
    with open(os.path.join(os.getcwd(), "..", header_file_path), "r", encoding="utf-8") \
            as header_file:
        header_text = header_file.read()

    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..",
                                "prompts/verification_error_prompt_template.txt")

    # Get the template for the prompt
    with open(template_path, "r", encoding="utf-8") as template:
        prompt_template = template.read()

    header_file_name = header_file_path.split("/")[-1]

    # Mapping that replaces the text in the template
    prompt_replacement_mapping = {
        "HEADER_FILE_TEXT": header_text,
        "CODE_ATTEMPT": previous_attempt,
        "VERIFICATION_ERROR_MESSAGE": error_message,
        "HEADER_FILE_NAME": header_file_name,
        "ALLOW_LOOPS": replace_loops(use_loop),
    }

    # Apply the map to the template
    prompt_mapped = prompt_template.format(**prompt_replacement_mapping)

    # Make sure that the token size is not too large
    prompt_size = num_tokens_from_string(prompt_mapped, model)
    if prompt_size > max_token_size:
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, \
                        the maximum is {max_token_size}")

    return prompt_mapped

def seperate_prompt(prompt):
    """Function to seperate the user and assistant prompt
    Args:
        prompt: The prompt to seperate
    Returns:
        A list with two elements, the first is the user prompt and the second is 
        the assistant prompt"""

    # Split the prompt into the user and assistant prompt
    return prompt.split("-----END_ASSISTANT_INFORMATION-----")
