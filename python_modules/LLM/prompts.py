""" This module contains the functions that generate prompts for the OPENAI models"""
import os
from helper_files.analyse_specification import get_functions
from helper_files.change_specification import add_line_in_code

def replace_loops(use_loops):
    """ Function that returns a string based on the use_loops boolean
    Args:
        use_loops: Boolean that indicates if the code should use loops
    Returns:
        A string that indicates if the code should use loops or not"""

    if use_loops:
        return "* Add loop invariants and assertions for loops if these \
                    improve the verification process"
    else:
        return "* Do not make use of any type of loop. That is, no for, while, do-while or recursive loops"

def initial_prompt(absolute_header_file_path, model, max_token_size, use_loop, prompt_technique):
    """Function that generates a prompt based on a header file
    Args:
        header_file_path: The path to the header file
        model: The model to use
        max_token_size: The maximum token size allowed
        use_loop: Boolean that indicates if the code should use loops
    Returns:
        The prompt as a string"""

    # Get the text from the header file
    with open(absolute_header_file_path, "r", encoding="utf-8")  \
            as header_file:
        header_text = header_file.read()

    # Create a string that will include the path of the prompt template
    template_path = "prompts/initial_prompt_template"
    
    # Add the prompting technique, by replacing - to _ and adding the path
    template_path += "_" + prompt_technique.replace("-", "_")
    
    # Add the file extension
    template_path += ".txt"
    
    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..", template_path)

    # Get the template for the prompt
    with open(template_path, "r", encoding="utf-8") as template:
        prompt_template = template.read()
        
    # Get the functions from the header file
    with open(absolute_header_file_path, 'r', encoding='utf-8') as file:
        functions = get_functions(file.readlines())

    # For each function, add a line with "  // TODO: ADD CODE HERE"
    # We iterate backwards to avoid changing the line numbers
    for (line_number, _) in functions[::-1]:
        header_text = add_line_in_code(header_text, line_number + 1,
                                       "  // TODO: ADD CODE HERE\n")

    header_file_name = absolute_header_file_path.split("/")[-1]

    # Mapping that replaces the text in the template
    prompt_replacement_mapping = {
        "HEADER_FILE_TEXT": header_text,
        "HEADER_FILE_NAME": header_file_name,
        "ALLOW_LOOPS": replace_loops(use_loop),
    }
    
    # Apply the map to the template
    prompt_mapped = prompt_template.format(**prompt_replacement_mapping)

    # Make sure that the token size is not too large
    prompt_size = model.num_tokens_from_string(prompt_mapped, model.args.model_name)

    if prompt_size > max_token_size:
        # print everything to a file
        with open("prompt-error.txt", "w", encoding="utf-8") as f:
            f.write(prompt_mapped)
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, " + \
            "the maximum is {max_token_size}")

    return prompt_mapped

def compilation_error_prompt(absolute_header_path, previous_attempt, error_message,
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
    with open(absolute_header_path, "r", encoding="utf-8") \
            as header_file:
        header_text = header_file.read()

    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..", \
                                "prompts/compilation_error_prompt_template.txt")

    # Get the template for the prompt
    with open(template_path, "r", encoding="utf-8") as template:
        prompt_template = template.read()

    header_file_name = absolute_header_path.split("/")[-1]

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
    prompt_size = model.num_tokens_from_string(prompt_mapped, model.args.model_name)
    if prompt_size > max_token_size:
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, \
                        the maximum is {max_token_size}")

    return prompt_mapped

def verification_error_prompt(absolute_header_path, previous_attempt, error_message,
                              model, max_token_size, use_loop, natural_language_only, prompt_technique):
    """Function that generates a prompt based on a verification error message
    Args:
        header_file_path: The path to the header file
        previous_attempt: The previous attempt at the code
        error_message: The error message from the verification
        model: The model to use
        max_token_size: The maximum token size allowed
        natural_language_only: Whether the prompt must be in natural language only. 
            If false it also makes use of the formal specification feedback
    Returns:
        The prompt as a string"""
    
    # Limit the error message to 500 characters
    # error_message = error_message[:800]

    # Get the text from the header file
    with open(absolute_header_path, "r", encoding="utf-8") \
            as header_file:
        header_text = header_file.read()
        
    # Create a string that will include the path of the prompt template
    template_path = "prompts/verification_error_prompt_template"
    
    # Add the prompting technique, by replacing - to _ and adding the path
    template_path += "_" + prompt_technique.replace("-", "_")
    
    # If natural language only is true, add the natural language only path
    if natural_language_only:
        template_path += "_natural_language"
    
    # Add the file extension
    template_path += ".txt"
    
    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..", template_path)
    
    # Get the template for the prompt
    with open(template_path, "r", encoding="utf-8") as template:
        prompt_template = template.read()

    header_file_name = absolute_header_path.split("/")[-1]

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
    prompt_size = model.num_tokens_from_string(prompt_mapped, model.args.model_name)
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