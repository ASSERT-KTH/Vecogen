import os
from GPT.check_tokens import num_tokens_from_string

## Function that generates an initial prompt (first attempt) with the header file
# @param file path to the header file
# @return the prompt as a string
def initial_prompt(header_file_path, model, max_token_size):
    # Get the text from the header file
    with open(os.path.join(os.getcwd(), "..", header_file_path), "r") as header_file:
        header_text = header_file.read()
        
    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..",  "prompts/initial_prompt_template.txt")
    
    # Get the template for the prompt
    with open(template_path, "r") as template:
        prompt_template = template.read()

    header_file_name = header_file_path.split("/")[-1]
    
    # Mapping that replaces the text in the template
    prompt_replacement_mapping = {
        "HEADER_FILE_TEXT": header_text,
        "HEADER_FILE_NAME": header_file_name
    }
    
    # Apply the map to the template
    prompt_mapped = prompt_template.format(**prompt_replacement_mapping)

    # Make sure that the token size is not too large
    prompt_size = num_tokens_from_string(prompt_mapped, model)
    if prompt_size > max_token_size:
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, \
                        the maximum is {max_token_size}")

    return prompt_mapped
    
## Function that generates a prompt based on an compilation error message
# @param file path to the header file
# @param previous attempt of the code
# @param compilation error_message the error message
# @return the prompt as a string
def compilation_error_prompt(header_file_path, previous_attempt, error_message, model, max_token_size):
    # Get the text from the header file
    with open(os.path.join(os.getcwd(), "..", header_file_path), "r") as header_file:
        header_text = header_file.read()
        
    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..",  "prompts/compilation_error_prompt_template.txt")
    
    # Get the template for the prompt
    with open(template_path, "r") as template:
        prompt_template = template.read()

    header_file_name = header_file_path.split("/")[-1]
    
    # Mapping that replaces the text in the template
    prompt_replacement_mapping = {
        "HEADER_FILE_TEXT": header_text,
        "CODE_ATTEMPT": previous_attempt,
        "COMPILATION_ERROR_MESSAGE": error_message,
        "HEADER_FILE_NAME": header_file_name
    }

    # Apply the map to the template
    prompt_mapped = prompt_template.format(**prompt_replacement_mapping)

    # Make sure that the token size is not too large
    prompt_size = num_tokens_from_string(prompt_mapped, model)
    if prompt_size > max_token_size:
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, \
                        the maximum is {max_token_size}")

    return prompt_mapped

## Function that generates a prompt based on a verification error message
def verification_error_prompt(header_file_path, previous_attempt, error_message, model, max_token_size):
    # Get the text from the header file
    with open(os.path.join(os.getcwd(), "..", header_file_path), "r") as header_file:
        header_text = header_file.read()

    # Get the path to the template
    template_path = os.path.join(os.getcwd(), "..",  "prompts/verification_error_prompt_template.txt")

    # Get the template for the prompt
    with open(template_path, "r") as template:
        prompt_template = template.read()

    header_file_name = header_file_path.split("/")[-1]

    # Mapping that replaces the text in the template
    prompt_replacement_mapping = {
        "HEADER_FILE_TEXT": header_text,
        "CODE_ATTEMPT": previous_attempt,
        "VERIFICATION_ERROR_MESSAGE": error_message,
        "HEADER_FILE_NAME": header_file_name
    }

    # Apply the map to the template
    prompt_mapped = prompt_template.format(**prompt_replacement_mapping)

    # Make sure that the token size is not too large
    prompt_size = num_tokens_from_string(prompt_mapped, model)
    if prompt_size > max_token_size:
        raise ValueError(f"The prompt is too large, it has {prompt_size} tokens, \
                        the maximum is {max_token_size}")

    return prompt_mapped

## Function that seperates the prompt into a user and assistant prompt
# @param prompt the prompt to seperate
# @return the user and assistant prompt
def seperate_prompt(prompt):
    # Split the prompt into the user and assistant prompt
    return prompt.split("-----END_ASSISTANT_INFORMATION-----")