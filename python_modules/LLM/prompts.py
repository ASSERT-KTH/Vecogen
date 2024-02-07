import os

## Function that generates an initial prompt (first attempt) with the header file
# @param file path to the header file
# @return the prompt as a string
def initial_prompt(header_file_path):
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
    return prompt_template.format(**prompt_replacement_mapping)
    
## Function that generates a prompt based on an compilation error message
# @param file path to the header file
# @param previous attempt of the code
# @param compilation error_message the error message
# @return the prompt as a string
def compilation_error_prompt(header_file_path, previous_attempt, error_message):
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
    return prompt_template.format(**prompt_replacement_mapping)

## Function that generates a prompt based on a verification error message
def verification_error_prompt(header_file_path, previous_attempt, error_message):
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
    return prompt_template.format(**prompt_replacement_mapping)

## Function that seperates the prompt into a user and assistant prompt
# @param prompt the prompt to seperate
# @return the user and assistant prompt
def seperate_prompt(prompt):
    # Split the prompt into the user and assistant prompt
    return prompt.split("-----END_ASSISTANT_INFORMATION-----")