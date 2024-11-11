""" This module contains functions for creating a prompt that will prompt an LLM for generating formally verified C code"""

def create_prompt(args, previous_attempt: str = "", previous_attempt_feedback: str = ""):
    # Get the template file
    template_path = "../prompts/prompt_template.txt"

    # Print the template
    with open(template_path, "r", encoding="utf-8") as template:
        prompt_template = template.read()
        
        # Mapping for the replacement
        prompt_replacement_mapping = {
            'INITIAL_MESSAGE' : add_initial_message(args.formal_specification_included, args.natural_language_included),
            'ONE_SHOT_EXAMPLE' : add_one_shot_example(args.prompt_technique, args.natural_language_included, args.formal_specification_included),
            'RULES' : rules(args.allowloops),
            'NATURAL_LANGUAGE_DESCRIPTION' : add_natural_language_specification(args.natural_language_specification, args.natural_language_included),
            'FORMAL_SPECIFICATION' : add_formal_specification(args.formal_specification_file, args.formal_specification_included),
            'FUNCTION_SIGNATURE' : add_signature(args.function_signature),    
            'PREVIOUS_ATTEMPT' : add_previous_attempt_feedback(previous_attempt, args.natural_language_included, args.formal_specification_included, previous_attempt_feedback)
        }
        
        return prompt_template.format(**prompt_replacement_mapping)

# Function that adds the initial message to the prompt
def add_initial_message(formal_specification_included: bool = False, natural_language_included: bool = False):
    initial_message = "You are given a specification in"

    if natural_language_included and formal_specification_included:
        initial_message += " natural language and a formal specification in ACSL"
    elif natural_language_included:
        initial_message += " natural language"
    elif formal_specification_included:
        initial_message += " formal specification"
 
    initial_message += ". You must write a function that adheres to this problem specification, such that the code will be formally verified using Frama-C."

    # Return the initial message
    return initial_message

# Function that adds the formal specification if enabled
def add_formal_specification(formal_specification: str, formal_specification_included: bool = False):
    # If formal specification is not included, return an empty string
    if not formal_specification_included:
        return ""

    # Return the content of the formal specification file
    with open(formal_specification, "r", encoding="utf-8") as formal_spec:
        return formal_spec.read()

# Function to add the signature to the prompt
def add_signature(signature: str):
    with open(signature, "r", encoding="utf-8") as signature_file:
        return signature_file.read()

# Function that adds the natural language specification if enabled
def add_natural_language_specification(natural_language_specification: str, natural_language_included: bool = False):
    # If natural language is not included, return an empty string
    if not natural_language_included:
        return ""

    # Return the content of the natural language specification file
    with open(natural_language_specification, "r", encoding="utf-8") as natural_spec:
        return natural_spec.read()

# Function for employing one-shotting or zero-shotting
def add_one_shot_example(prompt_technique: str, natural_language_included: bool = False, formal_specification_included: bool = False):
    # If zero-shotting is chosen, return an empty string
    if prompt_technique == "zero-shot":
        return ""

    # Read the one-shot example from file
    one_shot_example_path = "../prompts/one_shot_example.txt"

    # Read file and extract parts into dictionary
    with open(one_shot_example_path, "r", encoding="utf-8") as one_shot:
        # Split the one-shot example into three parts
        natural_language_split = one_shot.read().split("---END_NATURAL_LANGUAGE---")
        formal_split = natural_language_split[1].split("---END_FORMAL_SPECIFICATION---")

        # Extract the parts
        natural_language = natural_language_split[0]
        formal_specification = formal_split[0]
        function_example = formal_split[1]

        # build the one-shot information
        one_shot_information = "```C\n"

        # If natural language is included
        if natural_language_included:
            one_shot_information += natural_language[:-1]

        # If formal specification is included
        if formal_specification_included:
            one_shot_information += formal_specification[:-1]

        # Add the function example
        one_shot_information += function_example

        # Close the code block
        one_shot_information += "```"

        # Return the one-shot information, with a pre-pended message talking about the one-shot example
        return "Here is an example of the task:\n" + one_shot_information

# Function that adds rules to the prompt
def rules(allow_loops = False):
    # Define the rules
    rules_array = []

    # Add the rules to the array
    rules_array.append("You must adhere to the following rules:")
    rules_array.append("Do not add an explanation to the code")
    rules_array.append("Only give the output function, do not repeat the specification")

    # If loops are not allowed
    if not allow_loops:
        rules_array.append("Do not make use of any type of loops. That is, no for, while, do-while or recursive loops")

    # Return the rules
    return "\n * ".join(rules_array)

# Function to add the previous attempt to the prompt along with some information about it
def add_previous_attempt_feedback(previous_attempt: str, natural_language_included: bool = False, formal_specification_included: bool = False, previous_attempt_feedback: str = ""):
    # If no previous attempt is given, return an empty string
    if previous_attempt == "":
        return ""

    # If only natural language is included then give a message that the previous attempt did not verify, but no formal specification was given
    if natural_language_included and not formal_specification_included:
        return "The previous code attempt did not verify: \n" + previous_attempt + "Please improve the code such that it formally verifies."

    # If a formal specification is included, then give a message that the previous attempt did not verify
    if formal_specification_included:
        return "The previous code attempt did not verify: \n" + previous_attempt + " The following feedback was given: \n" + previous_attempt_feedback + "Please improve the code such that it formally verifies."

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

def seperate_prompt(prompt):
    """Function to seperate the user and assistant prompt
    Args:
        prompt: The prompt to seperate
    Returns:
        A list with two elements, the first is the user prompt and the second is 
        the assistant prompt"""

    # Split the prompt into the user and assistant prompt
    return prompt.split("-----END_ASSISTANT_INFORMATION-----")
