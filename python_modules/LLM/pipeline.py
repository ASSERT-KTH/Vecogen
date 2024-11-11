""" This module contains the function that iteratively generates a prompt based on a 
    verification error message """
import os
import json
from LLM.create_prompt import create_prompt
from LLM.code_generation_objects import IterationInformation, CompletionInformation, CodeGenerationProcess
from Verify_files.check_file import check_file
from testing.test_function import test_generated_code
from helper_files.list_files import list_folders_directory, list_files_directory
from helper_files.specification import add_specifications_to_code
from helper_files.output_file import output_results
from helper_files.verify_input import require_problem_specification

def generate_code_process(args):
    """Function to iteratively generate code and check it
    Returns:
        code_generation_process: The code generation process
    Args:
        args: The arguments given to the program
        print_information_iteration: Boolean that indicates if the information\
        about the iteration should be printed
    """

    # Create a code generation process object
    code_generation_process = CodeGenerationProcess(args)

    # Perform the initial code generation step
    initial_code_generation_information = initial_code_generation_step(args)

    # Add the initial code generation information to the code generation process
    code_generation_process.add_initial_code_generation_information(initial_code_generation_information)

    verified = initial_code_generation_information.is_verified

    # Print information about the initial code generation
    print(f"After the initial code generation step:\n Verified: {verified}, proved goals: {initial_code_generation_information.best_attempt_metric_percentage}")

    # Create an index for the code improvement iterations
    i = 0
    last_iteration = initial_code_generation_information

    # Do the code improvement steps until the code is verified or the maximum iterations are reached
    while (i < args.iterations and not verified):
        print("-" * 100)
        print(f"Code improvement iteration {i + 1} of {args.iterations}.")
        print("-" * 100)

         # Take the best attempt from the initial generation attempts
        code = last_iteration.best_attempt_code
        output = last_iteration.best_attempt_feedback

        # Perform the code improvement step
        code_improvement_information = code_improvement_step(args, i + 1, code, output)

        # Add the code improvement information to the code generation process
        code_generation_process.add_code_improvement_information(code_improvement_information)

        # Stop if the code is verified
        verified = code_improvement_information.is_verified

        # Update the last iteration and the counter
        last_iteration = code_improvement_information
        i += 1

    # Print the results
    print(f"Total completions used: {code_generation_process.total_completions_used}, total tokens used: {code_generation_process.total_tokens_used}, total effective requested: {code_generation_process.total_completions_requested}")
    print(f"Verified: {verified}")
    if args.debug:
        print("Results:")
        for result in code_generation_process.code_improvement_information:
            print(result)

    # save the results to a file
    output_results(args, code_generation_process.to_dict())
    return code_generation_process

# Function that processes the generated code by adding the specification and creating the output file
def add_specification_and_output_code(args, code):
    """Function to process the generated code and write it to a file
    Args:
        args: The arguments given to the program
        code: The code that has been generated
    Returns:
        None
    """

    # Ensure that the code has triple backticks
    if "```C" not in code:
        raise ValueError(f"Attempting to add the specification to the code. The code does not contain triple backticks. Code: {code}")

    # Get the code from the output of the LLM
    code = code.split("```C")[1]
    code = code.split("```")[0]

    # Remove everything before the first newline, the function signature
    code = code.split("\n", 1)[1]

    # Add the specification
    code = add_specifications_to_code(args.absolute_formal_specification_path, args.absolute_natural_language_specification_path, args.absolute_function_signature_path, code)

    # Output the code to the specified file
    print(f"Writing the code to the file {args.absolute_output_directory}/{args.output_file_name}")
    with open(args.absolute_output_directory + "/" + args.output_file_name, "w",
                encoding="utf-8") as f:
        args.absolute_c_path = args.absolute_output_directory + "/" + args.output_file_name
        f.write(code)

    if args.debug:
        print(f"Code generated. Written to {args.absolute_output_directory}/{args.output_file_name}")

    return code

# Function that generates code in a folder
def generate_code_folder(args):
    """Function to generate code from a folder with folders
    Args:
        args: The arguments given to the program
    Returns:
        None
    Requirements of the arguments:
    - The output path is absolute"""

    # Get the folders in the directory
    folders = list_folders_directory(args.directory)

    # Get the base directory of the output
    base_directory = args.absolute_output_directory

    # Sort the folders based on the number
    folders.sort(key=lambda x: int(x.split('-')[0]))

    # Filter the folders if needed
    folders = [f for f in folders if int(f.split('-')[0]) < 932]

    # filter folders based on the number
    # folders = ["0"]

    # Filter the folders based on if it the specific specification file is present
    folders = list(folders)

    # Save the file names of the specifications
    natural_language_file_name = args.natural_language_specification
    formal_specification_file_name = args.formal_specification_file
    function_signature_file_name = args.function_signature

    # filter the folders that have the formalspecification
    folders = [f for f in folders if os.path.exists(args.directory + "/" + f + "/" + formal_specification_file_name)]

    # filter the folders that have the function signature
    folders = [f for f in folders if os.path.exists(args.directory + "/" + f + "/" + function_signature_file_name)]

    # If natural language is included in the arguments, then filter the folders that have the natural language specification
    if args.natural_language_specification:
        folders = [f for f in folders if os.path.exists(args.directory + "/" + f + "/" + natural_language_file_name)]
 
    # For each folder in the directory
    for folder in folders:
        # Set the input and output files
        args.natural_language_specification = args.directory + "/" + folder + "/" + natural_language_file_name
        args.formal_specification_file = args.directory + "/" + folder + "/" + formal_specification_file_name
        args.function_signature = args.directory + "/" + folder + "/" + function_signature_file_name

        # Set the output path
        try:
            if not args.output_file_name:
                args.output_file = f"output_{args.model_name}.c"
        except AttributeError:
            print("No output file specified, using default output file name")
        args.absolute_output_directory = base_directory + "/" + folder

        # Verify that the input and output is set correctly
        require_problem_specification(args)

        # Create the output directory if it does not exist yet
        if not os.path.exists(args.absolute_output_directory):
            os.mkdir(args.absolute_output_directory)

        # Run the code without printing the information
        generate_code_process(args)

        # Print the current generated file
        print("\n \n" + "-" * 100 + "\n \n")
        print(f"Generated code for folder {folder}.")

# Function that verifies and tests the code that has been generated
def verify_and_test_code_attempt(args, response_gpt, i):
    """ 
    Function to verify and test the code that has been generated
    Args:
        args: The arguments given to the program
        response_gpt: The response from the GPT model
        i: The iteration number
    Returns:
        code: The code that has been generated
        verified: Boolean that indicates if the code is verified
        output: The output of the verification process
        verified_goals: The proportion of goals that have been verified
        test_information: The information about the tests
        verification_time_taken: The time taken to verify the code
    """

    # Process the generated code by adding the specification
    try:
        code = add_specification_and_output_code(args, response_gpt)
    except Exception as e:
        if args.debug:
            print(f"Error: Could not add the specification to the code, error: {e}")
        return response_gpt, False, "Could not add specification to code", "0 / 0", {
            "summary": {
                "passed": 0,
                "failed": 0,
                "total": 0,
                "information": f"Error with GPT response, could not add specification. Error: {e}"
            }
        }, 0

    # If no loops are allowed and the code contains a loop, then automatically fail the verification
    if not args.allowloops and ("for" in response_gpt or "while" in response_gpt):
        return code, False, "The code contains a loop, but loops are not allowed", "0 / 0", {
            "summary": {
                "passed": 0,
                "failed": 0,
                "total": 0,
                "information": "Loops are not allowed, but the code contains a loop"
            }
        }, 0 

    # Verify the code
    verified, output, verified_goals, verification_time_taken = check_file(args.absolute_c_path,
        args)

    # If debugging is true, then print the time it took to verify the code
    if args.debug:
        print(f"Verification time taken: {verification_time_taken}")

    # If the compilation failed, then return the information
    if not verified and verified_goals is None:
        test_information = {
            "summary": {
                "passed": 0,
                "failed": 0,
                "total": 0,
                "information": "Compilation failed"
            }
        }

        return code, verified, output, "0 / 0", test_information, verification_time_taken

    # See if the folder of the absolute c path has a tests file
    files_directory = list_files_directory(os.path.dirname(args.absolute_formal_specification_path))

    # Check if the tests file exists
    if "tests.c" in files_directory:
        # Get the path to the tests file
        path_tests = os.path.dirname(args.absolute_formal_specification_path) + "/tests.c"
        passed_tests, total_tests, test_information =  \
            test_generated_code(args.absolute_c_path, path_tests,
                "temp_test_file", args.temp_folder, args.debug)
    else:
        test_information = {
            "summary": {
                "passed": 0,
                "failed": 0,
                "total": 0,
                "information": "No tests found in the folder"
            }
        }
        passed_tests, total_tests = 0, 0
        if args.debug:
            print(f"No tests found, proved goals: {verified_goals}")   
    print(f"Verified goals: {verified_goals}, tests: {passed_tests} / {total_tests}")

    return code, verified, output, verified_goals, test_information, verification_time_taken

# Function for initial code generation
def initial_code_generation_step(args):
    """Function to generate the initial code based on the arguments
    Args:
        args: The arguments given to the program
    Returns:
        responses_gpt: The responses from the LLM
        tokens_used: The amount of tokens used for each response
        model_used: The model used, no list is used as only one model is used
    """

    # Information related to the iterations
    iteration_info = IterationInformation(0, args.initial_examples_generated, args.model_name)

    # Get the output path
    prompt = create_prompt(args)

    # generate the initial attempts by making prompts of at most x each
    responses_llm, tokens_used, models_used = prompt_using_max_n_samples(args, prompt, 10000)

    # For each response, check the code. Stop if the code is verified
    # use enumerate
    for llm_response_index, response_llm in enumerate(responses_llm):
        print("-" * 50)
        print(f"Initial code generation, code completion {llm_response_index + 1} of {len(responses_llm)}.")
        print("-" * 50)

        # Get the generated code and tokens used
        response = response_llm.message.content

        # Process the generated code and get information about the completion
        completion_information = process_code_and_get_completion_information(args, response, 0, prompt, tokens_used[llm_response_index], models_used[llm_response_index])

        # Add the completion to the iteration information
        iteration_info.add_completion(completion_information)

        # If the code is verified, then stop
        if completion_information.is_verified:
            break
    
    return iteration_info

# Function that performs one iteration of code improvement
def code_improvement_step(args, code_improvement_iteration, code, output):
    """Function to do one iteration of code improvement based on an existing file and and the verification error
    Args:
        args: The arguments given to the program
    Returns:
        verified: Boolean that indicates if the code is verified
        output: The output of the verification process
        prompt: The prompt as a string
    """

    # Create an iteration object that contains information about the code improvement iteration
    iteration_info = IterationInformation(code_improvement_iteration, args.initial_examples_generated, args.model_name)

    # Get the output path
    prompt = create_prompt(args, code, output)

    # generate the initial attempts by making prompts of at most x each
    responses_llm, tokens_used, models_used = prompt_using_max_n_samples(args, prompt, 10000)

    # For each response, check the code. Stop if the code is verified
    # use enumerate
    for llm_response_index, response_llm in enumerate(responses_llm):
        print("-" * 50)
        print(f"Code Improvement Iteration {code_improvement_iteration}, code completion {llm_response_index + 1} of {len(responses_llm)}.")
        print("-" * 50)

        # Get the generated code and tokens used
        response = response_llm.message.content

        # Process the generated code and get information about the completion
        completion_information = process_code_and_get_completion_information(args, response, code_improvement_iteration, prompt, tokens_used[llm_response_index], models_used[llm_response_index])

        # Add the completion to the iteration information
        iteration_info.add_completion(completion_information)

        # If the code is verified, then stop
        if completion_information.is_verified:
            break

    return iteration_info

# Function that uses the LLM to generate code, whilst only asking for N exmaples at a time
def prompt_using_max_n_samples(args, prompt, n):
    """Function to generate code using the pipeline and the LLM model
    Args:
        args: The arguments given to the program
        prompt: The prompt to use
    Returns:
        responses_LLM: The responses from the LLM
        tokens_used: The amount of tokens used for each response
        model_used: The model used, no list is used as only one model is used
    """

    # generate the initial attempts by making prompts of at most x each
    responses_llm = []
    tokens_used = []
    i_examples_generated = 0

    # Make LLM requests with at most n examples at a time
    while i_examples_generated < args.initial_examples_generated:
        # Calculate the amount of examples to generate
        n = min(n, args.initial_examples_generated - i_examples_generated)

        # Call the function to make the LLM request
        response_gpt, tokens_used_call, model_used = args.model.make_request(prompt, n)

        # Add the tokens used to the list
        # Only the first iteration has the tokens used
        tokens_used_initial_n_examples = [0] * (n - 1)
        tokens_used_initial_n_examples.insert(0, tokens_used_call)

        # Add the tokens used and the responses to the list
        tokens_used.extend(tokens_used_initial_n_examples)
        responses_llm.extend(response_gpt)

        # Increase the counter
        i_examples_generated += n

    return responses_llm, tokens_used, model_used

# Function that processes the code, and gets iteration information, and verifies the goals
def process_code_and_get_completion_information(args, response_gpt, i, prompt,
            tokens_used, model_used, initial_attempt = False, rebooting = False):
    """Function to process the generated code and get iteration information
    Args:
        args: The arguments given to the program
        response_gpt: The response from the GPT model
        i: The iteration number
        prompt: The prompt that has been used
        tokens_used: The amount of tokens used
        initial_attempt: Boolean that indicates if this is the initial attempt
        rebooting: Boolean that indicates if the code has been rebooted
    Returns:
        completion_information: The information about the completion
    """

    # Process the generated code
    code, verified, verification_output, verified_goals, test_information, verification_time_taken = \
        verify_and_test_code_attempt(args, response_gpt, i)

     # Add extra information about the generation attempt
    if initial_attempt:
        information = "Initial code generation attempt"
    elif rebooting:
        information = "The code was rebooted"
    elif verified:
        information = "The code has been verified"
    else:
        information = "The code has been improved"

    # Create an object that will contain information about the completion
    completion_information = CompletionInformation(i, prompt, response_gpt,  verified,
        verified_goals, test_information, args.temperature,information, args.max_tokens,
        tokens_used, model_used, code, verification_output, verification_time_taken)

    return completion_information
