""" This module contains the function that iteratively generates a prompt based on a 
    verification error message """
import os
from LLM.prompts import initial_prompt, verification_error_prompt
from LLM.specification import add_specification_to_code
from GPT.make_GPT_requests import make_gpt_request
from helper_files.list_files import list_folders_directory, list_files_directory
from Verify_files.check_file import check_file
from testing.test_function import test_generated_code

def generate_code(args, improve = False, print_information_iteration = True):
    """Function to iteratively generate code and check it
    Args:
        args: The arguments given to the program
        improve: Boolean that indicates if the code is improved
    Returns:
        None
        
    Requirements of the arguments:
    - The output path is absolute
    """

    # Create an array to store the information about the iterations
    information_iteration = []
    initial_generation_attempts = []

    # Boolean that indicates if the code has been verified
    verified = False

    # Check if the model continues the code or starts from scratch
    if improve:
        # Get the code from the c file
        with open(args.c_file, "r", encoding="utf-8") as f:
            code = f.read()

        # Write the c code to the output path
        with open(f"{args.absolute_output_directory}/{args.output_file}", "w",
                encoding="utf-8") as f:
            f.write(code)

        # Verify the file
        verified, output, _ = check_file(args.absolute_c_path, args.absolute_header_path, args)

        # Get the output path
        prompt = verification_error_prompt(args.header_file, code, output, \
                    args.model_name, args.max_tokens, args.allowloops)
    else:
        prompt = initial_prompt(args.header_file, args.model_name, args.max_tokens, args.allowloops)

    # A storage for the initial generation attempts
    
    # generate the initial attempts
    responses_gpt, tokens_used, model_used = make_gpt_request(args, prompt, 
                                                args.initial_examples_generated)
    
    # For each response, check the code
    for i in range(args.initial_examples_generated):
        print("-" * 50)
        print(f"Initial iteration {i+1} of {args.initial_examples_generated}, generating code...")
        print("-" * 50)
            
        code_response = responses_gpt[i].message.content
        
        # Process the generated code
        try:
            code, verified, output, verified_goals, test_information = \
                verify_and_test_code_attempt(args, code_response, i)

        except IndexError:
            print("The code could not be generated, please try again.")
            verified, output, verified_goals = False, "The model did not generate code", "0/0"
            break
    
        # Create a dict that will contain information about the iteration
        iteration_info = {
            "iteration": i,
            "prompt": prompt,
            "gpt_output": response_gpt,
            "verified": verified,
            "verified_goals": verified_goals,
            "test_information": test_information,
            "temperature": args.temperature,
            "info": "initial prompt",
            "max_tokens": args.max_tokens,
            "tokens_used": tokens_used,
            "model": model_used,
        }
        information_iteration.append(iteration_info)
        
        # Get the percentage of verified goals
        total_goals = verified_goals.split("/")[1]
        verified_goals = verified_goals.split("/")[0]
        if int(total_goals) == 0:
            verified_percentage = 0
        else:
            verified_percentage = int(verified_goals) / int(total_goals)
        
        initial_generation_attempts.append([verified_percentage, response_gpt])
        
    # Pick the best initial generation attempt
    best_attempt = max(initial_generation_attempts, key = lambda x: x[0])
    code = best_attempt[0]
    
    # Generate a prompt
    i = 0
    i_reboot = 0
    
    # If there is an improvement step then get the prompt
    if args.iterations > 0:
        prompt = verification_error_prompt(args.header_file, code, output, args.model_name,
                                            args.max_tokens, args.allowloops)
    
    # Create the initial n initial generation attempts
    while (i < args.iterations and not verified):
        if print_information_iteration:
            print("-" * 50)
            print(f"Iteration {i+1} of {args.iterations}, generating code...")
            print("-" * 50)

        # Get the output from the LLM
        response_gpt, tokens_used, model_used = make_gpt_request(args, prompt, 1)
        
        # Take the first response
        response_gpt = response_gpt[0].message.content

        # Process the generated code
        try:
            code, verified, output, verified_goals, test_information = \
                verify_and_test_code_attempt(args, response_gpt, i)

        except IndexError:
            print("The code could not be generated, please try again.")
            verified, output, verified_goals = False, "The model did not generate code", "0/0"
            break

        # Add extra information about the generation attempt
        if i_reboot == 0:
            information = "rebooted"
        elif verified:
            information = "verified"
        else:
            information = "code improved"

        # Create a dict that will contain information about the iteration
        iteration_info = {
            "iteration": i,
            "prompt": prompt,
            "gpt_output": response_gpt,
            "verified": verified,
            "verified_goals": verified_goals,
            "test_information": test_information,
            "temperature": args.temperature,
            "info": information,
            "max_tokens": args.max_tokens,
            "tokens_used": tokens_used,
            "model": model_used,
        }
        information_iteration.append(iteration_info)

        # Check if the code needs to be rebooted
        if not verified and i_reboot == args.reboot:
            if args.debug:
                print("Code has not been verified, rebooting...")
            prompt = initial_prompt(args.header_file, args.model_name, args.max_tokens,
                                    args.allowloops)
            i_reboot = 0

        # Check if the code needs to be improved
        elif not verified:
            # Create a new prompt based on the output
            prompt = verification_error_prompt(args.header_file, code, output, args.model_name,
                                            args.max_tokens, args.allowloops)
            i_reboot += 1

        # Increase the counter
        i += 1

    # Print the results
    print(f"Verified: {verified}, proved goals: {verified_goals}")
    if args.debug:
        print("Results:")
        for result in information_iteration:
            print(result)

    # save the results to a file
    with open(f"{args.absolute_output_directory}/results.txt", "w", encoding="utf-8") as f:
        f.write(str(information_iteration))

# Function that processes the generated code by adding the specification and creating the output file
def process_generated_code(args, code):
    """Function to process the generated code and write it to a file
    Args:
        args: The arguments given to the program
        code: The code that has been generated
    Returns:
        None
    Requirements of the arguments:
    - The output path is absolute"""

    # Get the code from the output of the LLM
    code = code.split("```C")[1]
    code = code.split("```")[0]

    # Remove everything before the first newline, the function signature
    code = code.split("\n", 1)[1]

    if args.debug:
        print(f"Code was generated. Writing it to {args.absolute_output_directory} \
                and then verifying the code \n")

    # Add the specification
    code = add_specification_to_code(args.header_file, code)

    # Output the code to the specified file
    with open(args.absolute_output_directory + "/" + args.output_file, "w",
                encoding="utf-8") as f:
        args.absolute_c_file = args.absolute_output_directory + "/" + args.output_file
        f.write(code)

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

    # For each folder in the directory
    for folder in folders:
        # Get the files in the folder
        files = list_files_directory(args.directory + "/" + folder)

        # Get the first .h file in the folder
        specification_file = [f for f in files if f.endswith(".h")][0]
        args.header_file = folder + "/" + specification_file

        # Set the header file
        args.header_file = args.directory + "/" +  args.header_file

        # Set the output path
        if not args.output_file:
            args.output_file = f"output_{args.model_name}.c"
        output_dir = base_directory + "/" + folder
        args.absolute_output_directory = output_dir

        # Set the c file and h file paths
        args.absolute_c_path = args.absolute_output_directory + "/" + args.output_file
        args.absolute_header_path = args.absolute_output_directory + "/" + specification_file

        # Create the output directory if it does not exist yet
        if not os.path.exists(output_dir):
            os.mkdir(output_dir)

        # Run the code without printing the information
        generate_code(args, print_information_iteration = False)

        # Print the current generated file
        print(f"Generated code for {args.absolute_c_path}.")

    # Get the paths to the header, the C file and the output
    
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
    """
    
    # Process the generated code by adding the specification
    code = process_generated_code(args, response_gpt)

    # Verify the code
    verified, output, verified_goals = check_file(args.absolute_c_path,
        args.absolute_header_path, args)

    # See if the folder of the absolute c path has a tests file
    files_directory = list_files_directory(os.path.dirname(args.absolute_c_path))

    # Check if the tests file exists
    if "tests.c" in files_directory:
        # Get the path to the tests file
        path_tests = os.path.dirname(args.absolute_c_path) + "/tests.c"
        passed_tests, total_tests, test_information =  \
            test_generated_code(args.absolute_c_path, path_tests,
                f"tests_iteration_{i}.json", args.temp_folder, args.debug)
        if args.debug:
            print(f"Tests passed: {passed_tests}/{total_tests}")
    else:
        passed_tests, total_tests, test_information = 0, 0, "No tests found in the folder"
        if args.debug:
            print(f"No tests found, proved goals: {verified_goals}")
            
    return code, verified, output, verified_goals, test_information
__all__ = ["generate_code", "generate_code_folder"]
