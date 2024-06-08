""" This module contains the function that iteratively generates a prompt based on a 
    verification error message """
import os
import json
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
        print_information_iteration: Boolean that indicates if the information about the iteration should be printed
    """

    # Total completions, total tokens used, and total effective completions
    total_completions = 0
    total_tokens_used = 0
    total_effective_completions = 0

    # Create an array to store the information about the iterations
    information_iteration = []
    initial_generation_attempts = []

    # Boolean that indicates if the code has been verified
    verified = False

    # Check if the model continues the code or starts from scratch
    if improve:
        prompt, output, verified = improve_code_prompt(args)
    else:
        prompt = initial_prompt(args.header_file, args.model_name, args.max_tokens, args.allowloops)

    # generate the initial attempts by making prompts of at most x each
    responses_gpt, tokens_used, model_used = prompt_using_max_n_examples(args, prompt, 10000)
    total_completions += len(responses_gpt)
    total_tokens_used += sum(tokens_used)

    # For each response, check the code. Stop if the code is verified
    for i in range(args.initial_examples_generated):
        print("-" * 50)
        print(f"Iteration {i+1} of {args.initial_examples_generated}, initial attempt.")
        print("-" * 50)

        # Get the generated code and tokens used
        response_gpt = responses_gpt[i].message.content

        # Process the generated code
        code, verified, output, verified_goals, iteration_info, passed_percentage = \
            process_code_and_get_iteration_information(args, response_gpt, i, prompt, tokens_used[i], model_used, True)

        # Add extra information about the generation attempt
        information_iteration.append(iteration_info)
        initial_generation_attempts.append([passed_percentage, response_gpt, verified, output])
        total_effective_completions += 1

        # If the code is verified, then break
        if verified:
            break

    # Take the best attempt
    code, verified, output = take_best_attempt(initial_generation_attempts)

    # print the best result
    print(f"Verified: {verified}, proved goals: {verified_goals}")

    # Generate a prompt
    i = args.initial_examples_generated
    i_total = args.initial_examples_generated
    i_reboot = 0

    # If there is an improvement step then get the prompt
    if args.iterations > 0 and not verified:
        prompt = verification_error_prompt(args.header_file, code, output, args.model_name,
                                            args.max_tokens, args.allowloops, args.natural_language_only)

    # Create the initial n initial generation attempts
    while (i < args.initial_examples_generated + args.iterations and not verified):
        if print_information_iteration:
            print("-" * 50)
            print(f"Iteration {i - args.initial_examples_generated + 1} of " +
                f"{args.iterations}, generating {args.initial_examples_generated} fixes...")
            print("-" * 50)

        # Get the output from the LLM
        responses_gpt, tokens_used, model_used = prompt_using_max_n_examples(args, prompt, 10000)
        total_completions += len(responses_gpt)
        total_tokens_used += sum(tokens_used)

        # An array that contains the information about possible attempts for this iteration
        iteration_attempts = []
        for j in range(args.initial_examples_generated):
            response_gpt = responses_gpt[j].message.content

            # Process the generated code
            code, verified, output, verified_goals, iteration_info, passed_percentage = \
                process_code_and_get_iteration_information(args, response_gpt, i_total, prompt, tokens_used[j], model_used, \
                rebooting= args.reboot == i_reboot)

            print(f"iteration {i_total}, verified: {verified}, verified goals: {verified_goals}, passed tests: {passed_percentage}")

            # Add the information to the iteration attempts
            iteration_attempts.append([passed_percentage, response_gpt, verified, output])
            information_iteration.append(iteration_info)
            i_total += 1
            total_effective_completions += 1
            if verified:
                break

        # If the code is verified, then exit the while loop and stop searching for a solution
        if verified:
            break

        # Pick the best attempt
        code, verified, output = take_best_attempt(iteration_attempts)

        # Get the next prompt
        if not verified and i_reboot == args.reboot:
            if args.debug:
                print("Reboot the code generation process.")
            prompt = initial_prompt(args.header_file, args.model_name, args.max_tokens,
                                    args.allowloops)
            i_reboot = 0

        # Check if the code needs to be improved
        elif not verified:
            # Create a new prompt based on the output
            prompt = verification_error_prompt(args.header_file, code, output, args.model_name,
                                            args.max_tokens, args.allowloops, args.natural_language_only)
            i_reboot += 1

        # Increase the counter
        i += 1

    # Add the final information to the last iteration
    information_iteration[-1]["total_completions"] = total_completions
    information_iteration[-1]["total_tokens_used"] = total_tokens_used
    information_iteration[-1]["total_completions_used"] = total_effective_completions

    # Print the results
    print(f"Total completions: {total_completions}, total tokens used: {total_tokens_used}, " +
          f"total effective completions: {total_effective_completions}")
    print(f"Verified: {verified}, proved goals: {verified_goals}")
    if args.debug:
        print("Results:")
        for result in information_iteration:
            print(result)

    # save the results to a file
    with open(f"{args.absolute_output_directory}/results.txt", "w", encoding="utf-8") as f:
        json.dump(information_iteration, f, indent=4)

# Function that processes the generated code by adding the specification and creating the output file
def add_specification_and_output_code(args, code):
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

    # Add the specification
    code = add_specification_to_code(args.formal_specification_path, code)

    # Output the code to the specified file
    with open(args.absolute_output_directory + "/" + args.output_file, "w",
                encoding="utf-8") as f:
        args.absolute_c_file = args.absolute_output_directory + "/" + args.output_file
        f.write(code)

    if args.debug:
        print(f"Code generated. Written to {args.absolute_output_directory}/{args.output_file}")

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
    # folders = [f for f in folders if int(f.split('-')[0])  ]
    # folders = ["0", "86", "124", "139", "237", "301", "376", "379", "427", "757", "834", "932", "976", "1166", "1347"]

    # Filter the folders based on if it the specific specification file is present
    folders = [f for f in folders if args.specification_file_name in list_files_directory(args.directory + "/" + f)]

    # For each folder in the directory
    for folder in folders:        
        # Set the header files
        args.header_file = args.directory + "/" + folder + "/" + args.specification_file_name
        args.formal_specification_path = args.absolute_directory + "/" + folder + "/" +  args.formal_specification_file

        # Set the output path
        if not args.output_file:
            args.output_file = f"output_{args.model_name}.c"
        output_dir = base_directory + "/" + folder
        args.absolute_output_directory = output_dir

        # Set the c file and h file paths
        args.absolute_c_path = args.absolute_output_directory + "/" + args.output_file
        args.absolute_header_path = args.absolute_directory + "/" + folder + \
            "/" + args.specification_file_name

        # Create the output directory if it does not exist yet
        if not os.path.exists(output_dir):
            os.mkdir(output_dir)

        # Run the code without printing the information
        generate_code(args, print_information_iteration = False)

        # Print the current generated file
        print("\n \n" + "-" * 50 + "\n \n")
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
        }
        
        
    # Verify the code
    verified, output, verified_goals = check_file(args.absolute_c_path,
        args.absolute_header_path, args)
    
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
        
        return code, verified, output, "0 / 0", test_information

    # See if the folder of the absolute c path has a tests file
    files_directory = list_files_directory(os.path.dirname(args.absolute_header_path))

    # Check if the tests file exists
    if "tests.c" in files_directory:
        # Get the path to the tests file
        path_tests = os.path.dirname(args.absolute_header_path) + "/tests.c"
        passed_tests, total_tests, test_information =  \
            test_generated_code(args.absolute_c_path, path_tests,
                f"tests_iteration_{i}", args.temp_folder, args.debug)
    else:
        test_information = {
            "summary": {
                "passed": 0,
                "failed": 0,
                "total": 0,
                "information": "No tests found in the folder"
            }
        }
        passed_tests, total_tests = 0, 0, 
        if args.debug:
            print(f"No tests found, proved goals: {verified_goals}")   
    print(f"Verified goals: {verified_goals}, tests: {passed_tests} / {total_tests}")

    return code, verified, output, verified_goals, test_information

# Function that creates a prompt based on existing code
def improve_code_prompt(args):
    """Function to create a prompt based on the verification error
    Args:
        args: The arguments given to the program
    Returns:
        verified: Boolean that indicates if the code is verified
        output: The output of the verification process
        prompt: The prompt as a string
    """

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
                args.model_name, args.max_tokens, args.allowloops, args.natural_language_only)

    return verified, output, prompt

# Function that uses the LLM to generate code, whilst only asking for N exmaples at a time
def prompt_using_max_n_examples(args, prompt, n):
    """Function to generate code using the pipeline and the LLM model
    Args:
        args: The arguments given to the program
        prompt: The prompt to use
    Returns:
        responses_gpt: The responses from the GPT model
        tokens_used: The amount of tokens used for each response
        model_used: The model used, no list is used as only one model is used
    """

    # generate the initial attempts by making prompts of at most x each
    responses_gpt = []
    tokens_used = []
    model_used = []
    i_examples_generated = 0

    # Make GPT requests with at most n examples at a time
    while i_examples_generated < args.initial_examples_generated:
        # Calculate the amount of examples to generate
        n = min(n, args.initial_examples_generated - i_examples_generated)

        # Call the function to make the GPT request
        response_gpt, tokens_used_call, model_used = make_gpt_request(args, prompt, n)

        # Add the tokens used to the list
        # Only the first iteration has the tokens used
        tokens_used_initial_n_examples = [0] * (n - 1)
        tokens_used_initial_n_examples.insert(0, tokens_used_call)

        # Add the tokens used and the responses to the list
        tokens_used.extend(tokens_used_initial_n_examples)
        responses_gpt.extend(response_gpt)

        # Increase the counter
        i_examples_generated += n

    return responses_gpt, tokens_used, model_used

# Function that processes the code, and gets iteration information, and verifies the goals
def process_code_and_get_iteration_information(args, response_gpt, i, prompt, 
            tokens_used, model_used, initial_attempt = False, rebooting = False):
    """Function to process the generated code and get iteration information
    Args:
        args: The arguments given to the program
        response_gpt: The response from the GPT model
        i: The iteration number
        prompt: The prompt that was used
        tokens_used: The amount of tokens used for each response
        model_used: The model used for each response
    Returns:
        code: The code that has been generated
        verified: Boolean that indicates if the code is verified
        output: The output of the verification process
        verified_goals: The proportion of goals that have been verified
        test_information: The information about the tests
        iteration_info: The information about the iteration
        passed_percentage: The percentage of either passed tests (priority) or verified goals
    """

    # Process the generated code
    code, verified, output, verified_goals, test_information = \
        verify_and_test_code_attempt(args, response_gpt, i)

     # Add extra information about the generation attempt
    if initial_attempt:
        information = "initial attempt"
    elif rebooting:
        information = "rebooted"
    elif verified:
        information = "verified"
    else:
        information = "code improved"

    # Create a dict that will contain information about the iteration
    iteration_info = {
        "iteration": i + 1,
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

    # Get the percentage of tests passed if the tests have been run
    # Otherwise use the verified goals
    try:
        if test_information[-1]["summary"]["total"] > 0:
            passed_percentage = test_information[-1]["summary"]["pass_rate"]
        else:
            total_goals = verified_goals.split("/")[1]
            verified_goals = verified_goals.split("/")[0]
            if int(total_goals) == 0:
                passed_percentage = 0
            else:
                passed_percentage = int(verified_goals) / int(total_goals)
    except:
        print("Error: Could not get the percentage of passed tests or verified goals" +
              "Test information: {test_information}, verified goals: {verified_goals})")
        passed_percentage = 0

    return code, verified, output, verified_goals, iteration_info, passed_percentage

# Function that ranks the best attempt according to a passed percentage of test cases
def take_best_attempt(initial_generation_attempts):
    """Function to take the best attempt based on the percentage of passed test cases
    Args:
        initial_generation_attempts: The initial generation attempts
            It is a list of tuples of 4 elements that contain:
            * passed_percentage
            * response_gpt
            * verified
            * output
    Returns:
        code: The code that has been generated
        verified: Boolean that indicates if the code is verified
        output: The output of the verification process
    """

    # Best attempt, start with the first one
    best_attempt = initial_generation_attempts[0]

    # First get if there is a verified attempt
    verified_attempt = any([x[2] for x in initial_generation_attempts])

    # If there is a verified attempt, then return the first one
    if verified_attempt:
        for attempt in initial_generation_attempts:
            if attempt[2]:
                return attempt[1], attempt[2], attempt[3]
    # If there is no verified attempt, then return the one with the most amount of passed tests / goals
    else:
        for attempt in initial_generation_attempts:
            print(attempt, best_attempt)
            if attempt[0] != "0 / 0" and attempt[0] > best_attempt[0]:
                best_attempt = attempt

    # Of this best attempt, get the code and boolean if it is verified or not
    return best_attempt[1], best_attempt[2], best_attempt[3]