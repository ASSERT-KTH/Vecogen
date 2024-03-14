""" This module contains the function that iteratively generates a prompt based on a 
    verification error message """
import os
from LLM.prompts import initial_prompt, verification_error_prompt
from LLM.specification import add_specification_to_code
from GPT.make_GPT_requests import make_gpt_request
from helper_files.list_files import list_folders_directory, list_files_directory
from Verify_files.check_file import check_file

def generate_code(args, improve = False):
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

    # Boolean that indicates if the code has been verified
    verified = False

    # Loop that iteratively prompts and checks the code
    i = 0
    i_reboot = 0
    while (i < args.iterations and not verified):
        print("-" * 50)
        print(f"Iteration {i+1} of {args.iterations}, generating code...")
        print("-" * 50)

        # Get the output from the LLM
        response_gpt = make_gpt_request(args, prompt)

        # Get the code from the output of the LLM
        code = response_gpt.split("```C")[1]
        code = code.split("```")[0]

        # Remove everything before the first newline, the function signature
        code = code.split("\n", 1)[1]

        if args.debug:
            print(f"Code was generated. Writing it to {args.absolute_output_directory} \
                  and then verifying the code \n")

        # Add the specification
        code = add_specification_to_code(args.header_file, code, improve)

        # Output the code to the specified file
        with open(args.absolute_output_directory + "/" + args.output_file, "w",
                  encoding="utf-8") as f:
            args.absolute_c_file = args.absolute_output_directory + "/" + args.output_file
            f.write(code)

        # Verify the code
        verified, output, verified_goals = check_file(args.absolute_c_path,
            args.absolute_header_path, args)

        # Extra information
        if i == 0:
            information = "initial prompt"
        elif i_reboot == 0:
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
            "info": information,
        }
        information_iteration.append(iteration_info)

        # Check if the code needs to be rebooted
        if not verified and i_reboot == args.reboot:
            if args.debug:
                print("Code has not been verified, rebooting...")
            prompt = initial_prompt(args.header_file, args.model_name, args.max_tokens,
                                    args.allowloops)
            i_reboot = 0
        else :
            # Create a new prompt based on the output
            prompt = verification_error_prompt(args.header_file, code, output, args.model_name,
                                            args.max_tokens, args.allowloops)

        i_reboot += 1
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
    for folder in folders[1:2]:
        # Get the files in the folder
        files = list_files_directory(args.directory + "/" + folder)

        # Get the first .h file in the folder
        specification_file = [f for f in files if f.endswith(".h")][0]
        args.header_file = folder + "/" + specification_file

        # Set the header file
        args.header_file = args.directory + "/" +  args.header_file

        # Set the output path
        args.output_file = "output_gpt3-5.c"
        output_dir = base_directory + "/" + folder
        args.absolute_output_directory = output_dir

        # Set the c file and h file paths
        args.absolute_c_path = args.absolute_output_directory + "/" + args.output_file
        args.absolute_header_path = args.absolute_output_directory + "/" + specification_file

        # Create the output directory if it does not exist yet
        if not os.path.exists(output_dir):
            os.mkdir(output_dir)

        # Run the code
        generate_code(args)

        # Print the current generated file
        print(f"Generated code for {args.absolute_c_path}.")

    # Get the paths to the header, the C file and the output
__all__ = ["generate_code", "generate_code_folder"]
