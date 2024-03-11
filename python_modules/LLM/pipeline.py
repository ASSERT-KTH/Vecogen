""" This module contains the function that iteratively generates a prompt based on a 
    verification error message """
from LLM.prompts import initial_prompt, verification_error_prompt
from LLM.specification import add_specification_to_code
from GPT.make_GPT_requests import make_gpt_request
from helper_files.list_files import get_absolute_path
from helper_files.debug import debug_to_file
from Verify_files.check_file import check_file

def generate_code(args):
    """Function to iteratively generate code and check it
    Args:
        args: The arguments given to the program
    Returns:
        None"""

    # Get the paths to the header, the C file and the output
    header_file_path = args.header_file
    output_path = get_absolute_path(args.output_path + "/tmp.c")
    args.c_file = output_path

    # Check if the model continues the code or starts from scratch
    if args.improve:
        # Get the code from the c file
        with open(args.c_file, "r", encoding="utf-8") as f:
            code = f.read()

        # Write the c code to the output path
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(code)

        # Verify the file
        verified, output = check_file(args)

        # Get the output path
        prompt = verification_error_prompt(header_file_path, code, output, \
                    args.model_name, args.max_tokens)
    else:
        prompt = initial_prompt(header_file_path, args.model_name, args.max_tokens)

    # Put the prompt into a file for debugging
    if args.debug:
        debug_to_file(args, args.output_path, "prompt", prompt + "\n" * 10)

    # Boolean that indicates if the code has been verified
    verified = False

    # Loop that iteratively prompts and checks the code
    i = 0
    i_reboot = 0
    while (i < args.iterations and not verified):
        print("-" * 50)
        print(f"Iteration {i+1} of {args.iterations}, generating code...")
        print("-" * 50)

        # Get the output from the GPT model
        response_gpt = make_gpt_request(args, prompt)

        # If debug is activated then print the output to the "output_gpt.txt" file
        debug_to_file(args, args.output_path, "output_gpt", response_gpt + "\n" * 10)

        # Get the code in triple backticks
        code = response_gpt.split("```C")[1]
        code = code.split("```")[0]

        # Remove everything before the first newline
        code = code.split("\n", 1)[1]

        # Get the output path
        output_path = get_absolute_path(f"{args.output_path}/{args.output_file}.c")

        # Add the specification
        code = add_specification_to_code(header_file_path, code)

        # Output the code to tmp.c
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(code)
            args.c_file = output_path

        print("Code has been generated, verifying...")

        # Verify the code
        verified, output = check_file(args)

        # Check if the code needs to be rebooted
        if not verified and i_reboot < args.reboot:
            print("Code has not been verified, rebooting...")
            prompt = initial_prompt(header_file_path, args.model_name, args.max_tokens)
            i_reboot = 0
        else :
            # Create a new prompt based on the output
            prompt = verification_error_prompt(header_file_path, code, output, args.model_name,
                                            args.max_tokens)
        debug_to_file(args, args.output_path, "prompt", prompt + "\n" * 10)

        i_reboot += 1
        i += 1

__all__ = ["generate_code"]
