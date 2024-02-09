import os
from LLM.prompts import initial_prompt, verification_error_prompt
from GPT.make_GPT_requests import make_gpt_request
from helper_files.list_files import get_absolute_path
from Verify_files.check_file import check_file

## Function that iteratively generates a prompt based on a verification error message
# @param args The arguments given to the program
def generate_code(args):
    header_file = args.header_file
    
    # Generate the initial prompt and check its size
    prompt = initial_prompt(header_file, args.model_name, args.max_tokens)

    # Put the prompt into a file for debugging
    with open("prompt.txt", "w") as f:
        f.write(prompt)
        f.write("\n" * 10)

    # Boolean that indicates if the code has been verified
    verified = False

    # Loop that iteratively prompts and checks the code
    i = 0
    while (i < args.iterations and not verified):
        print("-" * 50)
        print(f"Iteration {i+1} of {args.iterations}, generating code...")
        print("-" * 50)

        # Get the output from the GPT-3.5 model
        response_gpt = make_gpt_request(args, prompt)

        # Get the code in triple backticks
        code = response_gpt.split("```")[1]
        
        # Remove everything before the first newline
        code = code.split("\n", 1)[1]

        # Get the output papth
        output_path = get_absolute_path(args.output_path + "/tmp.c")

        # Output the code to tmp.c
        with open(output_path, "w") as f:
            f.write(code)

        print(f"Code has been generated, verifying...")

        # Verify the code
        args.c_file = output_path

        # Check the file
        verified, output = check_file(args)

        # Create a new prompt based on the output
        prompt = verification_error_prompt(header_file, code, output, args.model_name, args.max_tokens)
        with open("prompt.txt", "a") as f:
            f.write(prompt)
            f.write("\n" * 5)

        i += 1
        
__all__ = ["generate_code"]