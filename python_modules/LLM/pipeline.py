import os
from LLM.prompts import initial_prompt
from GPT.make_GPT_requests import make_gpt_request

## Function that iteratively generates a prompt based on a verification error message
# @param args The arguments given to the program
def generate_code(args):
    header_file = args.header_file
    
    # Generate the initial prompt
    prompt = initial_prompt(header_file)
    
    # Loop that iteratively prompts and checks the code
    i = 0
    while (i < args.iterations):
        print(make_gpt_request(args, prompt))
        i += 1
        
__all__ = ["generate_code"]