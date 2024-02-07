import os
from LLM.prompts import initial_prompt
## Function that iteratively generates a prompt based on a verification error message
# @param args The arguments given to the program
def generate_code(args):
    API_KEY_GPT = os.getenv("API_KEY_GPT")
    header_file = args.header_file
    
    # Generate the initial prompt
    prompt = initial_prompt(header_file)
    print(prompt)
    
    # Loop that iteratively prompts and checks the code
    i = 0
    while (i < args.iterations):
        print("Generating code for iteration", i)
        
__all__ = ["generate_code"]