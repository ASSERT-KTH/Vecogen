from openai import OpenAI
from LLM.prompts import seperate_prompt
from helper_files.list_files import list_files_directory

## Function that makes a request to the GPT-3.5 Turbo API
def make_gpt_request(args, prompt):
    # Create the openAI client
    client = OpenAI()
    
    # Seperate the prompt into the assistant and user prompt
    assistant_prompt, user_prompt = seperate_prompt(prompt)
    
    # Parameters for the request
    message=[{"role": "assistant", "content": assistant_prompt}, {"role": "user", "content": user_prompt}]
    temperature=args.temperature
    max_tokens=args.max_tokens
    frequency_penalty=0.0
    
    # Make the request
    response = client.chat.completions.create(
        model="gpt-3.5-turbo",
        messages = message,
        temperature=temperature,
        max_tokens=max_tokens,
        frequency_penalty=frequency_penalty
    )
    # Return the response
    return response.choices[0].message.content