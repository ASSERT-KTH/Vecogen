""" This module contains the function that makes a request to an OpenAI API"""
from openai import OpenAI
from LLM.prompts import seperate_prompt

def make_gpt_request(args, prompt):
    """Make a request to the OpenAI API
    Args:
        args: The arguments given to the program
        prompt: The prompt to send to the OpenAI API
    Returns:
        The response from the OpenAI API"""

    # Create the openAI client
    client = OpenAI()

    # Seperate the prompt into the assistant and user prompt
    assistant_prompt, user_prompt = seperate_prompt(prompt)

    # Parameters for the request
    message=[{"role": "assistant", "content": assistant_prompt}, 
             {"role": "user", "content": user_prompt}]
    temperature=args.temperature
    max_tokens=args.max_tokens
    frequency_penalty=0.0

    # Make the request
    response = client.chat.completions.create(
        model= args.model_name,
        messages = message,
        temperature=temperature,
        max_tokens=max_tokens,
        frequency_penalty=frequency_penalty
    )

    # Return the response
    return response.choices[0].message.content
