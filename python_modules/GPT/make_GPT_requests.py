""" This module contains the function that makes a request to an OpenAI API"""
from openai import OpenAI

def make_gpt_request(args, prompt):
    """Make a request to the OpenAI API
    Args:
        args: The arguments given to the program
        prompt: The prompt to send to the OpenAI API
    Returns:
        The response from the OpenAI API"""

    # Create the openAI client
    client = OpenAI()

    # Parameters for the request
    message=[{"role": "user", "content": prompt}]
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

    print(response.choices[0].message.content)

    # Return the response
    return response.choices[0].message.content
