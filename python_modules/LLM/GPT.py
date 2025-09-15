from openai import OpenAI
from LLM.create_prompt import seperate_prompt
from LLM.AbstractLLM import LLM
import tiktoken
class GPT(LLM):
    def __init__(self, args, api_key):
        self.client = OpenAI(api_key=api_key)
        self.args = args

    # Get response from GPT
    def make_request(self, prompt, n):
        """Make a request to the OpenAI API
        Args:
            args: The arguments given to the program
            prompt: The prompt to send to the OpenAI API
            n: The number of completions to generate
        Returns:
            The response from the OpenAI API
            The amount of tokens used in the request
            The exact model used in the request"""
        # Seperate the prompt into the assistant and user prompt
        assistant_prompt, user_prompt = seperate_prompt(prompt)

        message=[{"role": "system", "content": assistant_prompt},
                {"role": "user", "content": user_prompt}]
        temperature=self.args.temperature
        frequency_penalty=0.0

        # Make the request
        response = self.client.chat.completions.create(
            model= self.args.model_name,
            messages = message,
            temperature=temperature,
            frequency_penalty=frequency_penalty,
            n = n,
        )

        # Return the response
        return response.choices, response.usage.total_tokens, response.model

    # Count the number of tokens in a prompt
    def num_tokens_from_string(self, string: str, encoding_name: str):
        """Count the number of tokens in a prompt
        Args:
            prompt: The prompt to count the tokens in
        Returns:
            The number of tokens in the prompt"""
        encoding = tiktoken.encoding_for_model(encoding_name)
        num_tokens = len(encoding.encode(string))
        return num_tokens
