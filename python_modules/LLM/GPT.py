from openai import OpenAI
from LLM.prompts import seperate_prompt
from LLM.AbstractLLM import LLM
class GPT(LLM):
    def __init__(self, args):
        self.client = OpenAI()
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
        max_tokens=self.args.max_tokens
        frequency_penalty=0.0

        # Make the request
        response = self.client.chat.completions.create(
            model= self.args.model_name,
            messages = message,
            temperature=temperature,
            max_tokens=max_tokens,
            frequency_penalty=frequency_penalty,
            n = n,
        )

        # Return the response
        return response.choices, response.usage.total_tokens, response.model
    
    

