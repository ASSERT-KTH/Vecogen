from openai import OpenAI
from LLM.create_prompt import seperate_prompt
from LLM.AbstractLLM import LLM
import tiktoken

class OpenRouterGPT(LLM):
    """
    LLM client that uses OpenRouter's OpenAI-compatible API.

    Args:
        args: your run-time args (must include .model_name and .temperature)
        api_key: OpenRouter API key
        site_url: optional, recommended by OpenRouter for analytics (HTTP-Referer)
        app_name: optional, recommended by OpenRouter for analytics (X-Title)
    """
    def __init__(self, args, api_key, site_url: str | None = None, app_name: str | None = None):
        headers = {}
        if site_url:
            headers["HTTP-Referer"] = site_url
        if app_name:
            headers["X-Title"] = app_name

        self.client = OpenAI(
            base_url="https://openrouter.ai/api/v1",
            api_key=api_key,
            default_headers=headers or None,
        )
        self.args = args

    def make_request(self, prompt, n):
        """Make a request to the OpenRouter API."""
        assistant_prompt, user_prompt = seperate_prompt(prompt)

        messages = [
            {"role": "system", "content": assistant_prompt},
            {"role": "user", "content": user_prompt},
        ]

        response = self.client.chat.completions.create(
            model=self.args.model_name,           # e.g. "anthropic/claude-3.5-sonnet" or "openai/gpt-4o"
            messages=messages,
            temperature=self.args.temperature,
            frequency_penalty=0.0,
            n=n,
        )

        # usage may be missing for some models/providers; handle gracefully
        total_tokens = 0
        try:
            total_tokens = response.usage.total_tokens
        except Exception:
            pass

        return response.choices, total_tokens, response.model

    def num_tokens_from_string(self, string: str, encoding_name: str):
        """Token count helper (best-effort if model not known to tiktoken)."""
        try:
            encoding = tiktoken.encoding_for_model(encoding_name)
        except Exception:
            encoding = tiktoken.get_encoding("cl100k_base")
        return len(encoding.encode(string))
