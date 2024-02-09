"""Module to check the number of tokens in a prompt."""
import tiktoken

def num_tokens_from_string(string: str, encoding_name: str) -> int:
    """Get the number of tokens from a string
    Args:
        string: The string to get the number of tokens from
        encoding_name: The encoding name to use
    Returns:
        The number of tokens in the string"""
    encoding = tiktoken.encoding_for_model(encoding_name)
    num_tokens = len(encoding.encode(string))
    return num_tokens
