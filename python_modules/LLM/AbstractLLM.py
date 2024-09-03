
from abc import ABC, abstractmethod

class LLM(ABC):
    @abstractmethod
    def make_request(self, prompt, n):
        pass
    def num_tokens_from_string(self, string, encoding_name):
        pass