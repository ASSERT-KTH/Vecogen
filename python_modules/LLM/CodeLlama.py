import os
import json
import logging
from transformers import AutoTokenizer, AutoModelForCausalLM, BitsAndBytesConfig
import gc
from LLM.prompts import seperate_prompt
from LLM.AbstractLLM import LLM
# Module inspired by https://github.com/ASSERT-KTH/MoKav/blob/feat/codellama/src/chatgpt.py#L80
# This is used to run CodeLama on a GPU
