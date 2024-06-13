import os
import json
import logging
import torch
from transformers import AutoTokenizer, AutoModelForCausalLM, BitsAndBytesConfig
import gc
from LLM.prompts import seperate_prompt
from LLM.AbstractLLM import LLM
# Module inspired by https://github.com/ASSERT-KTH/MoKav/blob/feat/codellama/src/chatgpt.py#L80
# This is used to run CodeLama on a GPU
class CodeLlama(LLM):
    def __init__(self, args, model="codellama/CodeLlama-7b-Instruct-hf"):
        # Arguments from Vecogen
        self.cache_file_path = args.temp_folder
        self.args = args
        
        # Attempt to load cache from file
        self.cache = self.load_cache()  # Load cache from file
        self.inst_sep = '[/INST]'
        
        # If quanization is needed, uncomment the following lines
        # quantization_config = BitsAndBytesConfig(
        #     load_in_4bit=True,
        #     bnb_4bit_compute_dtype=torch.float16,
        #     bnb_4bit_use_double_quant=True,
        # )
        
        # Load the model and tokenizer
        self.model = AutoModelForCausalLM.from_pretrained(
            model,
            # quantization_config=quantization_config,
            device_map="cuda",
            cache_dir="./.models",
        )
        self.tokenizer = AutoTokenizer.from_pretrained(
            model, use_fast=True, padding_side="left"
        )

    # Load cache from file
    def load_cache(self):
        if os.path.exists(self.cache_file_path):
            with open(self.cache_file_path, 'r') as f:
                return json.load(f)
        return {}

    # Save cache to file
    def save_cache(self):
        with open(self.cache_file_path, 'w') as f:
            json.dump(self.cache, f)

    # Get response from CodeLlama
    def make_request(self, prompt, n):
        # Seperate the prompt
        assistant_prompt, user_prompt = seperate_prompt(prompt)
        
        message =[  {"role": "system", "content": assistant_prompt},
                    {"role": "user", "content": user_prompt}]

        print("###Messages###\n\n", message)
        logging.info(f"###CHATGPT_INITIAL_PROMPT###\n\n {message}")

        prompt = "\n".join([msg['content'] for msg in message])

        # If the prompt is too long, raise an exception
        if len(prompt) > self.args.max_tokens:            
            raise Exception("Messages are too long!!")
            
        # Check if the prompt is in the cache
        # Since we want different results for the same prompt, we don't want to cache the prompt
        # if prompt in self.cache:
        #     return self.cache[prompt]

        inputs = self.tokenizer.apply_chat_template(message, tokenize=True, return_tensors="pt").to("cuda")
        
        # input_ids = inputs.input_ids.to(self.model.device)
        # attention_mask = inputs.attention_mask.to(self.model.device)

        with torch.no_grad():
            outputs = self.model.generate(
                inputs,
                max_length= self.args.max_tokens,
                temperature= self.args.temperature,
                num_return_sequences= n,
                pad_token_id=self.tokenizer.eos_token_id,
                do_sample=True,
            )
            
        # Clear memory
        torch.cuda.empty_cache()
        gc.collect()
        
        # Get the responses
        responses = [self.tokenizer.decode(
            output, skip_special_tokens=True) for output in outputs]
        
        instruction_responses = [response.split(self.inst_sep, 1)[1] for response in responses]
        self.cache[prompt] = instruction_responses
        self.save_cache()
        
        # Return the first result
        print("###Instruction Responses###\n\n", instruction_responses)
        return instruction_responses[0]