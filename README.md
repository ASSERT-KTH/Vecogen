Formally verified code generation using Large Language Models (LLMs)

A project that uses LLMs to generate formally verified code. The input are formal specifications, it then uses LLMs to generate the code that will be used. The code is then verified using formal methods to ensure that it meets the specifications. The project is still in its early stages and is not yet functional. 

## Pre-requisites
- Python 3.6 or higher
- Python dependencies listed in requirements.txt (python3 -m pip install -r requirements.txt)
- Frama-c (https://frama-c.com/)
- Why3 (https://why3.lri.fr/)
- Provers in the Why3 platform, i.e. Alt-Ergo, CVC4, and Z3
- .env file in the root directory with a API keys for the used services of OPENAI and GROQ, OPENAI_API_KEY = "..." and GROQ_API_KEY = "..."

# Provers 
- alt-ergo 2.4.3 (https://alt-ergo.lri.fr/)
- CVC4 1.7 (https://cvc4.github.io/)
- Z3 4.8.6  


## Installation
1. Clone the repository
2. Install the required python packages using the following command:
```bash
pip install -r requirements.txt
```
3. Install Frama-c and Why3 using the links provided above.

## Usage
1. Run the following command to generate the code:
```bash
python main.py function
```

# Currently implemented functions
- 'verify'          : Verifies the given C file (-c) using a formal specification (-fsf) file. 
- 'list_dir'        : Lists the files given in a directory, where the directory is described by the -d flag
- 'improve_code_step': Only executes one code improvement step on the given formal specification and program candidate
- 'generate_prompt' : Generates a prompt for the user to given an .h file
- 'generate_code'   : Generates the code for the given .h file using Large Language models. Requires the API key to be set.
- 'generate_code_folder: Recursively generate code for each subfolder in a given directory

# Flags Documentation

## General Flags
### `--function`
- **Description**: Specifies the function to execute (e.g., `list_files`, `verify`).
- **Type**: `str`
- **Default**: Required

### `--debug`
- **Description**: Enables debug mode, providing verbose logging.
- **Type**: `bool`
- **Default**: `False`

### `--clear`
- **Description**: Clears debug files in the specified output path.
- **Type**: `bool`
- **Default**: `False`

## Input/Output Flags
### `--directory`
- **Description**: Path to the directory for file operations.
- **Type**: `str`
- **Default**: `None`

### `--c_file`
- **Description**: Path to the C file to be verified or improved.
- **Type**: `str`
- **Default**: `None`

### `--formal_specification_file`
- **Description**: Path to the formal specification file for verification.
- **Type**: `str`
- **Default**: `None`

### `--output_path`
- **Description**: Path to save output files, such as generated code or verification results.
- **Type**: `str`
- **Default**: `None`

### `--output_file_name`
- **Description**: Name of the output file for generated code.
- **Type**: `str`
- **Default**: `None`

## Code Generation Flags
### `--natural_language_specification`
- **Description**: Natural language description of the task for code generation.
- **Type**: `str`
- **Default**: `None`

### `--function_signature`
- **Description**: Function signature for the code to be generated.
- **Type**: `str`
- **Default**: `None`

### `--specification_type`
- **Description**: Specifies the type of specification for code generation (`natural`, `formal`, or `both`).
- **Type**: `str`
- **Default**: `both`

### `--model_name`
- **Description**: Name of the LLM model to use for code generation (e.g., `gpt-3.5-turbo`).
- **Type**: `str`
- **Default**: `gpt-3.5-turbo`

### `--temperature`
- **Description**: Sampling temperature for the LLM; higher values generate more diverse outputs.
- **Type**: `float`
- **Default**: `1.0`

### `--max_tokens`
- **Description**: Maximum number of tokens to generate in the output.
- **Type**: `int`
- **Default**: `4096`

### `--allowloops`
- **Description**: Enables or disables loops in the generated code.
- **Type**: `bool`
- **Default**: `False`

### `--iterations`
- **Description**: Number of iterations to use for code generation or improvement.
- **Type**: `int`
- **Default**: `10`


## Verification Flags


# Example of usage. Make sure you are in the python_modules directory
python3 main.py generate_code_folder -d ../paper_problems/ -ieg 2 -iter 2 -temp 1 -wpt 5 -o ../output/gpt-4o -output-file generated_code.c -fsf formal-specification.h -nl natural-language-specification.h -sig function-signature.h -pt one-shot -spectype both -model gpt-4o

This generates code for all problems in a folders

## Running the code
1. Clone the docker image
docker pull

2. Create the .env file with the API keys for the services used

3. Run the docker image using the env file
docker run --env-file .env -it 
