Formally verified code generation using Large Language Models (LLMs)

A tool that uses formal specification and natural language specifications to generate formally verified C code automatically. The tool uses Large Language Models (LLMs) to generate code based on the given specifications. The generated code is then verified using Frama-c and Why3 to ensure that it satisfies the given formal specification. The tool can also improve existing code by generating code snippets that satisfy the given formal specification. 
```

# Currently implemented functions
- 'verify'          : Verifies the given C file (-c) using a formal specification (-fsf) file. 
- 'list_dir'        : Lists the files given in a directory, where the directory is described by the -d flag
- 'improve_code_step': Only executes one code improvement step on the given formal specification and program candidate
- 'generate_prompt' : Generates a prompt for the user to given an .h file
- 'generate_code'   : Generates the code for the given .h file using Large Language models. Requires the API key to be set.
- 'generate_code_folder: Recursively generate code for each subfolder in a given directory

# Input
The input to the tool are three seperate files that are used to generate the code:
- Formal specification file (-fsf): A file that contains the formal specification of the code that needs to be generated.
- Natural language specification file (-nl): A file that contains the natural language specification of the code that needs to be generated. 
- Function signature file (-sig): A file that contains the function signature of the code that needs to be generated.

VeCoGen combines the specifications in the prompt. The tool allows for deciding whether to include the formal specification, natural language specification, or both in the prompt. The user can specify this using the -spectype flag. The possible values are 'formal', 'natural', and 'both'.

Note that the generate_code_folder function generates code for each folder in a directory. For each of the problems in the subfolders, the tool generates code based on the formal specification, natural language specification, and function signature.

# Example of usage. Make sure you are in the python_modules directory
python3 main.py generate_code_folder -d ../paper_problems/ -ieg 2 -iter 2 -temp 1 -wpt 5 -o ../output/gpt-3.5-turbo -output-file generated_code.c -fsf formal-specification.h -nl natural-language-specification.h -sig function-signature.h -pt one-shot -spectype both -model gpt-3.5-turbo

This generates code for all problems in a folders

# Running the tool
## Running the tool using Docker
1. Clone the docker image
```
docker pull merlijnsevenhuijsen/vecogen
```

2. Create the .env file with the API keys for the services used
```
OPENAI_API_KEY=XXX
GROQ_API_KEY=XXX
```

3. Run the docker image using the env file
```
docker run --env-file .env -it merlijnsevenhuijsen/vecogen
```

4. Go to the python_modules directory
```
cd python_modules
```

5. Run the code generation process
```
python3 main.py generate_code_folder -d ../paper_problems/ -ieg 2 -iter 2 -temp 1 -wpt 5 -o ../output/gpt-3.5-turbo -output-file generated_code.c -fsf formal-specification.h -nl natural-language-specification.h -sig function-signature.h -pt one-shot -spectype both -model gpt-3.5-turbo
```
## Running the tool manually
### Prerequisites
- Python 3.6 or higher
- Python dependencies listed in requirements.txt (python3 -m pip install -r requirements.txt)
- Frama-c (https://frama-c.com/)
- Why3 (https://why3.lri.fr/)
- Provers in the Why3 platform, i.e. Alt-Ergo, CVC4, and Z3


### Provers 
- alt-ergo 2.4.3 (https://alt-ergo.lri.fr/)
- CVC4 1.7 (https://cvc4.github.io/)
- Z3 4.8.6  

### Manual Installation
1. Clone the repository
2. Install the required python packages using the following command:
```bash
pip install -r requirements.txt
```
3. Create an .env file with the API keys for the services used
```
OPENAI_API_KEY=XXX
GROQ_API_KEY=XXX
```
4. Go to the python_modules directory
```
cd python_modules
```

5. Run the code generation process
```
python3 main.py generate_code_folder -d ../paper_problems/ -ieg 2 -iter 2 -temp 1 -wpt 5 -o ../output/gpt-3.5-turbo -output-file generated_code.c -fsf formal-specification.h -nl natural-language-specification.h -sig function-signature.h -pt one-shot -spectype both -model gpt-3.5-turbo
```