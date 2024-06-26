Formally verified code generation using Large Language Models (LLMs)

A project that uses LLMs to generate formally verified code. The input are formal specifications, it then uses LLMs to generate the code that will be used. The code is then verified using formal methods to ensure that it meets the specifications. The project is still in its early stages and is not yet functional. 

## Pre-requisites
- Python 3.6 or higher
- Python dependencies listed in requirements.txt (python3 -m pip install -r requirements.txt)
- Frama-c (https://frama-c.com/)
- Why3 (https://why3.lri.fr/)
- .env file in the root directory with a OPENAI API key, "OPENAI_API_KEY = {key}" 

# Solvers 
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
- 'verify_dir'      : Verifies the first .c and .h file. 
- 'verify'          : Verifies the given .c and .h file. 
- 'list_dir'        : Lists the files given in a directory, where the directory is described by the -d flag
- 'generate_prompt' : Generates a prompt for the user to given an .h file
- 'generate_code"   : Generates the code for the given .h file using Large Language models. Requires the API key to be set.

# Existing flags
- '-c' : The .c file
- '-he': The .h file to verify
- '-fsf': The formal specification header file to use for verification purposes. If not set, then uses header_file instead
- '-d' : The directory
- '-s' : The solvers to be used
- '-p' : The prompt to be used
- '-wpt': The timeout for the wp solvers
- '-wps': The maximum amount of steps for the wp solvers
- '-sd' : The smoke detector option for the solvers. Checks consistency of the solvers
- '-iter': The amount of iterations for the code generation
- '-temp': The temperature for the code generation
- '-mt': The maximum amount of tokens for the code generation
- '-o': The output path for the generated code
- '-debug': The debug option that prints the output of the solvers
- '-model': The model to be used for the code generation
- '-clear': The clear option that clears all debug files
- '-reboot': The amount of iterations before a reboot occurs. A reboot starts from the original prompt.
- '-al': The option to allow loops or not
- '-ieg': The amount of initial examples generated for each problem
- '-sfn': The name of the specification file in the folder. Used for generating code in folders
- '-nl': The option to only use natural language in the prompting. This means that any formal feedback is not used when iterative prompting.
- '-pt': The prompt technique used for the code generation. Options are 'zero-shot' and 'one-shot'. Default is 'zero-shot'

# Example of usages. Make sure you are in the python_modules directory
- python3 main.py verify_folder -d ../no_loop_problems/0
    This command will verify the first .c and .h file in the folder no_loop_problems/0
- python3 main.py verify -c ../no_loop_problems/0/solution.c -he ../no_loop_problems/0/specification.h
    This command will verify the given .c and .h file
- python3 main.py generate_code -he ../no_loop_problems/0/specification.h
    This command will generate the code for the given .h file

python3 main.py generate_code -he ../no_loop_problems/284/specification.h -ieg 5 -temp 0.8  -iter 10 -reboot 5

python3 main.py generate_code -he ../no_loop_problems/301/specification.h -ieg 5 -temp 0.8 -iter 10 -reboot 5 -o ../output/gpt4/301/ -model gpt-4

python3 main.py generate_code_folder -d ../no_loop_problems/ -ieg 1 -iter 1 -temp 1  -reboot 5 -wpt 5 -o ../output/3.5-1-1-1-all -output-file generated_code.c
