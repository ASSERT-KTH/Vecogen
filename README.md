A project that uses Large Language Models (LLMs) to generate formally verified code. The input are formal specifications, it then uses LLMs to generate the code that will be used. The code is then verified using formal methods to ensure that it meets the specifications. The project is still in its early stages and is not yet functional. 

## Pre-requisites
- Python 3.6 or higher
- Frama-c (https://frama-c.com/)
- Why3 (https://why3.lri.fr/)

# Solvers 
- alt-ergo (https://alt-ergo.lri.fr/)
- CVC4 (https://cvc4.github.io/)
- Z3  


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
- 'verify_dir'      : Verifies the first .c and .h file in the given directory using -d
- 'verify'          : Verifies the given .c and .h file 
- 'list_dir'        : Lists the files given in a directory
- 'generate_prompt' : Generates a prompt for the user to given an .h file

## TODO:
- Automatically detect solvers
