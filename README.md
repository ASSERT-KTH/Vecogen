# Formally Verified Code Generation using Large Language Models (LLMs)

A tool that uses formal specification and natural language specifications to generate formally verified C code automatically. The tool uses Large Language Models (LLMs) to generate code based on the given specifications. The generated code is then verified using Frama-C and Why3 to ensure that it satisfies the given formal specification. The tool can also improve existing code by generating code snippets that satisfy the given formal specification.

## Pre-requisites

- Python 3.6 or higher
- Python dependencies listed in requirements.txt (`python3 -m pip install -r requirements.txt`)
- Frama-C (https://frama-c.com/)
- Why3 (https://why3.lri.fr/)
- Provers in the Why3 platform, i.e. Alt-Ergo, CVC4, and Z3
- `.env` file in the root directory with API keys for OPENAI and GROQ:
  ```
  OPENAI_API_KEY=...
  GROQ_API_KEY=...
  ```

## Provers

- Alt-Ergo 2.4.3 (https://alt-ergo.lri.fr/)
- CVC4 1.7 (https://cvc4.github.io/)
- Z3 4.8.6

## Installation

1. Clone the repository
2. Install the required Python packages:

```bash
pip install -r requirements.txt
```

3. Install Frama-C and Why3 using the links above

## Usage

Run:

```bash
python main.py function
```

## Currently Implemented Functions

- `improve_code_step`: Executes one code improvement step on a given formal specification and program candidate
- `generate_prompt`: Generates a prompt from an `.h` file
- `generate_code`: Generates code using LLMs (requires API keys)
- `generate_code_folder`: Recursively generates code for each subfolder in a directory

## Input

The tool expects three separate files:

- Formal specification file (`-fsf`): contains the formal specification
- Natural language specification file (`-nl`): contains the natural language description
- Function signature file (`-sig`): contains the function signature

VeCoGen combines these specifications in the prompt. The `-spectype` flag controls which specifications are used:

- `formal`
- `natural`
- `both`

`generate_code_folder` processes each subfolder and generates code based on all three inputs.

## Example Usage

Make sure you are in the `python_modules` directory:

```bash
python3 main.py generate_code_folder \
  -d ../paper_problems/ \
  -ieg 2 \
  -iter 2 \
  -temp 1 \
  -wpt 5 \
  -o ../output/gpt-4o \
  --output-file generated_code.c \
  -fsf formal-specification.h \
  -nl natural-language-specification.h \
  -sig function-signature.h \
  -pt one-shot \
  -spectype both \
  -provider openai \
  -model gpt-4o
```

This generates code for all problems in a folder.

## Running the Tool

### Docker

1. Pull the image:

```bash
docker pull merlijnsevenhuijsen/vecogen
```

2. Create `.env`:

```
OPENAI_API_KEY=XXX
GROQ_API_KEY=XXX
```

3. Run:

```bash
docker run --env-file .env -it merlijnsevenhuijsen/vecogen
```

4. Go to:

```bash
cd python_modules
```

5. Run generation:

```bash
python3 main.py generate_code_folder \
  -d ../paper_problems/ \
  -ieg 2 \
  -iter 2 \
  -temp 1 \
  -wpt 5 \
  -o ../output/gpt-4o \
  --output-file generated_code.c \
  -fsf formal-specification.h \
  -nl natural-language-specification.h \
  -sig function-signature.h \
  -pt one-shot \
  -spectype both \
  -provider openai \
  -model gpt-4o
```

### Manual

#### Prerequisites

- Python 3.6+
- requirements.txt
- Frama-C
- Why3
- Alt-Ergo, CVC4, Z3

#### Installation

```bash
pip install -r requirements.txt
```

Create `.env`:

```
OPENAI_API_KEY=XXX
GROQ_API_KEY=XXX
```

Run:

```bash
cd python_modules
```

```bash
python3 main.py generate_code_folder \
  -d ../paper_problems/ \
  -ieg 2 \
  -iter 2 \
  -temp 1 \
  -wpt 5 \
  -o ../output/gpt-4o \
  --output-file generated_code.c \
  -fsf formal-specification.h \
  -nl natural-language-specification.h \
  -sig function-signature.h \
  -pt one-shot \
  -spectype both \
  -provider openai \
  -model gpt-4o
```

## General Flags

### `--function`
- Specifies the function to execute
- Type: `str`

### `--debug`
- Enables verbose logging
- Type: `bool`
- Default: `False`

### `--clear`
- Clears debug files
- Type: `bool`
- Default: `False`

## Input/Output Flags

### `--directory`
- Directory for file operations

### `--c_file`
- C file to verify or improve

### `--formal_specification_file`
- Formal specification file

### `--output_path`
- Output directory

### `--output_file_name`
- Output file name

## Code Generation Flags

### `--natural_language_specification`
- Natural language specification

### `--function_signature`
- Function signature

### `--specification_type`
- `natural`, `formal`, or `both`

### `--model_name`
- LLM model

### `--provider`
- LLM provider: `openai`, `groq`, `llama`, or `openrouter`

### `--temperature`
- Sampling temperature

### `--allowloops`
- Allow loops in generated code

### `--iterations`
- Number of iterations

## Example Commands

```bash
python3 main.py generate_code_folder \
  -d ../paper_problems/ \
  -ieg 10 \
  -iter 10 \
  -temp 1 \
  -wpt 5 \
  -o ../output/llama3.1-8b-10-10-1-one-shot-both \
  --output-file generated_code.c \
  -fsf formal-specification.h \
  -nl natural-language-specification.h \
  -sig function-signature.h \
  -pt one-shot \
  -spectype both \
  -provider llama \
  -model llama3.1-8b
```

```bash
python3 main.py generate_code_folder \
  -d ../journal_problems/ \
  -samples 1 \
  -iter 1 \
  -temp 1 \
  -wpt 10 \
  -o ../output/test-gpt-5-nano \
  -of generated-code.c \
  -fsf formal_specification.h \
  -nl natural_language_specification.h \
  -pt zero-shot \
  -spectype both \
  -provider openai \
  -model gpt-5-nano \
  -wpm real \
  -sig function_signature.c \
  -tc solution_test.c \
  -extra extras.c
```
