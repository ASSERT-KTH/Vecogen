""" This is the main file for the tool. It contains the main function that is called 
    when the tool is run. It also contains the functions that are called based on the 
    arguments given to the tool. """
import sys
import os
import argparse
from dotenv import load_dotenv
from helper_files.list_files import list_files_directory
from helper_files.verify_input import require_directory_exists, require_c_file, require_solver, require_api_key_gpt, check_output_path_set, ensure_integers,require_model, require_problem_specification, require_output_path
from helper_files.debug import clear_debug
from Verify_files.check_file import check_file
from LLM.pipeline import add_specification_and_output_code, code_improvement_step, generate_code_process, generate_code_folder
from LLM.create_prompt import create_prompt

def list_files(args):
    """List the files in a directory"""
    require_directory_exists(args)
    print(list_files_directory(args.absolute_directory))

def verify(args):
    """Verify a C file and a formal specification file"""
    # Make sure the formal specification and C file are given in the arguments 
    require_problem_specification(args)
    require_solver(args)
    check_output_path_set(args)

    add_specification_and_output_code(args, "```C\nvoid aaa(){\n    return 1;\n}```")

    print(check_file(args.absolute_c_path, args))

def generate_initial_prompt(args):
    """ Generate the initial prompt for the code generation"""
    require_problem_specification(args)
    print(create_prompt(args))

def generate_code(args):
    """ Generate code using the pipeline and the LLM"""
    require_solver(args)
    require_api_key_gpt()
    require_problem_specification(args)
    check_output_path_set(args)
    require_model(args)

    # Set the path of the file that will be generated
    args.absolute_c_path = f"{args.absolute_output_directory}/{args.output_file_name}"

    generate_code_process(args)

    print("The code has been generated and saved to the file: " + args.absolute_c_path + "\n" + "For more information, see results.txt")

def improve_code_step(args):
    """ Improve existing code using the pipeline and the LLM"""
    require_solver(args)
    require_api_key_gpt()
    require_c_file(args)
    require_problem_specification(args)
    check_output_path_set(args)
    require_model(args)

    # Get the code from the c file
    with open(args.absolute_c_path, "r", encoding="utf-8") as f:
        code = f.read()

    # Write the c code to the output path
    with open(f"{args.absolute_output_directory}/{args.output_file_name}", "w",
            encoding="utf-8") as f:
        f.write(code)

    # Verify the file
    verified, output, _, _ = check_file(args.absolute_c_path, args)

    if not verified:
        print("The code is not formally verified, improving the code")
        code_improvement_step(args, 1, code, output)

        print("The code has been improved and saved to the file: " + args.absolute_c_path + ".\n")
    else:
        print("The code is already formally verified")

def generate_folder(args):
    """ Generate code from a folder with folders"""
    require_solver(args)
    require_api_key_gpt()
    require_directory_exists(args)
    require_model(args)
    require_output_path(args)

    # ensure that the output path is absolute
    generate_code_folder(args)

def clear(args):
    """Clears the debugging folders"""
    # Clear the files errors.txt, output_gpt.txt and prompt.txt
    check_output_path_set(args)
    clear_debug(args, args.output_path)

def parse_arguments(functions_list):
    """Parse the arguments given to the tool"""
    # Create argument parser
    parser = argparse.ArgumentParser()

    # Positional mandatory arguments
    parser.add_argument("function", help="The function to call", type=str,
                        choices=functions_list)

    # Arguments related to I/O
    parser.add_argument("-d", "--directory", help="The directory to use for verification of the files.", type=str)
    parser.add_argument("-c", "--c_file", help="The C file to use", type=str)
    parser.add_argument("-fsf", "--formal_specification_file", help="The formal specification file to use for verification purposes.", type=str)
    parser.add_argument('-o', '--output_path', help="The output path to use for the code \
                        generation", type=str)
    parser.add_argument('-output-file', '--output_file_name', help="The output file to use for the \
                        code generation", type=str)
    parser.add_argument("-tmp", "--temp_folder", help="The folder where temporary files are stored", default= os.path.join(os.getcwd(), "..", "tmp"), type=str)
    parser.add_argument("-fs", "--formal_specification", help="A boolean whether a formal specification is included in the generation. Note that the tool needs a formal specification to verify the code, but you can choose not to include it in other parts of the generation process.", default=True, action=argparse.BooleanOptionalAction, type=bool)
    parser.add_argument("-nl", "--natural_language_specification", help="The natural language specification to use for the code generation.", type=str)
    parser.add_argument("-sig", "--function_signature", help="The function signature to use for the code generation", type=str)
    parser.add_argument("-spectype", "--specification_type", help="The type of specification to use for the code generation", type=str, choices=["natural", "formal", "both"], default="both")

    # Arguments for Debugging
    parser.add_argument('-debug', '--debug', help="The debug mode, outputs more information \
                        to the console", type=bool, action=argparse.BooleanOptionalAction, \
                        default=False)
    parser.add_argument('-clear', '--clear', help="Clears the debugging folders",
                        default=False, action=argparse.BooleanOptionalAction, type=bool)

    # Verification arguments
    parser.add_argument("-wpt", "--wp_timeout", help="The timeout to use for the wp-prover",
                        type=int, default=2)
    parser.add_argument("-wps", "--wp_steps", help="The steps to use for the wp-prover",
                        type=int, default=1500000)
    parser.add_argument("-s", "--solver", help="The solver to use for the formal verification",
                        type=str)
    parser.add_argument("-sd", "--smoke_detector", help="The smoke detector to use for the \
                        formal verification", type=bool, action=argparse.BooleanOptionalAction,
                        default=True)

    # Tool arguments
    parser.add_argument("-iter", "--iterations", help="The number of iterations to use for \
                        the code generation", type=int, default=10)
    parser.add_argument('-temp', '--temperature', help="The temperature to use for the code \
                        generation", type=float, default=1)
    parser.add_argument('-mt', '--max_tokens', help="The maximum tokens to use for the code \
                        generation", type=int, default=4096)
    parser.add_argument('-model', '--model_name', help="The model name to use for the \
                        code generation", type=str, default="gpt-3.5-turbo")
    parser.add_argument('-reboot', '--reboot', help="Set the amount of iterations before a \
                        reboot occurs", default= 999999, type=int)
    parser.add_argument("-al", "--allowloops", help="Allow loops in the generated code",
                        default=False, action=argparse.BooleanOptionalAction, type=bool)
    parser.add_argument("-ieg", "--initial_examples_generated", help="The amount of initial examples that are generated for each problem", default=10, type=int)
    parser.add_argument("-pt", "--prompt_technique", help="Define the prompt technique used. Currently zero-shot and one-shot are supported.", default="one-shot", type=str, choices=["zero-shot", "one-shot"])

    # Print the version of the tool
    parser.add_argument("--version", action="version", version='%(prog)s - Version 1.1')

    # Parse arguments
    return parser.parse_args()

# Main function
if __name__ == "__main__":
    # Dictionary that maps the function to the function to call
    switcher = {
        "list_files": list_files,
        "verify": verify,
        "generate_prompt": generate_initial_prompt,
        "generate_code": generate_code,
        "improve_code_step": improve_code_step,
        "generate_code_folder": generate_folder
    }

    # Load the environment variables
    load_dotenv()

    # Get a list of the functions
    arguments = parse_arguments(list(switcher.keys()))

    # Ensure that the integers are valid
    ensure_integers(arguments)

    # Clear the debugging folders if the clear argument is given
    if arguments.clear:
        clear(arguments)

    # Get the function from switcher dictionary
    switcher.get(arguments.function, lambda: "Invalid function")(arguments)
