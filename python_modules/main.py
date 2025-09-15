""" This is the main file for the tool. It contains the main function that is called 
    when the tool is run. It also contains the functions that are called based on the 
    arguments given to the tool. """
import sys
import os
import argparse
from dotenv import load_dotenv
from helper_files.verify_input import require_directory_exists, require_c_file, require_solver, check_output_path_set, ensure_integers,require_model, require_problem_specification, require_output_path
from helper_files.debug import clear_debug
from Verify_files.check_file import check_file
from LLM.pipeline import code_improvement_step, generate_code_process, generate_code_folder
from LLM.create_prompt import create_prompt


def _normalize_args(a):
    """Unify legacy names expected by helpers; set absolute paths."""
    # map canonical → legacy
    a.output_path = getattr(a, "output_dir", getattr(a, "output_path", None))
    a.output_file_name = getattr(a, "output_file", getattr(a, "output_file_name", None))
    a.temp_folder = getattr(a, "temp_dir", getattr(a, "temp_folder", None))
    a.tests_path = getattr(a, "tests_file", getattr(a, "tests_file", None))
    a.directory = getattr(a, "input_dir", getattr(a, "directory", None))

    # derive absolutes commonly used by helpers
    if getattr(a, "output_dir", None):
        a.absolute_output_directory = os.path.abspath(a.output_dir)
    if getattr(a, "c_file", None):
        a.absolute_c_path = os.path.abspath(a.c_file)
    if getattr(a, "input_dir", None):
        a.absolute_directory = os.path.abspath(a.input_dir)
    return a

def generate_initial_prompt(args):
    """ Generate the initial prompt for the code generation"""
    require_problem_specification(args)
    print(create_prompt(args))

def generate_code(args):
    """ Generate code using the pipeline and the LLM"""
    require_solver(args)
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

import argparse, os

# Nice help: show defaults + keep raw newlines in examples
class _Fmt(argparse.ArgumentDefaultsHelpFormatter, argparse.RawTextHelpFormatter):
    pass

def parse_arguments(functions_list):
    """Parse CLI arguments for the ACSL-based code-gen & verification tool (VeCoGen-style)."""
    parser = argparse.ArgumentParser(
        description=(
            "Generate C code from specifications and formally verify it.\n"
            "Uses LLMs for code proposals and Frama-C WP/Why3 for proof feedback."
        ),
        formatter_class=_Fmt,
        epilog=(
            "Examples:\n"
            "  # Batch-generate per problem folder, include both specs in the prompt\n"
            "  python3 main.py generate_code_folder \\\n"
            "    --input-dir ../problems --initial-examples 2 --iterations 3 --wp-timeout 5 \\\n"
            "    --output-dir ../out/gpt-4o --output-file generated.c \\\n"
            "    --formal-spec-file formal.h --natural-spec-file natural.h --signature-file sig.h \\\n"
            "    --prompt-technique one-shot --specification-type both --model gpt-4o-mini \\\n"
            "    --tests-file solution.c/\n\n"
            "  # Verify an existing C file against ACSL\n"
            "  python3 main.py verify --c-file foo.c --solver z3 --wp-timeout 10"
        ),
    )

    # Positional
    parser.add_argument(
        "function", metavar="FUNCTION",
        help="Which subcommand/function to run",
        type=str, choices=functions_list,
    )

        # Inputs & specifications
    specs = parser.add_argument_group("Inputs & specifications")
    specs.add_argument("-fsf", "--formal-spec-file", type=str, dest="formal_spec_file",
                       help="Path to ACSL formal specification file ...")
    specs.add_argument("-nl", "--natural-spec-file", type=str, dest="natural_spec_file",
                       help="Path to natural-language specification file ...")
    specs.add_argument("-sig", "--signature-file", type=str, dest="signature_file",
                       help="Path to function signature file ...")
    specs.add_argument("-tc", "--tests-file", type=str, dest="tests_file",
                       help="Path to test cases (file). Used to validate/filter candidates.")
    specs.add_argument("-spectype", "--specification-type",
                       choices=["natural", "formal", "both"], default="both",
                       help="Which specs to include in the LLM prompt")
    specs.add_argument("-extra", "--extra-specs",
                       type=str, dest="extra_specs",
                       help="Additional header file to include in the prompt and generated code (e.g., for structs, imports, etc.)")

    # Project I/O paths
    io = parser.add_argument_group("Project I/O paths")
    io.add_argument("-d", "--input-dir", type=str, dest="input_dir",
                    help="Root directory for batch runs (each subfolder = one problem)")
    io.add_argument("-o", "--output-dir", type=str, dest="output_dir",
                    help="Directory where generated artifacts are written")
    io.add_argument("--output-file", "--output-file-name", "-of", type=str, dest="output_file",
                    help="Filename for the generated C file inside --output-dir")
    io.add_argument("-tmp", "--temp-dir", type=str, dest="temp_dir",
                    default=os.path.join(os.getcwd(), "..", "tmp"),
                    help="Directory for temporary files")

    # ── Generation options ───────────────────────────────────────────────────────
    gen = parser.add_argument_group("Generation")
    gen.add_argument("-iter", "--iterations", help="Max generation-improvement cycles", type=int, default=10)
    gen.add_argument("-temp", "--temperature", help="LLM sampling temperature", type=float, default=1.0)
    gen.add_argument("-model", "--model-name", help="LLM model name", type=str, default="gpt-3.5-turbo")
    gen.add_argument("-reboot", "--reboot", help="Hard reset after this many iterations", type=int, default=999999)
    gen.add_argument(
        "-al", "--allow-loops",
        help="Permit loops in generated code (may hinder WP proofs)",
        action=argparse.BooleanOptionalAction, default=False, dest="allow_loops"
    )
    gen.add_argument(
        "-samples", "--generated-samples",
        help="Number of candidate programs to sample per problem per iteration",
        type=int, default=10, dest="initial_examples"
    )
    gen.add_argument(
        "-pt", "--prompt-technique",
        help="Prompting strategy",
        choices=["zero-shot", "one-shot"], default="one-shot"
    )

    # ── Verification options ────────────────────────────────────────────────────
    ver = parser.add_argument_group("Verification")
    ver.add_argument("-s", "--solver", help="Why3 solver to use (e.g., z3, cvc5, alt-ergo)", type=str)
    ver.add_argument("-wpt", "--wp-timeout", help="Timeout in seconds for Frama-C WP", type=int, default=2)
    ver.add_argument("-wpm", "--wp-model", help="Model/logic profile for WP backend", type=str, default="")
    ver.add_argument(
        "-sd", "--smoke-detector",
        help="Detect inconsistencies in specification and/or implementations. I.e. dead code will not verify",
        action=argparse.BooleanOptionalAction, default=False
    )

    # ── Debugging & housekeeping ────────────────────────────────────────────────
    dbg = parser.add_argument_group("Debugging")
    dbg.add_argument("-debug", "--debug",
                     help="Verbose logging (prints prompts, verifier output, and diffs)",
                     action=argparse.BooleanOptionalAction, default=False)
    dbg.add_argument("-clear", "--clear",
                     help="Clear temp/output subfolders before running",
                     action=argparse.BooleanOptionalAction, default=False)

    # Version
    parser.add_argument("--version", action="version", version="%(prog)s - Version 1.2")

    return parser.parse_args()

# Main function
if __name__ == "__main__":
    # Dictionary that maps the function to the function to call
    switcher = {
        "generate_prompt": generate_initial_prompt,
        "generate_code": generate_code,
        "improve_code_step": improve_code_step,
        "generate_code_folder": generate_folder
    }

    # Load the environment variables
    load_dotenv()
    arguments = parse_arguments(list(switcher.keys()))
    arguments = _normalize_args(arguments)

    # Ensure that the integers are valid
    ensure_integers(arguments)
    if arguments.clear:
        clear(arguments)

    # Get the function from switcher dictionary
    switcher.get(arguments.function, lambda *_: print("Invalid function"))(arguments)
