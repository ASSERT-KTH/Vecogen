""" This module contains the function that iteratively generates a prompt based on a 
    verification error message """
import os
import json
import re
from LLM.create_prompt import create_prompt
from LLM.code_generation_objects import IterationInformation, CompletionInformation, CodeGenerationProcess
from Verify_files.check_file import check_file
from testing.test_function import test_generated_code
from helper_files.list_files import list_folders_directory, list_files_directory
from helper_files.specification import add_specifications_to_code
from helper_files.output_file import output_results
from helper_files.verify_input import require_problem_specification

def generate_code_process(args):
    """Function to iteratively generate code and check it
    Returns:
        code_generation_process: The code generation process
    Args:
        args: The arguments given to the program
        print_information_iteration: Boolean that indicates if the information\
        about the iteration should be printed
    """

    # Create a code generation process object
    code_generation_process = CodeGenerationProcess(args)

    # Perform the initial code generation step
    initial_code_generation_information = initial_code_generation_step(args)

    # Add the initial code generation information to the code generation process
    code_generation_process.add_initial_code_generation_information(initial_code_generation_information)

    verified = initial_code_generation_information.is_verified

    # Create an index for the code improvement iterations
    i = 0
    last_iteration = initial_code_generation_information

    # Do the code improvement steps until the code is verified or the maximum iterations are reached
    while (i < args.iterations and not verified):
        print("-" * 100)
        print(f"Code improvement iteration {i + 1} of {args.iterations}.")
        print("-" * 100)

         # Take the best attempt from the initial generation attempts
        code = last_iteration.best_attempt_code
        output = last_iteration.best_attempt_feedback

        # Perform the code improvement step
        code_improvement_information = code_improvement_step(args, i + 1, code, output)

        # Add the code improvement information to the code generation process
        code_generation_process.add_code_improvement_information(code_improvement_information)

        # Stop if the code is verified
        verified = code_improvement_information.is_verified

        # Update the last iteration and the counter
        last_iteration = code_improvement_information
        i += 1

    # Print the results
    print(f"Total completions used: {code_generation_process.total_completions_used}, total tokens used: {code_generation_process.total_tokens_used}, total time taken: {code_generation_process.total_time_taken_verification}.")
    print(f"Has the code been successfully verified: {verified}")
    if args.debug:
        print("Results:")
        for result in code_generation_process.code_improvement_information:
            print(result)

    # save the results to a file
    output_results(args, code_generation_process.to_dict())
    return code_generation_process

# Function that processes the generated code by adding the specification and creating the output file
def add_specification_and_output_code(args, code):
    """Extract C code (fenced or not), inject specs, and write to output."""
    import os, re

    def _extract_c(src: str) -> str:
        # Prefer fenced blocks
        m = re.search(r"```(?:[cC]\b)?\s*\n(.*?)```", src, re.DOTALL) or \
            re.search(r"```\s*\n(.*?)```", src, re.DOTALL)
        if m:
            return m.group(1).strip()

        # Heuristic: start at first include/typedef/struct/enum/extern/static or signature
        lines = src.splitlines()
        sig = re.compile(r'^\s*[_a-zA-Z][\w\s\*\[\]]+\s+[_a-zA-Z]\w*\s*\([^;{]*\)\s*\{?\s*$')
        start = 0
        for i, ln in enumerate(lines):
            s = ln.strip()
            if s.startswith(('#include','typedef','struct','enum','extern','static')) or sig.match(ln):
                start = i
                break
        return "\n".join(lines[start:]).strip()

    # --- Extract only; DO NOT trim header here (spec helper will do it once) ---
    code_body = _extract_c(code)

    # Paths
    formal = getattr(args, "absolute_formal_specification_path", None)
    natural = getattr(args, "absolute_natural_language_specification_path", None)
    signature = getattr(args, "absolute_function_signature_path", None)
    extra = getattr(args, "absolute_extra_specs_path", None) or getattr(args, "absolute_extra_specs", None)
    if not formal or not signature:
        raise ValueError("Missing required spec paths: formal and signature must be set.")

<<<<<<< HEAD
    # Output the code to the specified file
    if args.debug:
        print(f"Writing the code to the file {args.absolute_output_directory}/{args.output_file_name}")
    with open(args.absolute_output_directory + "/" + args.output_file_name, "w",
                encoding="utf-8") as f:
        args.absolute_c_path = args.absolute_output_directory + "/" + args.output_file_name
        f.write(code)
=======
    # Inject specs (this call handles removing the model's own header/brace)
    code_out = add_specifications_to_code(formal, natural, signature, extra, code_body)
>>>>>>> 09cadd7 (Update code, ignore untracked files)

    # Output target
    out_dir = getattr(args, "absolute_output_directory")
    out_file = getattr(args, "output_file", None) or getattr(args, "output_file_name", None)
    if not out_file:
        out_file = f"output_{getattr(args, 'model_name', 'model')}.c"
        args.output_file = out_file
        args.output_file_name = out_file

    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, out_file)

    with open(out_path, "w", encoding="utf-8") as f:
        f.write(code_out)
    args.absolute_c_path = out_path

    if getattr(args, "debug", False):
        print(f"Code generated. Written to {out_path}")

    return code_out


def generate_code_folder(args):
    """Generate code for each subfolder in --input-dir, writing to --output-dir/<subfolder>."""
    import os

    def _first(*names):
        for n in names:
            v = getattr(args, n, None)
            if v:
                return v
        return None

    def _join(*p): return os.path.join(*p)

    # Roots
    src_root = _first("absolute_directory", "input_dir", "directory")
    out_root = getattr(args, "absolute_output_directory")

    # Folders
    try:
        folders = list_folders_directory(src_root)
    except NameError:
        folders = [d for d in os.listdir(src_root) if os.path.isdir(_join(src_root, d))]
    print("Found the following folders in the directory:", set(folders))

    def _numkey(name):
        head = name.split("-", 1)[0]
        return (0, int(head), name) if head.isdigit() else (1, name)
    folders.sort(key=_numkey)

    # Spec filenames expected in each subfolder
    nl_name  = _first("natural_spec_file", "natural_language_specification")
    fs_name  = _first("formal_spec_file", "formal_specification_file")
    sig_name = _first("signature_file", "function_signature")
    nl_name  = os.path.basename(nl_name)  if nl_name  else None
    fs_name  = os.path.basename(fs_name)  if fs_name  else None
    sig_name = os.path.basename(sig_name) if sig_name else None

    # Optional extras (either a global path or a per-folder filename)
    extra_cfg = getattr(args, "extra_specs", None)
    extra_global_abs = None
    extra_name = None
    if extra_cfg:
        cand = extra_cfg if os.path.isabs(extra_cfg) else os.path.join(os.getcwd(), extra_cfg)
        if os.path.isfile(cand):
            extra_global_abs = cand
        extra_name = os.path.basename(extra_cfg)

    # Early checks
    if not fs_name:
        print("No formal spec given; set -fsf/--formal-spec-file to a filename (e.g., spec.h).")
        return
    if not sig_name:
        print("No function signature given; set -sig/--signature-file to a filename (e.g., sig.h).")
        return
    if getattr(args, "natural_language_included", False) and not nl_name:
        print("Spec type requires natural language; set -nl/--natural-spec-file to a filename.")
        return

    # Filter by presence
    original = list(folders)
    folders = [f for f in folders if os.path.exists(_join(src_root, f, fs_name))]
    if len(set(original) - set(folders)) > 0:
        print("Removed (no formal spec):", set(original) - set(folders))

    original = list(folders)
    folders = [f for f in folders if os.path.exists(_join(src_root, f, sig_name))]

    if len(set(original) - set(folders)) > 0:
        print("Removed (no signature):", set(original) - set(folders))

    if getattr(args, "natural_language_included", False) and nl_name:
        original = list(folders)
        folders = [f for f in folders if os.path.exists(_join(src_root, f, nl_name))]
        print("Removed (no natural spec):", set(original) - set(folders))

    # Only keep folders with an integer of >= 31
    # folders = [f for f in folders if f.isdigit() and int(f) >= 43]
    # folders.append('28')
    print(folders)

    # Per-folder generation
    for folder in folders:
<<<<<<< HEAD
        # Set the input and output files
        args.natural_language_specification = args.directory + "/" + folder + "/" + natural_language_file_name
        args.formal_specification_file = args.directory + "/" + folder + "/" + formal_specification_file_name
        args.function_signature = args.directory + "/" + folder + "/" + function_signature_file_name
        
        print(f"Starting to generate code for folder {folder}....")
=======
        # Point args to files inside this folder
        if nl_name:
            args.natural_spec_file = _join(src_root, folder, nl_name)
            args.natural_language_specification = args.natural_spec_file  # legacy
        args.formal_spec_file = _join(src_root, folder, fs_name)
        args.formal_specification_file = args.formal_spec_file            # legacy
        args.signature_file = _join(src_root, folder, sig_name)
        args.function_signature = args.signature_file                      # legacy
>>>>>>> 09cadd7 (Update code, ignore untracked files)

        # Optional extras: global file takes precedence; else look inside folder by name; else unset
        if extra_global_abs:
            args.extra_specs = extra_global_abs
        elif extra_name and os.path.isfile(_join(src_root, folder, extra_name)):
            args.extra_specs = _join(src_root, folder, extra_name)
        else:
            args.extra_specs = None  # avoid stale value from previous folder

        # Output location: <out_root>/<folder>
        args.absolute_output_directory = _join(out_root, folder)
        os.makedirs(args.absolute_output_directory, exist_ok=True)

        # Default output filename if none provided
        if not _first("output_file", "output_file_name"):
            default_c = f"output_{getattr(args, 'model_name', 'model')}.c"
            args.output_file = default_c
            args.output_file_name = default_c  # legacy

        # Validate specs (also validates optional extras via require_optional_extra_specs)
        require_problem_specification(args)

        # Run generation
        generate_code_process(args)

<<<<<<< HEAD
        # Print the current generated file
        print("\n \n" + "-" * 100 + "\n \n")
        print(f"Generated code for folder {folder}. \n\n")
=======
        print("\n" + "-" * 100 + f"\nGenerated code for folder {folder}.\n")
>>>>>>> 09cadd7 (Update code, ignore untracked files)

# Function that verifies and tests the code that has been generated
def verify_and_test_code_attempt(args, response_gpt, i):
    """
    Verify & (optionally) test the generated code.
    """
    import os

    # 1) Write code w/ specs
    try:
        code = add_specification_and_output_code(args, response_gpt)
    except Exception as e:
        if getattr(args, "debug", False):
            print(f"Error: Could not add the specification to the code, error: {e}")
        return response_gpt, False, "Could not add specification to code", "0 / 0", {
            "summary": {"passed": 0, "failed": 0, "total": 0,
                        "information": f"Error with LLM response: {e}"}
        }, 0

    # 2) Loop policy
    if not getattr(args, "allow_loops", False) and contains_loop(code):
        return code, False, "Code contains a loop, but loops are not allowed", "0 / 0", {
            "summary": {"passed": 0, "failed": 0, "total": 0,
                        "information": "Loops are not allowed"}
        }, 0

    print(f"Step 2: Compiling the code...")
    # 3) Formal verification
    verified, output, verified_goals, verification_time_taken = check_file(args.absolute_c_path, args)
    if getattr(args, "debug", False):
        print(f"Verification time taken: {verification_time_taken}")

    # If compilation failed during verification, bail out before tests
    if not verified and verified_goals is None:
        test_information = {"summary": {"passed": 0, "failed": 0, "total": 0,
                                        "information": "Compilation failed"}}
        return code, verified, output, "0 / 0", test_information, verification_time_taken

    # 4) Locate a test SOURCE file (not a directory!)
    def _first(*names):
        for n in names:
            v = getattr(args, n, None)
            if v:
                return v
        return None

    base_dir = os.path.dirname(getattr(args, "absolute_formal_specification_path",
                          os.path.dirname(args.absolute_c_path)))
    tests_cfg = _first("tests_path", "tests_file")  # canonical then legacy
    test_source = None

    def _candidate(p):
        return p if os.path.isabs(p) else os.path.join(base_dir, p)

    # a) If user provided something, resolve it
    if tests_cfg:
        cand = _candidate(tests_cfg)
        if os.path.isdir(cand):
            # Try common names inside the dir
            for name in ("tests.c", "test.c"):
                if os.path.isfile(os.path.join(cand, name)):
                    test_source = os.path.join(cand, name)
                    break
        elif os.path.isfile(cand):
            test_source = cand

    # b) If still unset, try defaults next to the specs
    if not test_source:
        for name in ("tests.c", "test.c"):
            cand = os.path.join(base_dir, name)
            if os.path.isfile(cand):
                test_source = cand
                break

    # 5) Run tests if we found a source file
    print(f"Step 4: Testing the code...")
    if test_source:
        temp_dir = _first("temp_dir", "temp_folder") or os.path.join(os.getcwd(), "tmp")
        passed_tests, total_tests, test_information = test_generated_code(
            args.absolute_c_path, test_source, "temp_test_file", temp_dir, getattr(args, "debug", False)
        )
    else:
        test_information = {"summary": {"passed": 0, "failed": 0, "total": 0,
                                        "information": "No tests found"}}
        passed_tests, total_tests = 0, 0
<<<<<<< HEAD
        if args.debug:
            print(f"No tests found, proved goals: {verified_goals}") 
    print(f"Verified goals: {verified_goals}, tests: {passed_tests} / {total_tests}. Used {verification_time_taken} seconds to verify.")
=======
        if getattr(args, "debug", False):
            print(f"No tests found, proved goals: {verified_goals}")
>>>>>>> 09cadd7 (Update code, ignore untracked files)

    print(f"Step 5: Testing complete. Verified goals: {verified_goals}, tests: {passed_tests} / {total_tests}")
    return code, verified, output, verified_goals, test_information, verification_time_taken


# --- helpers used locally ---
def _initial_examples(args, default=10):
    return (
        getattr(args, "initial_examples", None)
        or getattr(args, "initial_examples_generated", None)
        or getattr(args, "generated_samples", None)
        or default
    )


def initial_code_generation_step(args):
    """Generate candidates one-by-one and stop early if one verifies."""
    iex = _initial_examples(args)
    iteration_info = IterationInformation(0, iex, args.model_name)

    prompt = create_prompt(args)
    print("Generating the code using " + args.model_name)

    generated = 0
    while generated < iex and not iteration_info.is_verified:
        # Request exactly one completion
        responses, tokens_used_call, model_used = args.model.make_request(prompt, 1)
        resp = responses[0]

        print("-" * 50)
        print(f"Initial code generation, code completion {generated + 1} of {iex}.")
        print("-" * 50)
        print("Step 1: Adding specification and outputting code.")

        response = resp.message.content
        ci = process_code_and_get_completion_information(
            args, response, 0, prompt, tokens_used_call, model_used
        )
        iteration_info.add_completion(ci)

        generated += 1
        if ci.is_verified:
            break

    return iteration_info


def code_improvement_step(args, code_improvement_iteration, code, output):
    """Improve code one-by-one and stop early if a candidate verifies."""
    iex = _initial_examples(args)
    iteration_info = IterationInformation(code_improvement_iteration, iex, args.model_name)

    prompt = create_prompt(args, code, output, "feedback")

    generated = 0
    while generated < iex and not iteration_info.is_verified:
        # Request exactly one completion
        responses, tokens_used_call, model_used = args.model.make_request(prompt, 1)
        resp = responses[0]

        print("-" * 50)
        print(f"Code Improvement Iteration {code_improvement_iteration}, "
              f"code completion {generated + 1} of {iex}.")
        print("-" * 50)
        print("Step 1: Adding specification and outputting code.")

        response = resp.message.content
        ci = process_code_and_get_completion_information(
            args, response, code_improvement_iteration, prompt, tokens_used_call, model_used
        )
        iteration_info.add_completion(ci)

        generated += 1
        if ci.is_verified:
            break

    return iteration_info


def prompt_using_max_n_samples(args, prompt, n_max):
    """
    Deprecated in practice by the one-by-one loops above, but kept for compatibility.
    If you still call this somewhere else, it will now just request in chunks of 1
    without prefetching the full budget at once.
    """
    responses_llm, tokens_used, models_used = [], [], []
    total = _initial_examples(args)
    generated = 0
    while generated < total:
        responses, tokens_used_call, model_used = args.model.make_request(prompt, 1)
        responses_llm.extend(responses)
        tokens_used.append(tokens_used_call)
        models_used.append(model_used)
        generated += 1
    return responses_llm, tokens_used, models_used


# Process a single candidate and collect completion info
def process_code_and_get_completion_information(
    args, response_gpt, i, prompt, tokens_used, model_used, initial_attempt=False, rebooting=False
):
    code, verified, verification_output, verified_goals, test_information, verification_time_taken = \
        verify_and_test_code_attempt(args, response_gpt, i)

    if initial_attempt:
        information = "Initial code generation attempt"
    elif rebooting:
        information = "The code was rebooted"
    elif verified:
        information = "The code has been verified"
    else:
        information = "The code has been improved"

    completion_information = CompletionInformation(
        i, prompt, response_gpt, verified, verified_goals, test_information,
        args.temperature, information, tokens_used, model_used, code,
        verification_output, verification_time_taken
    )
    return completion_information

def contains_loop(code):
    # Remove comments then check for loops
    code = re.sub(r'//.*', '', code)
    code = re.sub(r'/\*.*?\*/', '', code, flags=re.DOTALL)
    return bool(re.compile(r'\b(for|while)\b').search(code))