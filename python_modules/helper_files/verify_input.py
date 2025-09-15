""" This module contains functions that verify the input given by the user.
    The functions check if the input is valid and if the files and directories exist."""
import sys
import os
from helper_files.list_files import get_absolute_path
from Frama_C.solvers import solvers
from LLM.GPT import GPT
from LLM.Groq import Groq_LLM
from LLM.LLama import LLama
from LLM.Openrouter import OpenRouterGPT
from openai import OpenAI

# --------- small helpers ------------------------------------------------------

def _get(args, *names):
    """Return the first existing attribute among names, else None."""
    for n in names:
        if hasattr(args, n) and getattr(args, n) not in (None, ""):
            return getattr(args, n)
    return None

def _set(args, name, value):
    setattr(args, name, value)

def _abs_path(p):
    return p if os.path.isabs(p) else os.path.join(os.getcwd(), p)

# --------- directory checks ---------------------------------------------------

def require_directory(args):
    """Check that an input directory is provided."""
    directory = _get(args, "input_dir", "directory")
    if not directory:
        print("Please provide an input directory with -d or --input-dir")
        sys.exit()
    _set(args, "input_dir", directory)  # canonical
    _set(args, "directory", directory)  # legacy alias

def require_directory_exists(args):
    """Check that the input directory exists and set absolute path."""
    require_directory(args)
    dir_path = _get(args, "input_dir", "directory")
    abs_dir = _abs_path(dir_path)
    _set(args, "absolute_directory", abs_dir)
    if not os.path.isdir(abs_dir):
        print(f"Please insert a valid directory, {dir_path} is not a directory")
        sys.exit()

# --------- specification bundle ----------------------------------------------

# Optional extra code file (e.g., extras.c / extras.h)
def require_optional_extra_specs(args):
    """If --extra-specs is provided, validate it and set absolute/name fields."""
    extra = getattr(args, "extra_specs", None)
    if not extra:  # truly optional
        return

    # Only files supported (not directories)
    abs_extra = extra if os.path.isabs(extra) else os.path.join(os.getcwd(), extra)
    if not os.path.isfile(abs_extra):
        print(f"Please insert a valid extra specs file, {extra} is not a file")
        sys.exit()

    args.extra_specs = extra                                   # canonical
    args.absolute_extra_specs_path = abs_extra                  # absolute path
    args.extra_specs_name = os.path.basename(abs_extra)         # filename only


def require_problem_specification(args):
    """Validate spec selection & presence of files."""
    st = getattr(args, "specification_type", "both")
    args.formal_specification_included = (st in ("formal", "both"))
    args.natural_language_included    = (st in ("natural", "both"))

    if _get(args, "natural_spec_file", "natural_language_specification"):
        requires_natural_language_specification_file(args)

    require_formal_specification_file(args)
    requires_function_signature(args)

    if args.natural_language_included:
        requires_natural_language_specification_file(args)

    # NEW: optional extras.c/.h
    require_optional_extra_specs(args)


def require_formal_specification_file(args):
    """Ensure ACSL formal specification header exists; set absolute + name."""
    fs = _get(args, "formal_spec_file", "formal_specification_file")
    if not fs:
        print("Please provide a formal specification with -fsf or --formal-spec-file")
        sys.exit()

    if not fs.endswith(".h"):
        fs += ".h"

    abs_fs = _abs_path(fs)
    name   = os.path.basename(abs_fs)

    _set(args, "formal_spec_file", fs)                         # canonical
    _set(args, "formal_specification_file", fs)                # legacy
    _set(args, "absolute_formal_specification_path", abs_fs)   # used elsewhere
    _set(args, "formal_specification_file_name", name)         # legacy name

    if not os.path.isfile(abs_fs):
        print(f"Please insert a valid formal specification file, {fs} is not a file")
        sys.exit()
    if not abs_fs.endswith(".h"):
        print("The formal specification file must be a .h file")
        sys.exit()

def requires_natural_language_specification_file(args):
    """Ensure NL spec file exists; set absolute + name."""
    nl = _get(args, "natural_spec_file", "natural_language_specification")
    if not nl:
        print("Please provide a natural-language specification with -nl or --natural-spec-file")
        sys.exit()

    abs_nl = _abs_path(nl)
    name   = os.path.basename(abs_nl)

    _set(args, "natural_spec_file", nl)                               # canonical
    _set(args, "natural_language_specification", nl)                   # legacy
    _set(args, "absolute_natural_language_specification_path", abs_nl) # legacy field name
    _set(args, "natural_language_specification_name", name)

    if not os.path.isfile(abs_nl):
        print(f"Please insert a valid natural language specification file, {nl} is not a file")
        sys.exit()

def requires_function_signature(args):
    """Ensure signature file exists; set absolute + name."""
    sig = _get(args, "signature_file", "function_signature")
    if not sig:
        print("Please provide a function signature with -sig or --signature-file")
        sys.exit()

    abs_sig = _abs_path(sig)
    name    = os.path.basename(abs_sig)

    _set(args, "signature_file", sig)                     # canonical
    _set(args, "function_signature", sig)                 # legacy
    _set(args, "absolute_function_signature_path", abs_sig)
    _set(args, "function_signature_name", name)

    if not os.path.isfile(abs_sig):
        print(f"Please insert a valid function signature file, {sig} is not a file")
        sys.exit()

# --------- C file -------------------------------------------------------------

def require_c_file(args):
    """Ensure a C file is provided and exists; set absolute + name."""
    c = _get(args, "c_file")
    if not c:
        print("Please provide a C file with -c or --c-file")
        sys.exit()

    abs_c = _abs_path(c)
    name  = os.path.basename(abs_c)
    _set(args, "absolute_c_path", abs_c)
    _set(args, "c_file_name", name)

    if not os.path.isfile(abs_c):
        print(f"Please insert a valid C file, {c} is not a file")
        sys.exit()

# --------- solver -------------------------------------------------------------

def require_solver(args):
    """Ensure selected solver(s) are available."""
    available = solvers()
    if "Coq" in available:
        available.remove("Coq")

    if args.solver is None:
        args.solver = ",".join(available)
    elif args.solver not in available:
        print(f"The solver {args.solver} is not available, please use one of: {available}")
        sys.exit()

# --------- output dir / file --------------------------------------------------

def require_output_path(args):
    """Ensure output directory exists (create if needed)."""
    out = _get(args, "output_dir", "output_path")
    if not out:
        print("Please provide an output directory with -o or --output-dir")
        sys.exit()

    abs_out = get_absolute_path(out)
    _set(args, "output_dir", out)                     # canonical
    _set(args, "output_path", out)                    # legacy
    _set(args, "absolute_output_directory", abs_out)  # used elsewhere

    if not os.path.isdir(abs_out):
        os.makedirs(abs_out)

def check_output_path_set(args):
    """Derive output dir/file from other inputs when not explicitly set."""
    out = _get(args, "output_dir", "output_path")
    if not out:
        if _get(args, "c_file"):
            abs_c = get_absolute_path(args.c_file)
            _set(args, "absolute_c_path", abs_c)
            _set(args, "c_file_name", os.path.basename(abs_c))
            _set(args, "absolute_output_directory", os.path.dirname(abs_c))
        elif _get(args, "input_dir", "directory"):
            _set(args, "absolute_output_directory", _get(args, "absolute_directory") or _abs_path(_get(args, "input_dir", "directory")))
        elif _get(args, "absolute_formal_specification_path"):
            _set(args, "absolute_output_directory", os.path.dirname(args.absolute_formal_specification_path))
        else:
            print("Please provide an output directory with -o or --output-dir")
            sys.exit()
    else:
        _set(args, "absolute_output_directory", get_absolute_path(out))

    # Derive output file name if missing
    of = _get(args, "output_file", "output_file_name")
    if not of:
        if _get(args, "c_file"):
            _set(args, "output_file_name", _get(args, "c_file_name"))
            _set(args, "output_file", _get(args, "c_file_name"))
        elif _get(args, "absolute_formal_specification_path"):
            base = os.path.basename(args.absolute_formal_specification_path).replace(".h", ".c")
            _set(args, "output_file_name", base)
            _set(args, "output_file", base)

    # Ensure directory exists
    abs_out = _get(args, "absolute_output_directory")
    if not os.path.isdir(abs_out):
        os.makedirs(abs_out)

# --------- numeric ranges -----------------------------------------------------

def ensure_integers(args):
    """Validate integer/float ranges."""
    if args.wp_timeout is not None and args.wp_timeout <= 0:
        print("The weakest precondition timeout must be a strictly positive integer")
        sys.exit()

    if _get(args, "iterations") is not None and args.iterations < 0:
        print("The number of iterations must be a positive integer")
        sys.exit()

    if args.temperature is not None and args.temperature < 0:
        print("The temperature must be a positive value")
        sys.exit()
    elif args.temperature is not None and args.temperature > 1:
        print("The temperature must be a value between 0 and 1")
        sys.exit()

    if args.reboot is not None and args.reboot <= 0:
        print("The reboot must be a positive integer")
        sys.exit()

    # initial examples: support both old and new names
    ie = _get(args, "initial_examples", "initial_examples_generated", "generated_samples")
    if ie is not None and ie <= 0:
        print("The number of initial/generated samples must be a positive integer")
        sys.exit()

# --------- model selection ----------------------------------------------------

def require_model(args):
    """Validate model name and instantiate the correct LLM wrapper.

    Provider selection rules:
      1) Explicit hint via args.provider / args.api_provider / args.llm_provider
      2) Heuristic: if model_name contains a slash (e.g., 'anthropic/claude-3.5-sonnet'),
         assume OpenRouter.
      3) Fallbacks: known Groq / Llama lists, else default to OpenAI.
    """
    m = _get(args, "model_name")
    if not m:
        print("Please provide a model name with -model or --model-name")
        sys.exit()

    provider_hint = (_get(args, "provider", "api_provider", "llm_provider") or "").lower()

<<<<<<< HEAD
    # Put the model in the args, and create an instance
    if args.model_name in ['gpt-3.5-turbo', 'gpt-3.5', 'gpt-4', 'gpt-4o']:
        # If the api key is not set, then give an error
        if os.getenv("OPENAI_API_KEY") is None:
            print("Please set the OPENAI_API_KEY environment variable")
            sys.exit()
        args.model = GPT(args, os.getenv("OPENAI_API_KEY"))
    elif args.model_name in ['llama3.1-70b', 'llama3.1-8b', 'llama3.1-405b']:
        # If the api key is not set, then give an error
        if os.getenv("LLAMA_API_KEY") is None:
            print("Please set the LLAMA_API_KEY environment variable")
            sys.exit()
        args.model = LLama(args, os.getenv("LLAMA_API_KEY"))
    else:
        if os.getenv("GROQ_API_KEY") is None:
            print("Please set the GROQ_API_KEY environment variable")
            sys.exit()
        args.model = Groq_LLM(args, os.getenv("GROQ_API_KEY"))
=======
    # Known sets for quick routing (extend as needed)
    groq_models = {
        "llama3-8b-8192", "llama3-70b-8192", "llama-3.1-8b-instant", "llama-3.1-70b-versatile",
        "mixtral-8x7b-32768", "gemma-7b-it", "gemma2-9b-it"
    }
    llama_api_models = {"llama3.1-70b", "llama3.1-8b", "llama3.1-405b"}
>>>>>>> 09cadd7 (Update code, ignore untracked files)

    # Heuristic: OpenRouter if explicitly requested OR model has a vendor prefix like "vendor/model"
    is_openrouter = (provider_hint == "openrouter") or ("/" in m)

    if is_openrouter:
        key = os.getenv("OPENROUTER_API_KEY")
        if not key:
            print("Please set the OPENROUTER_API_KEY environment variable")
            sys.exit()
        # Optional analytics headers if present on args
        site_url = _get(args, "site_url", "openrouter_site_url")
        app_name = _get(args, "app_name", "openrouter_app_name")
        args.model = OpenRouterGPT(args, key, site_url=site_url, app_name=app_name)
        return

    if provider_hint == "groq" or m in groq_models:
        key = os.getenv("GROQ_API_KEY")
        if not key:
            print("Please set the GROQ_API_KEY environment variable")
            sys.exit()
        args.model = Groq_LLM(args, key)
        return

    if provider_hint in ("llama", "meta") or m in llama_api_models:
        key = os.getenv("LLAMA_API_KEY")
        if not key:
            print("Please set the LLAMA_API_KEY environment variable")
            sys.exit()
        args.model = LLama(args, key)
        return

    # Default: OpenAI (no slow/pricey model enumeration)
    key = os.getenv("OPENAI_API_KEY")
    if not key:
        print("Please set the OPENAI_API_KEY environment variable")
        sys.exit()
    args.model = GPT(args, key)

# --------- folder-mode spec names --------------------------------------------

def require_set_specification_names(args):
    """Check that required files are set for folder generation."""
    if not _get(args, "formal_spec_file", "formal_specification_file"):
        print("Please insert a formal specification file with -fsf or --formal-spec-file")
        sys.exit()
    if not _get(args, "natural_spec_file", "natural_language_specification"):
        print("Please insert a natural language specification file with -nl or --natural-spec-file")
        sys.exit()
    if not _get(args, "signature_file", "function_signature"):
        print("Please insert a function signature with -sig or --signature-file")
        sys.exit()
