"""Build prompts for generating formally verified C code (Frama-C)."""

import json
# Hardcoded paths
ONE_SHOT_PATH_INITIAL = "../prompts/one_shot_example_initial.txt"
ONE_SHOT_PATH_FEEDBACK = "../prompts/one_shot_example_feedback.txt"


def _coerce_to_text(obj) -> str:
    """Return a readable string for strings, lists/tuples, dicts, etc."""
    if obj is None:
        return ""
    if isinstance(obj, str):
        return obj
    if isinstance(obj, (list, tuple)):
        parts = []
        for x in obj:
            if isinstance(x, str):
                parts.append(x)
            else:
                try:
                    parts.append(json.dumps(x, ensure_ascii=False, indent=2))
                except Exception:
                    parts.append(str(x))
        return "\n".join(parts)
    try:
        return json.dumps(obj, ensure_ascii=False, indent=2)
    except Exception:
        return str(obj)
    
def create_prompt(
    args,
    previous_attempt: str = "",
    previous_attempt_feedback: str = "",
    prompt_mode: str = "initial",  # "initial" | "feedback"
):
    """Create an LLM prompt for either an initial task or a feedback iteration."""

    # Determine inclusion mode from args.specification_type
    include_mode = getattr(args, "specification_type", "both")

    # Resolve inclusion based on include_mode (overrides args.*_included)
    nl_inc, acsl_inc = _resolve_inclusion(
        include_mode,
        default_nl=getattr(args, "natural_language_included", False),
        default_acsl=getattr(args, "formal_specification_included", False),
    )

    header = (
        "You are an expert C software engineer specializing in safety-critical code verified with Frama-C.\n\n"
        "-----END_ASSISTANT_INFORMATION-----\n"
    )

    one_shot = add_one_shot_example(
        prompt_technique=args.prompt_technique,
        natural_language_included=nl_inc,
        formal_specification_included=acsl_inc,
        path=_pick_one_shot_path(prompt_mode),
    )

    if prompt_mode == "initial":
        context = build_context_section(args, include_nl=nl_inc, include_acsl=acsl_inc)
        feedback_block = ""
    elif prompt_mode == "feedback":
        context = build_context_section(args, include_nl=nl_inc, include_acsl=acsl_inc)
        feedback_block = build_feedback_section(previous_attempt, previous_attempt_feedback, args)

    else:
        raise ValueError("prompt_mode must be 'initial' or 'feedback'.")

    rules_block = rules(
        allow_loops=args.allow_loops,
        include_nl=nl_inc,
        include_acsl=acsl_inc,
    )

    cta = (
        "Output only one fenced C code block containing the complete function definition "
        "(same signature + generated body). Output nothing else."
    )

    parts = [
        header,
        one_shot,
        context,
        feedback_block,
        "\nYOUR TASK:\n",
        rules_block,
        "\n",
        cta,
    ]
    return "\n".join(p for p in parts if p and p.strip())


# ---------------------------------------------------------------------------
# Sections
# ---------------------------------------------------------------------------

def build_context_section(args, include_nl: bool, include_acsl: bool):
    extra = add_extra_code(getattr(args, "absolute_extra_specs_path", None)).strip()
    nl = add_natural_language_specification(
        getattr(args, "absolute_natural_language_specification_path", None),
        include_nl,
    ).strip()
    acsl = add_formal_specification(
        getattr(args, "absolute_formal_specification_path", None),
        include_acsl,
    ).strip()
    sig = add_signature(getattr(args, "absolute_function_signature_path", None)).strip()

    blocks = ["--- CONTEXT (for reference only) ---"]
    if extra:
        blocks += ["EXTRA CODE:", "```c", extra, "```"]
    if include_nl and nl:
        blocks += ["NATURAL LANGUAGE DESCRIPTION:", "```c", nl, "```"]
    if include_acsl and acsl:
        blocks += ["ACSL FORMAL SPECIFICATION:", "```c", acsl, "```"]
    if sig:
        blocks += ["FUNCTION SIGNATURE:", "```c", sig, "```"]
    blocks.append("--- END CONTEXT ---")
    return "\n".join(blocks)

def build_feedback_section(
    previous_attempt: str,
    previous_attempt_feedback,
    args,
):
    """
    Show detailed verification feedback only if specification_type is 'formal' or 'both'.
    For 'natural', hide details to avoid leaking formal-spec info.
    """
    prev_attempt_txt = _coerce_to_text(previous_attempt)
    if not prev_attempt_txt.strip():
        return ""

    # Determine if we should show details
    spec_type = getattr(args, "specification_type", getattr(args, "spectype", "both")).lower()
    show_details = spec_type in ("formal", "both")

    # Fence the previous attempt if needed
    fenced_prev = (
        prev_attempt_txt if prev_attempt_txt.strip().startswith("```")
        else f"```C\n{prev_attempt_txt}\n```"
    )

    out = [
        "\n--- PREVIOUS ATTEMPT (did not verify) ---",
        fenced_prev,
    ]

    prev_feedback_txt = _coerce_to_text(previous_attempt_feedback).strip()
    if show_details and prev_feedback_txt:
        out += ["--- VERIFICATION FEEDBACK ---", prev_feedback_txt]
    else:
        out += [
            "--- FORMAL VERIFICATION RESULT ---",
            "The program did not pass formal verification with Frama-C. "
            "Improve the function to satisfy the specification and avoid undefined behavior. "
            "Fix it yourself and output only the corrected function definition.",
        ]

    out.append("--- END FEEDBACK ---")
    return "\n".join(out)

def add_one_shot_example(
    prompt_technique: str,
    natural_language_included: bool = False,
    formal_specification_included: bool = False,
    path: str | None = None,
):
    if prompt_technique == "zero-shot" or not path:
        return ""
    with open(path, "r", encoding="utf-8") as fh:
        content = fh.read()
    parts = content.split("---END_NATURAL_LANGUAGE---")
    natural_language = parts[0] if parts else ""
    rest = parts[1] if len(parts) > 1 else ""
    parts2 = rest.split("---END_FORMAL_SPECIFICATION---")
    formal_specification = parts2[0] if parts2 else ""
    function_example = parts2[1] if len(parts2) > 1 else rest

    block = ["Here is an example of the task:\n```C\n"]
    if natural_language_included and natural_language.strip():
        block.append(natural_language.rstrip("\n"))
    if formal_specification_included and formal_specification.strip():
        block.append(formal_specification.rstrip("\n"))
    block.append(function_example.strip())
    block.append("\n```")
    return "".join(block)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _pick_one_shot_path(prompt_mode: str) -> str | None:
    if prompt_mode == "initial":
        return ONE_SHOT_PATH_INITIAL
    if prompt_mode == "feedback":
        return ONE_SHOT_PATH_FEEDBACK
    return None


def _resolve_inclusion(include_mode: str, default_nl: bool, default_acsl: bool):
    """Return (include_nl, include_acsl) based on include_mode."""
    mode = (include_mode or "both").lower()
    if mode in ("nl", "nl_only", "natural", "natural_only"):
        return True, False
    if mode in ("acsl", "acsl_only", "formal", "formal_only"):
        return False, True
    if mode in ("none", "no_context"):
        return False, False
    # "both" (or unrecognized): fall back to provided defaults
    return default_nl, default_acsl


def _read(path):
    if not path:
        return ""
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def add_formal_specification(formal_spec_absolute: str, formal_specification_included: bool = False):
    return _read(formal_spec_absolute) if formal_specification_included else ""


def add_signature(signature_absolute: str):
    return _read(signature_absolute)


def add_natural_language_specification(natural_absolute: str, natural_language_included: bool = False):
    return _read(natural_absolute) if natural_language_included else ""


def add_extra_code(extra_absolute: str):
    txt = _read(extra_absolute)
    return txt if txt.strip() else ""


def rules(allow_loops=False, include_nl: bool = True, include_acsl: bool = True):
    """Rules text adapts to which context is present."""
    rules_array = ["You must adhere to the following rules:"]
    rules_array.append("Keep the function signature exactly as provided.")

    if include_acsl:
        rules_array.append("Respect all ACSL pre- and postconditions.")
    if include_nl and include_acsl:
        rules_array.append("If the natural language description and ACSL conflict, follow the ACSL.")
    elif include_nl and not include_acsl:
        rules_array.append("Follow the natural language description precisely.")

    # Build dynamic "do not repeat" line based on what is present
    comps = []
    if include_nl:
        comps.append("the natural language description")
    if include_acsl:
        comps.append("the ACSL")
    comps.append("the extra code")
    if len(comps) == 1:
        dont_repeat = f"Do not repeat {comps[0]}."
    elif len(comps) == 2:
        dont_repeat = f"Do not repeat {comps[0]} or {comps[1]}."
    else:
        dont_repeat = f"Do not repeat {', '.join(comps[:-1])}, or {comps[-1]}."
    rules_array.append(dont_repeat)

    rules_array.append("Do not add explanations or comments.")

    if not allow_loops:
        rules_array.append("Do not use any type of loops (for, while, do-while). Recursion is allowed if needed.")
    return "\n * ".join(rules_array)


def seperate_prompt(prompt):
    return prompt.split("-----END_ASSISTANT_INFORMATION-----")
