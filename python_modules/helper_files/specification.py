""" This module contains the functions that help with the specification handling in the tool. """
import os, re

def _read_if(path):
    if path and os.path.isfile(path):
        with open(path, "r", encoding="utf-8") as f:
            return f.read()
    return ""

def _wrap_c_comment(txt: str) -> str:
    t = (txt or "").strip()
    if not t:
        return ""
    # strip markdown fences if present
    if t.startswith("```"):
        t = re.sub(r"^```[^\n]*\n", "", t, flags=re.DOTALL)
        if t.endswith("```"):
            t = t[:-3]
        t = t.strip()
    if t.startswith("/*") and t.endswith("*/"):
        return t
    return "/*\n" + t + "\n*/"

def add_specifications_to_code(
    absolute_formal_specification_path: str,
    absolute_natural_language_path: str,
    absolute_function_signature_path: str,
    absolute_extra_code_path: str,
    code: str,
):
    """Prepend (optional) NL as C comment + formal ACSL + opened signature + (optional) extras; append BODY."""
    parts = []

    # extras (typedefs/includes) live outside the function
    extra_code = _read_if(absolute_extra_code_path)
    if extra_code.strip():
        parts.append(extra_code.strip())

    # NL as comment (optional)
    nl_code = _read_if(absolute_natural_language_path)
    if nl_code.strip():
        parts.append(_wrap_c_comment(nl_code))

    # formal spec (required)
    formal_code = _read_if(absolute_formal_specification_path)
    if formal_code.strip():
        parts.append(formal_code.strip())

    # function signature opened with '{'
    with open(absolute_function_signature_path, "r", encoding="utf-8") as f:
        sig_code = f.read()
    idx = sig_code.rfind(";")
    if idx != -1:
        sig_open = sig_code[:idx] + " {\n" + sig_code[idx+1:]
    elif "{" in sig_code:
        sig_open = sig_code
    else:
        sig_open = sig_code.rstrip() + " {\n"
    parts.append(sig_open.rstrip())

    # header block (outside function), then append model BODY later
    problem_description = "\n\n".join(parts) + "\n"

    # Strip model’s own header (and lone '{') so we don’t duplicate
    lines = code.splitlines()
    sig_re = re.compile(r'^\s*[_a-zA-Z][\w\s\*\[\]]+\s+[_a-zA-Z]\w*\s*\([^;{]*\)\s*[{]?\s*$')
    start = None
    for i, ln in enumerate(lines):
        if sig_re.match(ln):
            start = i
            break
    if start is not None:
        j = start + 1
        while j < len(lines) and not lines[j].strip():
            j += 1
        if j < len(lines) and lines[j].strip() == "{":
            j += 1
        body = "\n".join(lines[j:])
    else:
        body = "\n".join(lines)

    return problem_description + body.rstrip() + "\n"
