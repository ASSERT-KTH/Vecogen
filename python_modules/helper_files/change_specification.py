""" This module is to find certain lines in existing code files """

def add_line_in_code(code, line_number, text):
    """Add a line in a code file
    Args:
        file_path: The path to the file
        line_number: The line number to add the line
        text: The text to add"""
    lines = code.split("\n")
    lines.insert(line_number - 1, text)
    return "\n".join(lines)
