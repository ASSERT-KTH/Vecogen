""" This module contains a function to parse a C file using the Frama-C parser
    It also contains a function that gets a specific line number in the parsed C file"""

import subprocess
import os
def parse_c_file(c_file_path):
    """Parse a C file using the Frama-C parser
    Args:
        c_file_path: The path to the C file to parse
    Returns:
        The parsed C file"""

    # Run the Frama-C parser on the C file
    output = subprocess.check_output(["frama-c", "-print", c_file_path])

    # Decode the output
    output = output.decode("utf-8")

    # Return the parsed C file
    return output

def get_line_number_in_parsed_code(c_file_path, line_number):
    """Get a specific line number in the parsed C file
    Args:
        c_file_path: The path to the C file to parse
        line_number: The line number to get in the parsed C file
    Returns:
        The line number in the parsed C file"""
    # Read the file
    with open(c_file_path, "r") as file:
        parsed_code_lines = file.readlines()

    # Parse the C file
    #parsed_code = parse_c_file(c_file_path)

    # Split the parsed code by lines
    #parsed_code_lines = parsed_code.split("\n")

    # Get the line number in the parsed code
    line = parsed_code_lines[line_number - 1]

    # Return the line number
    print(f"Could not prove goal with associated line number {line_number}: {line}")
    return line
