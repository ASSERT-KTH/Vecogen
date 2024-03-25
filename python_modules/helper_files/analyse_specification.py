""" Module to analyze the header of a file """
def get_functions(lines):
    """ Get the functions in a C file 
    Args:
        lines: The lines of the file
    Returns:
        A list of tuples with the line number and the function content
        """

    # Get the functions, and store a tuple of line number and function content
    functions = []

    for i, line in enumerate(lines):
        # If the line is a function, store the line number and the function
        if  (line.strip().startswith("void ") or \
            line.strip().startswith("struct ") or \
            line.strip().startswith("bool ") or \
            line.strip().startswith("int ") or \
            line.strip().startswith("double ") or \
            line.strip().startswith("float ") or \
            line.strip().startswith("char ") or \
            line.strip().startswith("long ") or \
            line.strip().startswith("short ") or \
            line.strip().startswith("unsigned ") or \
            line.strip().startswith("signed ") or \
            line.strip().startswith("static ") or \
            line.strip().startswith("ulong ") or \
            line.strip().startswith("uint ")) and \
            "(" in line and ")" in line:

            # Get the function name
            function_code = line.strip().split("(")[0].split(" ")[-1]
            functions.append((i + 1, function_code))
    return functions
