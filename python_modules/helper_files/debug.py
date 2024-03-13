"""Module for helper files that are used for debugging"""
import os

def clear_debug(args, folder_name):
    """Clear the debugging folders
    Args:
        args: The arguments of the program"""
    if args.debug:
        # Clear the files errors.txt, output_gpt.txt and prompt.txt
        if os.path.exists(folder_name + "/errors.txt"):
            os.remove(folder_name + "/errors.txt")
        if os.path.exists(folder_name + "/output_gpt.txt"):
            os.remove(folder_name + "/output_gpt.txt")
        if os.path.exists(folder_name + "/output.txt"):
            os.remove(folder_name + "/output.txt")
        if os.path.exists(folder_name + "/prompt.txt"):
            os.remove(folder_name + "/prompt.txt")

def debug_to_file(args, folder_name, file_name, text):
    """Write the debugging information to a file
    Args:
        args: The arguments of the program
        folder_name: The name of the folder
        text: The text to write to the file"""
    if args.debug:
        # If the file does not exist then create it
        if not os.path.exists(folder_name):
            os.makedirs(folder_name)

        # Write the text to the file
        with open(folder_name + f"/{file_name}.txt", "a", encoding="utf-8") as file:
            file.write(text + "\n")

__all__ = ["clear_debug", "debug_to_file"]