"""This module contains a function to run the Frama-C weakest precondition plugin on a C file"""

import os
import subprocess

def run_frama_c_wpc(file_name):
    """Run the Frama-C weakest precondition plugin on a C file
    Args:
        file_name: The name of the C file to run the plugin on
    Returns:
        None"""
    # Get the current working directory
    cwd = os.getcwd()

    # Set the path to the C file
    path_to_c_file = cwd + "/c_files/" + file_name

    # Set the path to the Frama-C weakest precondition plugin
    path_to_frama_c_wpc = cwd + "/frama-c-wpc/frama-c-wpc.py"

    # Run the Frama-C weakest precondition plugin on the C file
    subprocess.call(["python3", path_to_frama_c_wpc, path_to_c_file])


__all__ = ["run_frama_c_wpc"]
