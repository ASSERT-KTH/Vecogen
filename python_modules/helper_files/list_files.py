""" This module contains helper functions to list all the files in a given directory 
    and to get the absolute path to the files"""
import os

def list_files_directory(directory):
    """List all the files in a given directory
    Args:
        directory: The directory to list the files from
    Returns:
        List of files in the directory"""
    return os.listdir(directory)

def get_absolute_path(relative_path):
    """Get the absolute path to a file
    Args:
        relative_path: The relative path to the file
    Returns:
        The absolute path to the file"""
    return os.path.join(os.getcwd(), "..", relative_path)

__all__ = ["list_files_directory", "get_absolute_path"]
