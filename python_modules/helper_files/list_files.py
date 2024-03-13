""" This module contains helper functions to list all the files in a given directory 
    and to get the absolute path to the files"""
import os

def list_files_directory(directory):
    """List all the files in a given directory
    Args:
        directory: The directory to list the files from
    Returns:
        List of files in the directory"""
    return [f for f in os.listdir(directory) if os.path.isfile(directory + "/" + f)]

def get_absolute_path(relative_path):
    """Get the absolute path to a file
    Args:
        relative_path: The relative path to the file
    Returns:
        The absolute path to the file"""
    return os.path.join(os.getcwd(), relative_path)

def list_folders_directory(directory):
    """List all the folders in a given directory
    Args:
        directory: The directory to list the folders from
    Returns:
        List of folders in the directory"""
    return [f for f in os.listdir(directory) if os.path.isdir(directory + "/" + f)]