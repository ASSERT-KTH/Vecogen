import sys 
def hello_world():
    print("Hello world!")

if __name__ == "__main__":
    # Implemented functions
    imp_functions = ["hello_world"]

    # Get the user input argument
    if len(sys.argv) > 1:
        user_input = sys.argv[1]
    else:
        print("No input arguments, please insert one of the following: ", imp_functions)
        sys.exit()

    # Check if user input is in implemented functions
    if user_input in imp_functions:
        # Call the function
        globals()[user_input]()
    else:
        print("Invalid implemented function, please insert one of the following: ", imp_functions)


