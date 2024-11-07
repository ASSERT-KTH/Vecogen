import json

class CustomJSONEncoder(json.JSONEncoder):
    """ Custom JSON encoder to handle custom objects """
    def default(self, obj):
        if hasattr(obj, 'to_dict'):
            return obj.to_dict()
        return super().default(obj)

# Function to output the results of a code generation process to a file
def output_results(args, results):
    """ Output the results of a code generation process to a file """
    with open(f"{args.absolute_output_directory}/results.txt", "w", encoding="utf-8") as f:
        f.write(json.dumps(results, indent=4, cls=CustomJSONEncoder))
