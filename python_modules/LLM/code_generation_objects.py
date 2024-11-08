
# Class for completion information
class CompletionInformation:
    """Class that contains information about an iteration"""
    def __init__(self, completion_count, prompt, gpt_output, verified, verified_goals, test_information, temperature, info, max_tokens, tokens_used, model, code, feedback):

        # Information about the completion
        self.code_completion_number = completion_count

        # Information about the input
        self.temperature_used = temperature
        self.prompt_used = prompt
        self.max_tokens_used = max_tokens

        # Information about the output
        self.model_used = model
        self.gpt_output = gpt_output
        self.tokens_used = tokens_used
        self.code = code
        self.feedback = feedback

        # Verification and testing information
        self.is_verified = verified
        self.verified_goals_count = verified_goals
        self.test_information = test_information
        self.completion_information = info
        self.verification_time = 0

        # Add the information about the passed percentage of the tests and goals
        try:
            if test_information is not None:
                self.passed_tests_percentage = test_information[-1]["summary"]["pass_rate"]
            else:
                self.passed_tests_percentage = 0
        except:
            print(f"Error: Could not get the percentage of passed tests or verified goals" +
                "Test information: {test_information}, verified goals: {verified_goals})")
            self.passed_tests_percentage = 0

        try:
            if verified_goals is not None:
                total_goals = verified_goals.split("/")[1]
                verified_goals = verified_goals.split("/")[0]
                if int(total_goals) == 0:
                    self.passed_goals_percentage = 0
                else:
                    self.passed_goals_percentage = int(verified_goals) / int(total_goals)
            else:
                self.passed_goals_percentage = 0
        except:
            self.passed_goals_percentage = 0
            print(f"Error: Could not get the percentage of passed tests or verified goals" +
                "Test information: {test_information}, verified goals: {verified_goals})")

    def to_dict(self):
        """ Function that converts the completion information to a dictionary"""
        return {
            "code_completion_number": self.code_completion_number,
            "temperature_used": self.temperature_used,
            "prompt_used": self.prompt_used,
            "max_tokens_used": self.max_tokens_used,
            "model_used": self.model_used,
            "gpt_output": self.gpt_output,
            "tokens_used": self.tokens_used,
            "code": self.code,
            "feedback": self.feedback,
            "is_verified": self.is_verified,
            "verified_goals_count": self.verified_goals_count,
            "test_information": self.test_information,
            "completion_information": self.completion_information,
            "verification_time": self.verification_time,
            "passed_tests_percentage": self.passed_tests_percentage,
            "passed_goals_percentage": self.passed_goals_percentage
        }

# Class for iteration information
class IterationInformation:
    """Class that contains information about the iteration"""
    def __init__(self, iteration, max_completions_used, model):
        self.iteration_number = iteration
        self.is_verified = False
        self.tokens_used_iteration = 0
        self.completions_used = 0
        self.completions = []
        self.max_completions_used = max_completions_used
        self.model_used = model
        self.best_attempt_index = None
        self.best_attempt_feedback = None
        self.best_attempt_code = None
        self.best_attempt_metric_percentage = None

    # Function that adds a completion to the iteration information
    def add_completion(self, completion_information):
        """Function that adds a completion to the iteration information
        Args:
            completion_information: The completion information that is added
        """
        # If attempted to add a completion that would exceed the maximum completions used, then raise an error
        if self.completions_used + 1 > self.max_completions_used:
            raise ValueError("Attempted to add a completion to the iteration information, but the maximum completions used would be exceeded.")

        self.completions.append(completion_information)
        self.tokens_used_iteration += completion_information.tokens_used
        self.completions_used += 1

        # Check if the code is verified
        if completion_information.is_verified:
            self.is_verified = True

        # Get the metric percentage. Priority to tests, then goals
        if completion_information.passed_tests_percentage is not None:
            metric_percentage = completion_information.passed_tests_percentage
        elif completion_information.passed_goals_percentage is not None:
            metric_percentage = completion_information.passed_goals_percentage
        else:
            metric_percentage = 0

        # If the new completion than the best attempt, then update the best attempt
        if self.best_attempt_index is None or metric_percentage > self.best_attempt_metric_percentage:
            self.best_attempt_index = completion_information.code_completion_number
            self.best_attempt_feedback = completion_information.feedback
            self.best_attempt_metric_percentage = completion_information.passed_goals_percentage
            self.best_attempt_code = completion_information.code

    def to_dict(self):
        """ Function that converts the iteration information to a dictionary"""
        return {
            "iteration_number": self.iteration_number,
            "is_verified": self.is_verified,
            "tokens_used_iteration": self.tokens_used_iteration,
            "completions_used": self.completions_used,
            "completions": [completion.to_dict() for completion in self.completions],
            "max_completions_used": self.max_completions_used,
            "model_used": self.model_used,
            "best_attempt_index": self.best_attempt_index,
            "best_attempt_feedback": self.best_attempt_feedback,
            "best_attempt_code": self.best_attempt_code,
            "best_attempt_metric_percentage": self.best_attempt_metric_percentage
        }

# Class for the code generation process
class CodeGenerationProcess:
    """Class that contains the code generation process"""
    def __init__(self, args):
        self.total_completions_requested = 0
        self.total_completions_used = 0
        self.total_tokens_used = 0
        self.max_code_improvement_iterations = args.iterations
        self.initial_code_generation_information = []
        self.code_improvement_information = []
        self.is_verified = False

    # Function that adds the initial code generation information to the code generation process
    def add_initial_code_generation_information(self, initial_code_generation_information):
        """Function that adds the initial code generation information to the code generation process
        Args:
            initial_code_generation_information: The initial code generation 
                information that is added
        """
        self.initial_code_generation_information.append(initial_code_generation_information)

        # Update the total completions requested and used
        self.total_completions_requested += initial_code_generation_information.max_completions_used
        self.total_completions_used += initial_code_generation_information.completions_used
        self.total_tokens_used += initial_code_generation_information.tokens_used_iteration

        # Check if the code is verified
        if initial_code_generation_information.is_verified:
            self.is_verified = True

    def to_dict(self):
        """ Function that converts the code generation process to a dictionary"""
        return {
            "total_completions_requested": self.total_completions_requested,
            "total_completions_used": self.total_completions_used,
            "total_tokens_used": self.total_tokens_used,
            "max_code_improvement_iterations": self.max_code_improvement_iterations,
            "initial_code_generation_information": [info.to_dict() for info in self.initial_code_generation_information],
            "code_improvement_information": [info.to_dict() for info in self.code_improvement_information],
            "is_verified": self.is_verified
        }

     # Function that adds the code improvement information to the code generation process
    def add_code_improvement_information(self, code_improvement_information):
        """Function that adds the code improvement information to the code generation process
        Args:
            code_improvement_information: The code improvement information that is added
        """
        self.code_improvement_information.append(code_improvement_information)

        # Update the total completions requested and used
        self.total_completions_requested += code_improvement_information.max_completions_used
        self.total_completions_used += code_improvement_information.completions_used
        self.total_tokens_used += code_improvement_information.tokens_used_iteration

        # Check if the code is verified
        if code_improvement_information.is_verified:
            self.is_verified = True
