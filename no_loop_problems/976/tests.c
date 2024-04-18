#include <stdio.h>

// The function declaration
void divideFibonacciNumberByThreeFibonacciNumbers(int n, int *out1, int *out2, int *out3);

// A structure for the test cases
typedef struct
{
    int n;
    int out1;
    int out2;
    int out3;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {0, 0, 0, 0},
    {0, 0, 0, 0},
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

// The main function
int main()
{
    // Keep track of the amount of passed tests
    int passed = 0;

    // For each test case try the function
    for (int i = 0; i < num_tests; i++)
    {
        // Create variables to store the output
        int out1, out2, out3;

        // Run the function
        divideFibonacciNumberByThreeFibonacciNumbers(tests[i].n, &out1, &out2, &out3);

        // Check if the result is correct
        if (out1 == tests[i].out1 && out2 == tests[i].out2 && out3 == tests[i].out3)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}