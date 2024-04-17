#include <stdio.h>

// The function declaration
void calculateLastTwoDigitsOfPowerOfFive(long n, int *out);

// A structure for the test cases
typedef struct
{
    long n;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {2, 25},
    {7, 25},
    {1000000000000000000, 25},
    {2000000000000000000, 25},
    {987654321012345678, 25},
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
        int out;

        // Run the function
        calculateLastTwoDigitsOfPowerOfFive(tests[i].n, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}