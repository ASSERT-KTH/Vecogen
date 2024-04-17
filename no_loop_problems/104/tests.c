#include <stdio.h>

// The function declaration
void calculateMaxSurvivalTime(int d, int L, int v1, int v2, int *out);

// A structure for the test cases
typedef struct
{
    int d;
    int L;
    int v1;
    int v2;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {2, 6, 2, 2, 1.00000000000000000000},
    {1, 10000, 1, 1, 4999.50000000000000000000},
    {9999, 10000, 10000, 10000, 0.00005000000000000000},
    {2173, 2176, 10000, 9989, 0.00015008254539996998},
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
        calculateMaxSurvivalTime(tests[i].d, tests[i].L, tests[i].v1, tests[i].v2, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}