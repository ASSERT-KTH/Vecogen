#include <stdio.h>

// The function declaration
void calculateMaximumPresentGivingTimes(int n, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 1},
    {2, 1},
    {3, 2},
    {4, 3},
    {100, 67},
    {101, 67},
    {102, 68},
    {1000000000, 666666667},
    {5, 3},
    {6, 4},
    {999999999, 666666666},
    {999999998, 666666665},
    {999999997, 666666665},
    {999999996, 666666664},
    {999999995, 666666663},
    {999999994, 666666663},
    {999999993, 666666662},
    {999999992, 666666661},
    {999999991, 666666661},
    {1000, 667},
    {10000, 6667},
    {100000, 66667},
    {1000000, 666667},
    {10000000, 6666667},
    {100000000, 66666667},
    {7, 5},
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
        calculateMaximumPresentGivingTimes(tests[i].n, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}