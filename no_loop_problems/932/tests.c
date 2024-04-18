#include <stdio.h>

// The function declaration
void calculateMinimumExamsToResitForGivenSum(int n, int k, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int k;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {4, 8, 4},
    {4, 10, 2},
    {1, 3, 0},
    {1, 2, 1},
    {4, 9, 3},
    {50, 234, 0},
    {50, 100, 50},
    {50, 250, 0},
    {29, 116, 0},
    {20, 69, 0},
    {46, 127, 11},
    {3, 7, 2},
    {36, 99, 9},
    {45, 104, 31},
    {13, 57, 0},
    {25, 106, 0},
    {8, 19, 5},
    {20, 69, 0},
    {13, 32, 7},
    {47, 128, 13},
    {17, 73, 0},
    {3, 7, 2},
    {16, 70, 0},
    {1, 5, 0},
    {38, 137, 0},
    {7, 20, 1},
    {1, 5, 0},
    {36, 155, 0},
    {5, 15, 0},
    {27, 75, 6},
    {21, 73, 0},
    {2, 5, 1},
    {49, 177, 0},
    {7, 20, 1},
    {44, 173, 0},
    {49, 219, 0},
    {16, 70, 0},
    {10, 28, 2},
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
        calculateMinimumExamsToResitForGivenSum(tests[i].n, tests[i].k, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}