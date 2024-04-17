#include <stdio.h>

// The function declaration
void calculateCandiesSaved(int x, int mode, int *out);

// A structure for the test cases
typedef struct
{
    int x;
    int mode;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {4, 0, 52},
    {30, 1, 11},
    {17, 1, 12},
    {31, 1, 7},
    {6, 0, 53},
    {1, 0, 52},
    {2, 0, 52},
    {3, 0, 52},
    {5, 0, 53},
    {7, 0, 52},
    {1, 1, 12},
    {2, 1, 12},
    {3, 1, 12},
    {4, 1, 12},
    {5, 1, 12},
    {6, 1, 12},
    {7, 1, 12},
    {8, 1, 12},
    {9, 1, 12},
    {10, 1, 12},
    {11, 1, 12},
    {12, 1, 12},
    {13, 1, 12},
    {14, 1, 12},
    {15, 1, 12},
    {16, 1, 12},
    {18, 1, 12},
    {19, 1, 12},
    {20, 1, 12},
    {21, 1, 12},
    {22, 1, 12},
    {23, 1, 12},
    {24, 1, 12},
    {25, 1, 12},
    {26, 1, 12},
    {27, 1, 12},
    {28, 1, 12},
    {29, 1, 12},
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
        int x, mode, out;

        // Run the function
        calculateCandiesSaved(tests[i].x, tests[i].mode, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}