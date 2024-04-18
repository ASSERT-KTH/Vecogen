#include <stdio.h>

// The function declaration
void calculateWaysToGetSecondCardForBlackjack(int n, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {12, 4},
    {20, 15},
    {10, 0},
    {11, 4},
    {15, 4},
    {18, 4},
    {25, 0},
    {22, 0},
    {1, 0},
    {2, 0},
    {3, 0},
    {4, 0},
    {5, 0},
    {6, 0},
    {7, 0},
    {8, 0},
    {9, 0},
    {13, 4},
    {14, 4},
    {16, 4},
    {17, 4},
    {19, 4},
    {21, 4},
    {23, 0},
    {24, 0},
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
        calculateWaysToGetSecondCardForBlackjack(tests[i].n, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}