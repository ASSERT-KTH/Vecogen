#include <stdio.h>

// The function declaration
void findLastDigitOfPower(int n, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 8},
    {2, 4},
    {1000, 6},
    {3, 2},
    {4, 6},
    {1000000000, 6},
    {5, 8},
    {6, 4},
    {999999999, 2},
    {1378, 4},
    {13781378, 4},
    {51202278, 4},
    {999999998, 4},
    {999999997, 8},
    {12193721, 8},
    {0, 1},
    {989898989, 8},
    {7, 2},
    {8, 6},
    {9, 8},
    {10, 4},
    {11, 2},
    {12, 6},
    {13, 8},
    {14, 4},
    {15, 2},
    {16, 6},
    {999999996, 6},
    {999999995, 2},
    {999999994, 4},
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
        findLastDigitOfPower(tests[i].n, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}