#include <stdio.h>

// The function declaration
void calculateHipsterSockDays(int a, int b, int *out1, int *out2);

// A structure for the test cases
typedef struct
{
    int a;
    int b;
    int out1;
    int out2;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {3, 1, 1, 1},
    {2, 3, 2, 0},
    {7, 3, 3, 2},
    {100, 100, 100, 0},
    {4, 10, 4, 3},
    {6, 10, 6, 2},
    {6, 11, 6, 2},
    {10, 40, 10, 15},
    {11, 56, 11, 22},
    {34, 30, 30, 2},
    {33, 33, 33, 0},
    {100, 45, 45, 27},
    {100, 23, 23, 38},
    {45, 12, 12, 16},
    {1, 1, 1, 0},
    {1, 100, 1, 49},
    {100, 1, 1, 49},
    {68, 59, 59, 4},
    {45, 99, 45, 27},
    {99, 100, 99, 0},
    {100, 98, 98, 1},
    {59, 12, 12, 23},
    {86, 4, 4, 41},
    {68, 21, 21, 23},
    {100, 11, 11, 44},
    {100, 10, 10, 45},
    {15, 45, 15, 15},
    {11, 32, 11, 10},
    {34, 96, 34, 31},
    {89, 89, 89, 0},
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
        int out1, out2;

        // Run the function
        calculateHipsterSockDays(tests[i].a, tests[i].b, &out1, &out2);

        // Check if the result is correct
        if (out1 == tests[i].out1 && out2 == tests[i].out2)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}