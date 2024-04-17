#include <stdio.h>

// The function declaration
void calculateMinimumSquirrelJumps(int n, long *out);

// A structure for the test cases
typedef struct
{
    int n;
    long out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {5, 9},
    {3, 1},
    {54321, 2950553761},
    {4, 4},
    {6, 16},
    {7, 25},
    {8, 36},
    {9, 49},
    {10, 64},
    {54320, 2950445124},
    {54319, 2950336489},
    {54318, 2950227856},
    {54317, 2950119225},
    {54316, 2950010596},
    {54315, 2949901969},
    {54314, 2949793344},
    {8153, 66438801},
    {51689, 2671545969},
    {16659, 277455649},
    {47389, 2245527769},
    {314, 97344},
    {23481, 551263441},
    {20380, 415262884},
    {1994, 3968064},
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
        long out;

        // Run the function
        calculateMinimumSquirrelJumps(tests[i].n, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}