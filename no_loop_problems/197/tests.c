#include <stdio.h>

// The function declaration
void findNthDigitInSequence(int n, int *out);

// A structure for the test cases
typedef struct {
    int n;
     int out;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 3, 3 },
    { 11, 0 },
    { 12, 1 },
    { 13, 1 },
    { 29, 9 },
    { 30, 2 },
    { 1000, 3 },
    { 999, 9 },
    { 100, 5 },
    { 123, 6 },
    { 8, 8 },
    { 157, 3 },
    { 289, 1 },
    { 179, 4 },
    { 942, 0 },
    { 879, 9 },
    { 394, 1 },
    { 423, 7 },
    { 952, 3 },
    { 121, 5 },
    { 613, 2 },
    { 945, 1 },
    { 270, 6 },
    { 781, 2 },
    { 453, 7 },
    { 171, 0 },
    { 643, 2 },
    { 570, 6 },
    { 750, 6 },
    { 500, 0 },
    { 2, 2 },
    { 1, 1 },
    { 108, 5 },
    { 500, 0 },
    { 189, 9 },
    { 491, 0 },
    { 191, 0 },
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
        if (out1 == tests[i].out_1 && out2 == tests[i].out_2)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}