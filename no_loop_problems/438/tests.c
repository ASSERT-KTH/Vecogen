#include <stdio.h>

// The function declaration
void calculateMinimumFlagstonesNeeded(int n, int m, long a, long *out);

// A structure for the test cases
typedef struct {
    int n;
     int m;
     long a;
     long out;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 6, 6, 4, 4 },
    { 1, 1, 1, 1 },
    { 2, 1, 1, 2 },
    { 1, 2, 1, 2 },
    { 2, 2, 1, 4 },
    { 2, 1, 2, 1 },
    { 1, 1, 3, 1 },
    { 2, 3, 4, 1 },
    { 1000000000, 1000000000, 1, 1000000000000000000 },
    { 12, 13, 4, 12 },
    { 222, 332, 5, 3015 },
    { 1000, 1000, 10, 10000 },
    { 1001, 1000, 10, 10100 },
    { 100, 10001, 1000000000, 1 },
    { 1000000000, 1000000000, 1000000000, 1 },
    { 1000000000, 1000000000, 999999999, 4 },
    { 1000000000, 1000000000, 192, 27126743055556 },
    { 1000000000, 987654321, 1, 987654321000000000 },
    { 456784567, 1000000000, 51, 175618850864484 },
    { 39916800, 134217728, 40320, 3295710 },
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