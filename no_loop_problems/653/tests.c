#include <stdio.h>

// The function declaration
void convertCentimetersToFeetAndInches(int n, int *out_1, int *out_2);

// A structure for the test cases
typedef struct {
    int n;
     int out_1;
     int out_2;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 42, 1, 2 },
    { 5, 0, 2 },
    { 24, 0, 8 },
    { 1, 0, 0 },
    { 2, 0, 1 },
    { 3, 0, 1 },
    { 4, 0, 1 },
    { 8, 0, 3 },
    { 10, 0, 3 },
    { 12, 0, 4 },
    { 13, 0, 4 },
    { 100, 2, 9 },
    { 120, 3, 4 },
    { 199, 5, 6 },
    { 501, 13, 11 },
    { 1000, 27, 9 },
    { 1233, 34, 3 },
    { 9876, 274, 4 },
    { 9999, 277, 9 },
    { 10000, 277, 9 },
    { 35, 1, 0 },
    { 71, 2, 0 },
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