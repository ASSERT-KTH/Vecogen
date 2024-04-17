#include <stdio.h>

// The function declaration
void problem(int x, int mode, int *out);

// A structure for the test cases
typedef struct {
    int x;
     int mode;
     int out;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 4, of, week, 52 },
    { 30, of, month, 11 },
    { 17, of, month, 12 },
    { 31, of, month, 7 },
    { 6, of, week, 53 },
    { 1, of, week, 52 },
    { 2, of, week, 52 },
    { 3, of, week, 52 },
    { 5, of, week, 53 },
    { 7, of, week, 52 },
    { 1, of, month, 12 },
    { 2, of, month, 12 },
    { 3, of, month, 12 },
    { 4, of, month, 12 },
    { 5, of, month, 12 },
    { 6, of, month, 12 },
    { 7, of, month, 12 },
    { 8, of, month, 12 },
    { 9, of, month, 12 },
    { 10, of, month, 12 },
    { 11, of, month, 12 },
    { 12, of, month, 12 },
    { 13, of, month, 12 },
    { 14, of, month, 12 },
    { 15, of, month, 12 },
    { 16, of, month, 12 },
    { 18, of, month, 12 },
    { 19, of, month, 12 },
    { 20, of, month, 12 },
    { 21, of, month, 12 },
    { 22, of, month, 12 },
    { 23, of, month, 12 },
    { 24, of, month, 12 },
    { 25, of, month, 12 },
    { 26, of, month, 12 },
    { 27, of, month, 12 },
    { 28, of, month, 12 },
    { 29, of, month, 12 },
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