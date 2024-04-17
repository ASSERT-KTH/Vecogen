#include <stdio.h>

// The function declaration
void divideFibonacciNumberByThreeFibonacciNumbers(int n, int *out_1, int *out_2, int *out_3);


// A structure for the test cases
typedef struct {
    int n;
     int out_1;
     int out_2;
     int out_3;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 0, 0, 0, 0 },
    { 0, 0, 0, 0 },
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