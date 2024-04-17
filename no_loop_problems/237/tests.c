#include <stdio.h>

// The function declaration
void calculateMinimumBrainsForStrategy(int N, int *out);


// A structure for the test cases
typedef struct {
    int N;
     int out;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 1, 1 },
    { 4, 2 },
    { 2, 1 },
    { 3, 2 },
    { 5, 3 },
    { 6, 3 },
    { 7, 4 },
    { 8, 4 },
    { 9, 5 },
    { 10, 5 },
    { 11, 6 },
    { 12, 6 },
    { 13, 7 },
    { 14, 7 },
    { 15, 8 },
    { 16, 8 },
    { 17, 9 },
    { 18, 9 },
    { 19, 10 },
    { 20, 10 },
    { 100, 50 },
    { 9999, 5000 },
    { 21736, 10868 },
    { 873467, 436734 },
    { 4124980, 2062490 },
    { 536870910, 268435455 },
    { 536870912, 268435456 },
    { 876543210, 438271605 },
    { 987654321, 493827161 },
    { 1000000000, 500000000 },
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