#include <stdio.h>

// The function declaration
void calculateSecondSpellCollisionDistance(double l, double p, double q, double *out);

// A structure for the test cases
typedef struct
{
    double l;
    double p;
    double q;
    double out;
} TestCase;

// The main function
int main()
{
    // Initialize test cases
    TestCase tests[] = {
        {100, 50, 50, 50},
        {199, 60, 40, 119.4},
        {1, 1, 1, 0.5},
        {1, 500, 500, 0.5},
        {1000, 1, 1, 500},
        {1000, 500, 500, 500},
        {987, 1, 3, 246.75},
        {600, 221, 279, 265.2},
    };

    // Get the number of test cases
    int num_tests = sizeof(tests) / sizeof(tests[0]);

    // Keep track of the amount of passed tests
    int passed = 0;

    // For each test case try the function
    for (int i = 0; i < num_tests; i++)
    {
        // Create variables to store the output
        double out;

        // Run the function
        calculateSecondSpellCollisionDistance(tests[i].l, tests[i].p, tests[i].q, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            printf("Test %d passed\n", i);
            passed++;
            printf("passed amount %d\n", passed);
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}