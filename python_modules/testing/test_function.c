#include <stdio.h>

// The function declaration
// ---FUNCTION DECLARATION---

// A structure for the test cases
// ---STRUCTURE FOR TEST CASES---

// Initialize test cases
// ---TEST CASES---

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