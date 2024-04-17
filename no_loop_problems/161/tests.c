#include <stdio.h>

// The function declaration
void findVasyasFinalEntrance(int n, int a, int b, int *out);


// A structure for the test cases
typedef struct {
    int n;
     int a;
     int b;
     int out;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 6, 2, -5, 3 },
    { 5, 1, 3, 4 },
    { 3, 2, 7, 3 },
    { 1, 1, 0, 1 },
    { 1, 1, -1, 1 },
    { 1, 1, 1, 1 },
    { 100, 1, -1, 100 },
    { 100, 54, 100, 54 },
    { 100, 37, -100, 37 },
    { 99, 41, 0, 41 },
    { 97, 37, -92, 42 },
    { 99, 38, 59, 97 },
    { 35, 34, 1, 35 },
    { 48, 1, -1, 48 },
    { 87, 65, -76, 76 },
    { 76, 26, 29, 55 },
    { 100, 65, 0, 65 },
    { 2, 1, 100, 1 },
    { 3, 2, -100, 1 },
    { 1, 1, 100, 1 },
    { 1, 1, -100, 1 },
    { 3, 1, -100, 3 },
    { 4, 3, -100, 3 },
    { 3, 2, -12, 2 },
    { 2, 2, -100, 2 },
    { 3, 2, -90, 2 },
    { 6, 2, -10, 4 },
    { 3, 3, -100, 2 },
    { 5, 2, 4, 1 },
    { 6, 4, 5, 3 },
    { 3, 2, -6, 2 },
    { 5, 1, -99, 2 },
    { 6, 2, 5, 1 },
    { 10, 1, -100, 1 },
    { 2, 2, 1, 1 },
    { 3, 3, 1, 1 },
    { 6, 4, 4, 2 },
    { 17, 17, 2, 2 },
    { 6, 6, 1, 1 },
    { 5, 3, -2, 1 },
    { 6, 2, -100, 4 },
    { 5, 3, -100, 3 },
    { 5, 4, 3, 2 },
    { 3, 2, 2, 1 },
    { 5, 5, 2, 2 },
    { 3, 2, 5, 1 },
    { 5, 5, -1, 4 },
    { 5, 3, 3, 1 },
    { 4, 2, 3, 1 },
    { 88, 76, 74, 62 },
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