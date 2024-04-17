#include <stdio.h>

// The function declaration
void calculateMinimumDistanceForShopping(int d1, int d2, int d3, int *out);

// A structure for the test cases
typedef struct {
    int d1;
     int d2;
     int d3;
     int out;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 10, 20, 30, 60 },
    { 1, 1, 5, 4 },
    { 100, 33, 34, 134 },
    { 777, 777, 777, 2331 },
    { 2, 2, 8, 8 },
    { 12, 34, 56, 92 },
    { 789, 101112, 131415, 203802 },
    { 27485716, 99999999, 35182, 55041796 },
    { 1, 293548, 5, 12 },
    { 12059, 259855, 5874875, 543828 },
    { 46981, 105809, 585858, 305580 },
    { 9889, 1221, 2442, 7326 },
    { 100500, 200600, 300700, 601800 },
    { 318476, 318476, 318476, 955428 },
    { 23985, 3353, 75633, 54676 },
    { 120, 1298, 2222, 2836 },
    { 98437, 23487, 666672, 243848 },
    { 100000000, 100000000, 100000000, 300000000 },
    { 2, 5, 2, 8 },
    { 1, 1000, 1, 4 },
    { 1, 100000000, 1, 4 },
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