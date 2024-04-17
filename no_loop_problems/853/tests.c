#include <stdio.h>

// The function declaration
void star(int a, int *out);

// A structure for the test cases
typedef struct {
    int a;
     int out;
} TestCase;


// Initialize test cases
TestCase tests[] = {
    { 2, 13 },
    { 1, 1 },
    { 3, 37 },
    { 4, 73 },
    { 5, 121 },
    { 6, 181 },
    { 7, 253 },
    { 8, 337 },
    { 9, 433 },
    { 15000, 1349910001 },
    { 4845, 140815081 },
    { 6914, 286778893 },
    { 3994, 95688253 },
    { 12504, 938025073 },
    { 13170, 1040614381 },
    { 427, 1091413 },
    { 11877, 846307513 },
    { 3202, 61497613 },
    { 5689, 194154193 },
    { 15302, 1404815413 },
    { 17042, 1742476333 },
    { 1481, 13151281 },
    { 15592, 1458569233 },
    { 16344, 1602659953 },
    { 4222, 106926373 },
    { 11808, 836502337 },
    { 13366, 1071819541 },
    { 3823, 87669037 },
    { 581, 2021881 },
    { 15479, 1437503773 },
    { 6543, 256825837 },
    { 11136, 743996161 },
    { 16331, 1600111381 },
    { 8543, 437845837 },
    { 7530, 340160221 },
    { 3154, 59667373 },
    { 11501, 793569001 },
    { 12038, 869408437 },
    { 13082, 1026753853 },
    { 18257, 1999798753 },
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