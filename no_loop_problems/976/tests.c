#include <stdio.h>

// The function declaration
void divideFibonacciNumberByThreeFibonacciNumbers(int n, int *out1, int *out2, int *out3);

// A structure for the test cases
typedef struct
{
    int n;
    int out1;
    int out2;
    int out3;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {3, 0, 1, 2},
    {2, 0, 1, 1},
    {3, 0, 1, 2},
    {5, 0, 2, 3},
    {8, 0, 3, 5},
    {13, 0, 5, 8},
    {21, 0, 8, 13},
    {34, 0, 13, 21},
    {55, 0, 21, 34},
    {89, 0, 34, 55},
    {144, 0, 55, 89},
    {13, 0, 5, 8},
    {233, 0, 89, 144},
    {377, 0, 144, 233},
    {610, 0, 233, 377},
    {987, 0, 377, 610},
    {1597, 0, 610, 987},
    {2584, 0, 987, 1597},
    {4181, 0, 1597, 2584},
    {6765, 0, 2584, 4181},
    {10946, 0, 4181, 6765},
    {17711, 0, 6765, 10946},
    {0, 0, 0, 0},
    {28657, 0, 10946, 17711},
    {46368, 0, 17711, 28657},
    {75025, 0, 28657, 46368},
    {121393, 0, 46368, 75025},
    {196418, 0, 75025, 121393},
    {317811, 0, 121393, 196418},
    {514229, 0, 196418, 317811},
    {832040, 0, 317811, 514229},
    {1346269, 0, 514229, 832040},
    {2178309, 0, 832040, 1346269},
    {1, 0, 0, 1},
    {3524578, 0, 1346269, 2178309},
    {5702887, 0, 2178309, 3524578},
    {9227465, 0, 3524578, 5702887},
    {14930352, 0, 5702887, 9227465},
    {24157817, 0, 9227465, 14930352},
    {39088169, 0, 14930352, 24157817},
    {63245986, 0, 24157817, 39088169},
    {102334155, 0, 39088169, 63245986},
    {165580141, 0, 63245986, 102334155},
    {267914296, 0, 102334155, 165580141},
    {2, 0, 1, 1},
    {433494437, 0, 165580141, 267914296},
    {701408733, 0, 267914296, 433494437},
    {701408733, 0, 267914296, 433494437},
    {102334155, 0, 39088169, 63245986},
    {63245986, 0, 24157817, 39088169},
    {1597, 0, 610, 987},
    {0, 0, 0, 0},
    {1, 0, 0, 1},
    {1, 0, 0, 1},
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
        int out1, out2, out3;

        // Run the function
        divideFibonacciNumberByThreeFibonacciNumbers(tests[i].n, &out1, &out2, &out3);

        // Check if the result is correct
        if (out1 == tests[i].out1 && out2 == tests[i].out2 && out3 == tests[i].out3)
        {
            passed++;
        }
    }
    printf("\nPassed %d out of %d tests.\n", passed, num_tests);
    return 0;
}