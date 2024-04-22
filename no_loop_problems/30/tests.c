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
        {1000, 500, 500, 500},
        {101, 11, 22, 33.6667},
        {987, 1, 3, 246.75},
        {258, 25, 431, 14.1447},
        {979, 39, 60, 385.667},
        {538, 479, 416, 287.935},
        {583, 112, 248, 181.378},
        {978, 467, 371, 545.019},
        {980, 322, 193, 612.738},
        {871, 401, 17, 835.577},
        {199, 60, 40, 119.4},
        {349, 478, 378, 194.886},
        {425, 458, 118, 337.934},
        {919, 323, 458, 380.073},
        {188, 59, 126, 59.9568},
        {644, 428, 484, 302.228},
        {253, 80, 276, 56.8539},
        {745, 152, 417, 199.016},
        {600, 221, 279, 265.2},
        {690, 499, 430, 370.624},
        {105, 68, 403, 15.1592},
        {1, 1, 1, 0.5},
        {762, 462, 371, 422.622},
        {903, 460, 362, 505.328},
        {886, 235, 95, 630.939},
        {655, 203, 18, 601.652},
        {718, 29, 375, 51.5396},
        {296, 467, 377, 163.782},
        {539, 61, 56, 281.017},
        {133, 53, 124, 39.8249},
        {998, 224, 65, 773.536},
        {961, 173, 47, 755.695},
        {1, 1, 500, 0.00199601},
        {285, 468, 62, 251.66},
        {496, 326, 429, 214.167},
        {627, 150, 285, 216.207},
        {961, 443, 50, 863.535},
        {623, 422, 217, 411.433},
        {678, 295, 29, 617.315},
        {1, 500, 1, 0.998004},
        {1, 500, 500, 0.5},
        {1000, 1, 1, 500},
        {1000, 1, 500, 1.99601},
        {1000, 500, 1, 998.004}};

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