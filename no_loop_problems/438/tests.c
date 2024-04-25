#include <stdio.h>

// The function declaration
void calculateMinimumFlagstonesNeeded(int n, int m, long a, long *out);

// A structure for the test cases
typedef struct
{
    int n;
    int m;
    long a;
    long out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {6, 6, 4, 4},
    {1, 1, 1, 1},
    {2, 1, 1, 2},
    {1, 2, 1, 2},
    {2, 2, 1, 4},
    {2, 1, 2, 1},
    {1, 1, 3, 1},
    {2, 3, 4, 1},
    {1000000000, 1000000000, 1, 1000000000000000000},
    {12, 13, 4, 12},
    {222, 332, 5, 3015},
    {1000, 1000, 10, 10000},
    {1001, 1000, 10, 10100},
    {100, 10001, 1000000000, 1},
    {1000000000, 1000000000, 1000000000, 1},
    {1000000000, 1000000000, 999999999, 4},
    {1000000000, 1000000000, 192, 27126743055556},
    {1000000000, 987654321, 1, 987654321000000000},
    {456784567, 1000000000, 51, 175618850864484},
    {39916800, 134217728, 40320, 3295710},
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

// The main function
int main(int argc, char *argv[])
{
    if (argc < 2)
    {
        printf("Usage: %s <output_filename>\n", argv[0]);
        return 1; // Exit with error code if no filename is provided
    }

    // File name is taken from command line
    const char *filename = argv[1];

    // Keep track of the amount of passed tests
    int passed = 0;
    FILE *file = fopen(filename, "w"); // Open the file specified by command line for writing

    if (file == NULL)
    {
        printf("Failed to open file: %s\n", filename);
        return 1; // Exit with error code if file cannot be opened
    }

    // Start JSON array
    fprintf(file, "[\n");

    // For each test case try the function
    for (int i = 0; i < num_tests; i++)
    {
        // Create variables to store the output
        long out;

        // Run the function
        calculateMinimumFlagstonesNeeded(tests[i].n, tests[i].m, tests[i].a, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            printf("Test %d passed\n", i);
            passed++;
        }
        else
        {
            printf("Test %d failed\n", i);
        }

        // Print results to the file as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"n\": %d, \"m\": %d, \"a\": %ld},\n", tests[i].n, tests[i].m, tests[i].a);
        fprintf(file, "        \"expected_output\": %ld,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %ld,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    // Add summary to the file
    fprintf(file, "    {\n");
    fprintf(file, "        \"summary\": {\n");
    fprintf(file, "            \"total\": %d,\n", num_tests);
    fprintf(file, "            \"passed\": %d,\n", passed);
    fprintf(file, "            \"failed\": %d,\n", num_tests - passed);
    fprintf(file, "            \"pass_rate\": %.2f\n", (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    // End JSON array
    fprintf(file, "]\n");
    fclose(file);
    return 0;
}