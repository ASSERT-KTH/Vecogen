#include <stdio.h>

typedef struct {
    int different_days;
    int same_days;
} SockDays;
// The function declaration
SockDays calculateHipsterSockDays(int a, int b);

// A structure for the test cases
typedef struct
{
    int a;
    int b;
    int out1;
    int out2;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {3, 1, 1, 1},
    {34, 30, 30, 2},
    {33, 33, 33, 0},
    {100, 45, 45, 27},
    {100, 23, 23, 38},
    {45, 12, 12, 16},
    {1, 1, 1, 0},
    {1, 100, 1, 49},
    {100, 1, 1, 49},
    {68, 59, 59, 4},
    {45, 99, 45, 27},
    {2, 3, 2, 0},
    {99, 100, 99, 0},
    {100, 98, 98, 1},
    {59, 12, 12, 23},
    {86, 4, 4, 41},
    {68, 21, 21, 23},
    {100, 11, 11, 44},
    {100, 10, 10, 45},
    {15, 45, 15, 15},
    {11, 32, 11, 10},
    {34, 96, 34, 31},
    {7, 3, 3, 2},
    {89, 89, 89, 0},
    {100, 100, 100, 0},
    {4, 10, 4, 3},
    {6, 10, 6, 2},
    {6, 11, 6, 2},
    {10, 40, 10, 15},
    {11, 56, 11, 22},
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
        SockDays result;

        // Run the function
        result = calculateHipsterSockDays(tests[i].a, tests[i].b);

        // Check if the result is correct
        if (result.different_days == tests[i].out1 && result.same_days == tests[i].out2)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed\n", i + 1);
        }

        // Print results to the file as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"a\": %d, \"b\": %d},\n", tests[i].a, tests[i].b);
        fprintf(file, "        \"expected_outputs\": {\"out1\": %d, \"out2\": %d},\n", tests[i].out1, tests[i].out2);
        fprintf(file, "        \"received_outputs\": {\"out1\": %d, \"out2\": %d},\n", result.different_days, result.same_days);
        fprintf(file, "        \"passed\": %s\n", (result.different_days == tests[i].out1 && result.same_days == tests[i].out2) ? "true" : "false");
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