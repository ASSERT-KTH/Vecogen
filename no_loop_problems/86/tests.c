#include <stdio.h>

// The function declaration
void calculateMinimumElephantSteps(int x, int *out);

// A structure for the test cases
typedef struct
{
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {5, 1},
    {534204, 106841},
    {469569, 93914},
    {502877, 100576},
    {942212, 188443},
    {97, 20},
    {53, 11},
    {89, 18},
    {574, 115},
    {716, 144},
    {729, 146},
    {12, 3},
    {8901, 1781},
    {3645, 729},
    {4426, 886},
    {46573, 9315},
    {86380, 17276},
    {94190, 18838},
    {999990, 199998},
    {999991, 199999},
    {999992, 199999},
    {999993, 199999},
    {999999, 200000},
    {999994, 199999},
    {999995, 199999},
    {999996, 200000},
    {999997, 200000},
    {999998, 200000},
    {41, 9},
    {1000000, 200000},
    {1, 1},
    {2, 1},
    {3, 1},
    {4, 1},
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
        int out;

        // Run the function
        calculateMinimumElephantSteps(tests[i].x, &out);

        // Check if the result is correct
        if (out == tests[i].out)
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
        fprintf(file, "        \"inputs\": {\"x\": %d},\n", tests[i].x);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
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