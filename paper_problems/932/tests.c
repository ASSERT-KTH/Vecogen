#include <stdio.h>

// The function declaration
void calculateMinimumExamsToResitForGivenSum(int n, int k, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int k;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {4, 8, 4},
    {4, 10, 2},
    {1, 3, 0},
    {1, 2, 1},
    {4, 9, 3},
    {50, 234, 0},
    {50, 100, 50},
    {50, 250, 0},
    {29, 116, 0},
    {20, 69, 0},
    {46, 127, 11},
    {3, 7, 2},
    {36, 99, 9},
    {45, 104, 31},
    {13, 57, 0},
    {25, 106, 0},
    {8, 19, 5},
    {20, 69, 0},
    {13, 32, 7},
    {47, 128, 13},
    {17, 73, 0},
    {3, 7, 2},
    {16, 70, 0},
    {1, 5, 0},
    {38, 137, 0},
    {7, 20, 1},
    {1, 5, 0},
    {36, 155, 0},
    {5, 15, 0},
    {27, 75, 6},
    {21, 73, 0},
    {2, 5, 1},
    {49, 177, 0},
    {7, 20, 1},
    {44, 173, 0},
    {49, 219, 0},
    {16, 70, 0},
    {10, 28, 2},
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
        calculateMinimumExamsToResitForGivenSum(tests[i].n, tests[i].k, &out);

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
        fprintf(file, "        \"inputs\": {\"n\": %d, \"k\": %d},\n", tests[i].n, tests[i].k);
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