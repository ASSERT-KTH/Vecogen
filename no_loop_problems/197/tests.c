#include <stdio.h>

// The function declaration
void findNthDigitInSequence(int n, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {3, 3},
    {11, 0},
    {12, 1},
    {13, 1},
    {29, 9},
    {30, 2},
    {1000, 3},
    {999, 9},
    {100, 5},
    {123, 6},
    {8, 8},
    {157, 3},
    {289, 1},
    {179, 4},
    {942, 0},
    {879, 9},
    {394, 1},
    {423, 7},
    {952, 3},
    {121, 5},
    {613, 2},
    {945, 1},
    {270, 6},
    {781, 2},
    {453, 7},
    {171, 0},
    {643, 2},
    {570, 6},
    {750, 6},
    {500, 0},
    {2, 2},
    {1, 1},
    {108, 5},
    {500, 0},
    {189, 9},
    {491, 0},
    {191, 0},
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

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
        findNthDigitInSequence(tests[i].n, &out);

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
        fprintf(file, "        \"inputs\": {\"n\": %d},\n", tests[i].n);
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