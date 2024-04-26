#include <stdio.h>

// The function declaration
void convertCentimetersToFeetAndInches(int n, int *out1, int *out2);

// A structure for the test cases
typedef struct
{
    int n;
    int out1;
    int out2;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {42, 1, 2},
    {5, 0, 2},
    {24, 0, 8},
    {1, 0, 0},
    {2, 0, 1},
    {3, 0, 1},
    {4, 0, 1},
    {8, 0, 3},
    {10, 0, 3},
    {12, 0, 4},
    {13, 0, 4},
    {100, 2, 9},
    {120, 3, 4},
    {199, 5, 6},
    {501, 13, 11},
    {1000, 27, 9},
    {1233, 34, 3},
    {9876, 274, 4},
    {9999, 277, 9},
    {10000, 277, 9},
    {35, 1, 0},
    {71, 2, 0},
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
        int out1, out2;

        // Run the function
        convertCentimetersToFeetAndInches(tests[i].n, &out1, &out2);

        // Check if the result is correct
        if (out1 == tests[i].out1 && out2 == tests[i].out2)
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
        fprintf(file, "        \"inputs\": {\"n\": %d},\n", tests[i].n);
        fprintf(file, "        \"expected_output\": {\"feet\": %d, \"inches\": %d},\n", tests[i].out1, tests[i].out2);
        fprintf(file, "        \"received_output\": {\"feet\": %d, \"inches\": %d},\n", out1, out2);
        fprintf(file, "        \"passed\": %s\n", (out1 == tests[i].out1 && out2 == tests[i].out2) ? "true" : "false");
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