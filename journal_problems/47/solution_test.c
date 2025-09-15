#include <stdio.h>

// The function declaration
int findLastDigitOfPower(int n);

// A structure for the test cases
typedef struct
{
    int n;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 8},
    {2, 4},
    {1000, 6},
    {3, 2},
    {4, 6},
    {1000000000, 6},
    {5, 8},
    {6, 4},
    {999999999, 2},
    {1378, 4},
    {13781378, 4},
    {51202278, 4},
    {999999998, 4},
    {999999997, 8},
    {12193721, 8},
    {0, 1},
    {989898989, 8},
    {7, 2},
    {8, 6},
    {9, 8},
    {10, 4},
    {11, 2},
    {12, 6},
    {13, 8},
    {14, 4},
    {15, 2},
    {16, 6},
    {999999996, 6},
    {999999995, 2},
    {999999994, 4},
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
        out = findLastDigitOfPower(tests[i].n);

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