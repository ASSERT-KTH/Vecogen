#include <stdio.h>

// The function declaration
int countKingMoves(int col, int row);

// A structure for the test cases
typedef struct
{
    int col;
    int row;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {5, 4, 8},
    {1, 1, 3},
    {8, 8, 3},
    {1, 4, 5},
    {7, 7, 8},
    {5, 1, 5},
    {2, 2, 8},
    {3, 7, 8},
    {8, 6, 5},
    {3, 8, 5},
    {8, 2, 5},
    {8, 5, 5},
    {1, 8, 3},
    {6, 8, 5},
    {8, 1, 3},
    {6, 2, 8},
    {5, 8, 5},
    {8, 3, 5},
    {2, 8, 5},
    {7, 8, 5},
    {4, 8, 5},
    {8, 4, 5},
    {2, 1, 5},
    {1, 2, 5},
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
        out = countKingMoves(tests[i].col, tests[i].row);

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
        fprintf(file, "        \"input\": {\n");
        fprintf(file, "            \"col\": %d,\n", tests[i].col);
        fprintf(file, "            \"row\": %d\n", tests[i].row);
        fprintf(file, "        },\n");
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