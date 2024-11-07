#include <stdio.h>

// The function declaration
void calculateMinimumBrainsForStrategy(int N, int *out);

// A structure for the test cases
typedef struct
{
    int N;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 1},
    {4, 2},
    {2, 1},
    {3, 2},
    {5, 3},
    {6, 3},
    {7, 4},
    {8, 4},
    {9, 5},
    {10, 5},
    {11, 6},
    {12, 6},
    {13, 7},
    {14, 7},
    {15, 8},
    {16, 8},
    {17, 9},
    {18, 9},
    {19, 10},
    {20, 10},
    {100, 50},
    {9999, 5000},
    {21736, 10868},
    {873467, 436734},
    {4124980, 2062490},
    {536870910, 268435455},
    {536870912, 268435456},
    {876543210, 438271605},
    {987654321, 493827161},
    {1000000000, 500000000},
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
        calculateMinimumBrainsForStrategy(tests[i].N, &out);

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
        fprintf(file, "        \"inputs\": {\"N\": %d},\n", tests[i].N);
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