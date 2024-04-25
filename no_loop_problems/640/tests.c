#include <stdio.h>

// The function declaration
void calculatePossiblePositionsForPetr(int n, int a, int b, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int a;
    int b;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {3, 1, 1, 2},
    {5, 2, 3, 3},
    {5, 4, 0, 1},
    {6, 5, 5, 1},
    {9, 4, 3, 4},
    {11, 4, 6, 7},
    {13, 8, 7, 5},
    {14, 5, 5, 6},
    {16, 6, 9, 10},
    {20, 13, 17, 7},
    {22, 4, 8, 9},
    {23, 8, 14, 15},
    {26, 18, 22, 8},
    {28, 6, 1, 2},
    {29, 5, 23, 24},
    {32, 27, 15, 5},
    {33, 11, 5, 6},
    {37, 21, 15, 16},
    {39, 34, 33, 5},
    {41, 27, 11, 12},
    {42, 25, 16, 17},
    {45, 7, 43, 38},
    {47, 16, 17, 18},
    {49, 11, 37, 38},
    {51, 38, 39, 13},
    {52, 29, 7, 8},
    {56, 43, 12, 13},
    {58, 57, 28, 1},
    {59, 12, 39, 40},
    {62, 9, 52, 53},
    {63, 29, 44, 34},
    {65, 30, 22, 23},
    {66, 27, 38, 39},
    {71, 33, 53, 38},
    {73, 14, 12, 13},
    {73, 37, 35, 36},
    {76, 69, 44, 7},
    {79, 25, 20, 21},
    {81, 60, 20, 21},
    {81, 79, 14, 2},
    {84, 0, 42, 43},
    {88, 79, 8, 9},
    {90, 76, 59, 14},
    {92, 2, 22, 23},
    {94, 5, 88, 89},
    {94, 62, 48, 32},
    {96, 22, 72, 73},
    {100, 11, 88, 89},
    {100, 81, 91, 19},
    {1, 0, 0, 1},
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
        calculatePossiblePositionsForPetr(tests[i].n, tests[i].a, tests[i].b, &out);

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
        fprintf(file, "        \"inputs\": {\"n\": %d, \"a\": %d, \"b\": %d},\n", tests[i].n, tests[i].a, tests[i].b);
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