#include <stdio.h>

// The function declaration
void findVasyasFinalEntrance(int n, int a, int b, int *out);

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
    {6, 2, -5, 3},
    {5, 1, 3, 4},
    {3, 2, 7, 3},
    {1, 1, 0, 1},
    {1, 1, -1, 1},
    {1, 1, 1, 1},
    {100, 1, -1, 100},
    {100, 54, 100, 54},
    {100, 37, -100, 37},
    {99, 41, 0, 41},
    {97, 37, -92, 42},
    {99, 38, 59, 97},
    {35, 34, 1, 35},
    {48, 1, -1, 48},
    {87, 65, -76, 76},
    {76, 26, 29, 55},
    {100, 65, 0, 65},
    {2, 1, 100, 1},
    {3, 2, -100, 1},
    {1, 1, 100, 1},
    {1, 1, -100, 1},
    {3, 1, -100, 3},
    {4, 3, -100, 3},
    {3, 2, -12, 2},
    {2, 2, -100, 2},
    {3, 2, -90, 2},
    {6, 2, -10, 4},
    {3, 3, -100, 2},
    {5, 2, 4, 1},
    {6, 4, 5, 3},
    {3, 2, -6, 2},
    {5, 1, -99, 2},
    {6, 2, 5, 1},
    {10, 1, -100, 1},
    {2, 2, 1, 1},
    {3, 3, 1, 1},
    {6, 4, 4, 2},
    {17, 17, 2, 2},
    {6, 6, 1, 1},
    {5, 3, -2, 1},
    {6, 2, -100, 4},
    {5, 3, -100, 3},
    {5, 4, 3, 2},
    {3, 2, 2, 1},
    {5, 5, 2, 2},
    {3, 2, 5, 1},
    {5, 5, -1, 4},
    {5, 3, 3, 1},
    {4, 2, 3, 1},
    {88, 76, 74, 62},
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
        findVasyasFinalEntrance(tests[i].n, tests[i].a, tests[i].b, &out);

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