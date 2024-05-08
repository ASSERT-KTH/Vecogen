#include <stdio.h>

// The function declaration
void amountOfDominosFit(int M, int N, int *out);

// A structure for the test cases
typedef struct
{
    int M;
    int N;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {2, 4, 4},
    {3, 3, 4},
    {1, 5, 2},
    {1, 6, 3},
    {1, 15, 7},
    {1, 16, 8},
    {2, 5, 5},
    {2, 6, 6},
    {2, 7, 7},
    {2, 14, 14},
    {2, 15, 15},
    {2, 5, 5},
    {2, 6, 6},
    {2, 7, 7},
    {2, 14, 14},
    {2, 15, 15},
    {1, 4, 2},
    {2, 16, 16},
    {3, 5, 7},
    {3, 6, 9},
    {3, 10, 15},
    {3, 14, 21},
    {3, 15, 22},
    {3, 16, 24},
    {5, 7, 17},
    {16, 16, 128},
    {15, 16, 120},
    {2, 3, 3},
    {15, 15, 112},
    {14, 16, 112},
    {11, 13, 71},
    {5, 16, 40},
    {8, 15, 60},
    {2, 2, 2},
    {3, 4, 6},
    {4, 4, 8},
    {1, 1, 0},
    {1, 2, 1},
    {1, 3, 1},
    {14, 15, 105}};

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
        amountOfDominosFit(tests[i].M, tests[i].N, &out);

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
        fprintf(file, "        \"inputs\": {\n");
        fprintf(file, "            \"M\": %d,\n", tests[i].M);
        fprintf(file, "            \"N\": %d\n", tests[i].N);
        fprintf(file, "        },\n");
        fprintf(file, "        \"expected\": %d,\n", tests[i].out);
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