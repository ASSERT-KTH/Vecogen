#include <stdio.h>

// The function declaration
void calculateOptimalMeetingPointDistance(int x1, int x2, int x3, int *out);

// A structure for the test cases
typedef struct
{
    int x1;
    int x2;
    int x3;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {7, 1, 4, 6},
    {30, 20, 10, 20},
    {1, 4, 100, 99},
    {100, 1, 91, 99},
    {1, 45, 100, 99},
    {1, 2, 3, 2},
    {71, 85, 88, 17},
    {30, 38, 99, 69},
    {23, 82, 95, 72},
    {22, 41, 47, 25},
    {9, 94, 77, 85},
    {1, 53, 51, 52},
    {25, 97, 93, 72},
    {42, 53, 51, 11},
    {81, 96, 94, 15},
    {21, 5, 93, 88},
    {50, 13, 75, 62},
    {41, 28, 98, 70},
    {69, 46, 82, 36},
    {87, 28, 89, 61},
    {44, 45, 40, 5},
    {86, 97, 68, 29},
    {43, 92, 30, 62},
    {16, 70, 1, 69},
    {40, 46, 19, 27},
    {71, 38, 56, 33},
    {82, 21, 80, 61},
    {75, 8, 35, 67},
    {75, 24, 28, 51},
    {78, 23, 56, 55},
    {85, 31, 10, 75},
    {76, 50, 9, 67},
    {95, 37, 34, 61},
    {84, 61, 35, 49},
    {87, 85, 37, 50},
    {1, 3, 2, 2},
    {4, 2, 6, 4},
    {6, 9, 3, 6},
    {12, 4, 8, 8},
    {15, 10, 5, 10},
    {1, 50, 17, 49},
    {10, 5, 15, 10},
    {8, 1, 9, 8},
    {3, 5, 4, 2},
    {2, 1, 3, 2},
    {1, 8, 2, 7},
    {1, 100, 2, 99},
    {1, 4, 6, 5},
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
        calculateOptimalMeetingPointDistance(tests[i].x1, tests[i].x2, tests[i].x3, &out);

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
        fprintf(file, "        \"inputs\": {\"x1\": %d, \"x2\": %d, \"x3\": %d},\n", tests[i].x1, tests[i].x2, tests[i].x3);
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