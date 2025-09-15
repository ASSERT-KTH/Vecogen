#include <stdio.h>

// The function declaration
int count_candies(int day, int mode);

// A structure for the test cases
typedef struct
{
    long day;
    int mode;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {4, 0, 52},
    {30, 1, 11},
    {17, 1, 12},
    {31, 1, 7},
    {6, 0, 53},
    {1, 0, 52},
    {2, 0, 52},
    {3, 0, 52},
    {5, 0, 53},
    {7, 0, 52},
    {1, 1, 12},
    {2, 1, 12},
    {3, 1, 12},
    {4, 1, 12},
    {5, 1, 12},
    {6, 1, 12},
    {7, 1, 12},
    {8, 1, 12},
    {9, 1, 12},
    {10, 1, 12},
    {11, 1, 12},
    {12, 1, 12},
    {13, 1, 12},
    {14, 1, 12},
    {15, 1, 12},
    {16, 1, 12},
    {18, 1, 12},
    {19, 1, 12},
    {20, 1, 12},
    {21, 1, 12},
    {22, 1, 12},
    {23, 1, 12},
    {24, 1, 12},
    {25, 1, 12},
    {26, 1, 12},
    {27, 1, 12},
    {28, 1, 12},
    {29, 1, 12}
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
        out = count_candies(tests[i].day, tests[i].mode);

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
        fprintf(file, "        \"inputs\": {\"day\": %ld, \"mode\": %d},\n", tests[i].day, tests[i].mode);
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