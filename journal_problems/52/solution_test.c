#include <stdio.h>

// The function declaration
int minWalkingDistance(int d1, int d2, int d3);

// A structure for the test cases
typedef struct
{
    int d1;
    int d2;
    int d3;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {10, 20, 30, 60},
    {1, 1, 5, 4},
    {100, 33, 34, 134},
    {777, 777, 777, 2331},
    {2, 2, 8, 8},
    {12, 34, 56, 92},
    {789, 101112, 131415, 203802},
    {27485716, 99999999, 35182, 55041796},
    {1, 293548, 5, 12},
    {12059, 259855, 5874875, 543828},
    {46981, 105809, 585858, 305580},
    {9889, 1221, 2442, 7326},
    {100500, 200600, 300700, 601800},
    {318476, 318476, 318476, 955428},
    {23985, 3353, 75633, 54676},
    {120, 1298, 2222, 2836},
    {98437, 23487, 666672, 243848},
    {100000000, 100000000, 100000000, 300000000},
    {2, 5, 2, 8},
    {1, 1000, 1, 4},
    {1, 100000000, 1, 4},
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
        out = minWalkingDistance(tests[i].d1, tests[i].d2, tests[i].d3);

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
        fprintf(file, "        \"inputs\": {\"n\": %d, \"x\": %d, \"y\": %d},\n", tests[i].d1, tests[i].d2, tests[i].d3);
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