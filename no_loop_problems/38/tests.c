#include <stdio.h>

// The function declaration
void calculateMinimumSquirrelJumps(int n, long *out);

// A structure for the test cases
typedef struct
{
    int n;
    long out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {5, 9},
    {54320, 2950445124},
    {54319, 2950336489},
    {54318, 2950227856},
    {54317, 2950119225},
    {54316, 2950010596},
    {54315, 2949901969},
    {54314, 2949793344},
    {8153, 66438801},
    {51689, 2671545969},
    {16659, 277455649},
    {3, 1},
    {47389, 2245527769},
    {314, 97344},
    {23481, 551263441},
    {20380, 415262884},
    {1994, 3968064},
    {54321, 2950553761},
    {4, 4},
    {6, 16},
    {7, 25},
    {8, 36},
    {9, 49},
    {10, 64},
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
        long out;

        // Run the function
        calculateMinimumSquirrelJumps(tests[i].n, &out);

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
        fprintf(file, "        \"inputs\": {\"n\": %d},\n", tests[i].n);
        fprintf(file, "        \"expected_output\": %ld,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %ld,\n", out);
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