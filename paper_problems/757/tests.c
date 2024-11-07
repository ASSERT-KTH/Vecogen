#include <stdio.h>

// The function declaration
void calculateMaximumToastsPerFriend(int n, int k, int l, int c, int d, int p, int nl, int np, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int k;
    int l;
    int c;
    int d;
    int p;
    int nl;
    int np;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {3, 4, 5, 10, 8, 100, 3, 1, 2},
    {5, 100, 10, 1, 19, 90, 4, 3, 3},
    {10, 1000, 1000, 25, 23, 1, 50, 1, 0},
    {1, 7, 4, 5, 5, 8, 3, 2, 4},
    {2, 3, 3, 5, 5, 10, 1, 3, 1},
    {2, 6, 4, 5, 6, 5, 1, 3, 0},
    {1, 7, 3, 5, 3, 6, 2, 1, 6},
    {2, 4, 5, 4, 5, 7, 3, 2, 1},
    {2, 3, 6, 5, 7, 8, 2, 1, 4},
    {1, 4, 5, 5, 3, 10, 3, 1, 6},
    {1, 4, 6, 7, 3, 5, 1, 3, 1},
    {1, 6, 5, 5, 5, 8, 3, 1, 8},
    {1, 7, 5, 3, 3, 9, 2, 1, 9},
    {3, 5, 3, 7, 6, 10, 3, 1, 1},
    {3, 6, 3, 5, 3, 6, 3, 1, 2},
    {1, 7, 5, 5, 5, 5, 2, 2, 2},
    {2, 5, 3, 5, 6, 9, 2, 1, 3},
    {3, 4, 3, 5, 3, 6, 2, 1, 2},
    {1, 5, 5, 4, 7, 6, 3, 1, 6},
    {2, 3, 7, 6, 5, 9, 3, 1, 3},
    {2, 6, 5, 3, 3, 8, 1, 1, 4},
    {2, 4, 7, 3, 4, 10, 2, 1, 5},
    {1, 1000, 1000, 1000, 1000, 1000, 1, 1, 1000},
    {17, 1000, 1000, 1000, 1000, 1000, 3, 7, 8},
    {115, 1000, 1000, 1000, 1000, 1000, 17, 15, 0},
    {1, 587, 981, 1, 2, 1, 1, 1, 1},
    {1, 1, 2, 1, 2, 2, 1, 1, 2},
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
        calculateMaximumToastsPerFriend(tests[i].n, tests[i].k, tests[i].l, tests[i].c, tests[i].d, tests[i].p, tests[i].nl, tests[i].np, &out);

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
        fprintf(file, "        \"inputs\": {\"n\": %d, \"k\": %d, \"l\": %d, \"c\": %d, \"d\": %d, \"p\": %d, \"nl\": %d, \"np\": %d},\n", tests[i].n, tests[i].k, tests[i].l, tests[i].c, tests[i].d, tests[i].p, tests[i].nl, tests[i].np);
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