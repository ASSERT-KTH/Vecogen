#include <stdio.h>

typedef struct SantaSpot {
    int lane;
    int desk;
    char side;
} SantaSpot;

// The function declaration
struct SantaSpot verify_santa_spot(int n, int m, int k);

// A structure for the test cases
typedef struct
{
    long n;
    int m;
    int k;
    struct SantaSpot out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {4, 3, 9, {2, 2, 'L'}},
    {4, 3, 24, {4, 3, 'R'}},
    {2, 4, 4, {1, 2, 'R'}},
    {3, 10, 24, {2, 2, 'R'}},
    {10, 3, 59, {10, 3, 'L'}},
    {10000, 10000, 160845880, {8043, 2940, 'R'}},
    {1, 1, 1, {1, 1, 'L'}},
    {1, 1, 2, {1, 1, 'R'}},
    {1, 10000, 1, {1, 1, 'L'}},
    {1, 10000, 20000, {1, 10000, 'R'}},
    {10000, 1, 1, {1, 1, 'L'}},
    {10000, 1, 10000, {5000, 1, 'R'}},
    {10000, 1, 20000, {10000, 1, 'R'}},
    {3, 2, 1, {1, 1, 'L'}},
    {3, 2, 2, {1, 1, 'R'}},
    {3, 2, 3, {1, 2, 'L'}},
    {3, 2, 4, {1, 2, 'R'}},
    {3, 2, 5, {2, 1, 'L'}},
    {3, 2, 6, {2, 1, 'R'}},
    {3, 2, 7, {2, 2, 'L'}},
    {3, 2, 8, {2, 2, 'R'}},
    {3, 2, 9, {3, 1, 'L'}},
    {3, 2, 10, {3, 1, 'R'}},
    {3, 2, 11, {3, 2, 'L'}},
    {3, 2, 12, {3, 2, 'R'}},
    {300, 2000, 1068628, {268, 314, 'R'}},
    {300, 2000, 584756, {147, 378, 'R'}},
    {300, 2000, 268181, {68, 91, 'L'}},
    {10000, 9999, 186450844, {9324, 4745, 'R'}},
    {10000, 9999, 197114268, {9857, 6990, 'R'}},
    {10000, 9999, 112390396, {5621, 818, 'R'}},
    {10000, 10000, 1, {1, 1, 'L'}},
    {10000, 10000, 2, {1, 1, 'R'}},
    {10000, 10000, 100000001, {5001, 1, 'L'}},
    {10000, 10000, 199999999, {10000, 10000, 'L'}},
    {10000, 10000, 200000000, {10000, 10000, 'R'}},
    {1, 2, 1, {1, 1, 'L'}},
    {1, 2, 2, {1, 1, 'R'}},
    {1, 2, 3, {1, 2, 'L'}},
    {1, 2, 4, {1, 2, 'R'}},
    {2, 1, 1, {1, 1, 'L'}},
    {2, 1, 2, {1, 1, 'R'}},
    {2, 1, 3, {2, 1, 'L'}},
    {2, 1, 4, {2, 1, 'R'}},
    {4, 3, 7, {2, 1, 'L'}},
    {1, 1, 1, {1, 1, 'L'}},
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
        SantaSpot out;

        // Run the function
        out = verify_santa_spot(tests[i].n, tests[i].m, tests[i].k);

        // Check if the result is correct
        if (out.lane == tests[i].out.lane &&
            out.desk == tests[i].out.desk &&
            out.side == tests[i].out.side)
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
        fprintf(file, "        \"inputs\": {\"n\": %ld, \"m\": %d, \"k\": %d},\n", tests[i].n, tests[i].m, tests[i].k);
        fprintf(file, "        \"expected_output\": {\"lane\": %d, \"desk\": %d, \"side\": \"%c\"},\n",
                tests[i].out.lane, tests[i].out.desk, tests[i].out.side);
        fprintf(file, "        \"received_output\": {\"lane\": %d, \"desk\": %d, \"side\": \"%c\"},\n", 
                out.lane, out.desk, out.side);
        fprintf(file, "        \"passed\": %s\n", (out.lane == tests[i].out.lane &&
                                                out.desk == tests[i].out.desk &&
                                                out.side == tests[i].out.side) ? "true" : "false");
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