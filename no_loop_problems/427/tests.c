#include <stdio.h>

// The function declaration
void calculateNumberOfCalendarColumns(int m, int d, int *out);

// A structure for the test cases
typedef struct
{
    int m;
    int d;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 7, 6},
    {1, 1, 5},
    {11, 6, 5},
    {2, 7, 5},
    {2, 1, 4},
    {8, 6, 6},
    {1, 1, 5},
    {1, 2, 5},
    {1, 3, 5},
    {1, 4, 5},
    {1, 5, 5},
    {1, 6, 6},
    {1, 7, 6},
    {2, 1, 4},
    {2, 2, 5},
    {2, 3, 5},
    {2, 4, 5},
    {2, 5, 5},
    {2, 6, 5},
    {2, 7, 5},
    {3, 1, 5},
    {3, 2, 5},
    {3, 3, 5},
    {3, 4, 5},
    {3, 5, 5},
    {3, 6, 6},
    {3, 7, 6},
    {4, 1, 5},
    {4, 2, 5},
    {4, 3, 5},
    {4, 4, 5},
    {4, 5, 5},
    {4, 6, 5},
    {4, 7, 6},
    {5, 1, 5},
    {5, 2, 5},
    {5, 3, 5},
    {5, 4, 5},
    {5, 5, 5},
    {5, 6, 6},
    {5, 7, 6},
    {6, 1, 5},
    {6, 2, 5},
    {6, 3, 5},
    {6, 4, 5},
    {6, 5, 5},
    {6, 6, 5},
    {6, 7, 6},
    {7, 1, 5},
    {7, 2, 5},
    {7, 3, 5},
    {7, 4, 5},
    {7, 5, 5},
    {7, 6, 6},
    {7, 7, 6},
    {8, 1, 5},
    {8, 2, 5},
    {8, 3, 5},
    {8, 4, 5},
    {8, 5, 5},
    {8, 6, 6},
    {8, 7, 6},
    {9, 1, 5},
    {9, 2, 5},
    {9, 3, 5},
    {9, 4, 5},
    {9, 5, 5},
    {9, 6, 5},
    {9, 7, 6},
    {10, 1, 5},
    {10, 2, 5},
    {10, 3, 5},
    {10, 4, 5},
    {10, 5, 5},
    {10, 6, 6},
    {10, 7, 6},
    {11, 1, 5},
    {11, 2, 5},
    {11, 3, 5},
    {11, 4, 5},
    {11, 5, 5},
    {11, 6, 5},
    {11, 7, 6},
    {12, 1, 5},
    {12, 2, 5},
    {12, 3, 5},
    {12, 4, 5},
    {12, 5, 5},
    {12, 6, 6},
    {12, 7, 6},
    {1, 4, 5},
    {1, 5, 5},
    {9, 7, 6},
    {2, 6, 5},
    {1, 6, 6},
    {2, 2, 5},
    {4, 7, 6},
    {12, 6, 6},
    {12, 3, 5},
    {3, 6, 6},
    {9, 6, 5},
    {7, 6, 6},
    {11, 7, 6},
    {6, 6, 5},
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
        calculateNumberOfCalendarColumns(tests[i].m, tests[i].d, &out);

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
        fprintf(file, "        \"inputs\": {\"m\": %d, \"d\": %d},\n", tests[i].m, tests[i].d);
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