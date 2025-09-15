#include <stdio.h>

// The function declaration
int months_transition(int w1, int w2);

// A structure for the test cases
typedef struct
{
    int w1;
    int w2;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {0, 1, 0},
    {6, 6, 1},
    {5, 1, 1},
    {1, 3, 1},
    {4, 2, 0},
    {6, 5, 0},
    {0, 0, 1},
    {0, 2, 1},
    {0, 3, 1},
    {0, 4, 0},
    {0, 5, 0},
    {0, 6, 0},
    {1, 0, 0},
    {1, 1, 1},
    {1, 2, 0},
    {1, 4, 1},
    {1, 5, 0},
    {1, 6, 0},
    {2, 0, 0},
    {2, 1, 0},
    {2, 2, 1},
    {2, 3, 0},
    {2, 4, 1},
    {2, 5, 1},
    {2, 6, 0},
    {3, 0, 0},
    {3, 1, 0},
    {3, 2, 0},
    {3, 3, 1},
    {3, 4, 0},
    {3, 5, 1},
    {3, 6, 1},
    {4, 0, 1},
    {4, 1, 0},
    {4, 3, 0},
    {4, 5, 0},
    {4, 6, 1},
    {5, 0, 1},
    {5, 2, 0},
    {5, 3, 0},
    {5, 4, 0},
    {5, 5, 1},
    {5, 6, 0},
    {6, 0, 0},
    {6, 1, 1},
    {6, 2, 1},
    {6, 3, 0},
    {6, 4, 0},
    {4, 4, 1},
    {4, 6, 1},
    {0, 0, 1},
    {4, 1, 0},
    {3, 5, 1},
    {1, 4, 1},
    {6, 2, 1},
    {0, 3, 1},
    {5, 6, 0},
    {4, 0, 1},
    {3, 3, 1},
    {2, 4, 1},
    {3, 0, 0},
    {2, 6, 0},
    {3, 4, 0},
    {0, 4, 0},
    {2, 5, 1},
    {3, 6, 1},
    {5, 4, 0},
    {5, 0, 1}
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

// The main function
int main(int argc, char *argv[])
{
    if (argc < 2)
    {
        printf("Usage: %s <output_filename>\n", argv[0]);
        return 1; // Exit with error code if 0 filename is provided
    }

    // File name is taken from command line
    const char *filename = argv[1];

    // Keep track of the amount of passed tests
    int passed = 0;
    FILE *file = fopen(filename, "w"); // Open the file specified by command line for writing

    if (file == NULL)
    {
        printf("Failed to open file: %s\n", filename);
        return 1; // Exit with error code if file can0t be opened
    }

    // Start JSON array
    fprintf(file, "[\n");

    // For each test case try the function
    for (int i = 0; i < num_tests; i++)
    {
        // Create variables to store the output
        int out;

        // Run the function
        out = months_transition(tests[i].w1, tests[i].w2);

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
        fprintf(file, "        \"inputs\": {\"w1\": %d, \"w2\": %d},\n", tests[i].w1, tests[i].w2);
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