#include <stdio.h>

// The function declaration
int can_reach_treasure(int x1, int y1, int x2, int y2, int x, int y);

// A structure for the test cases
typedef struct
{
    int x1;
    int y1;
    int x2;
    int y2;
    int x;
    int y;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {0, 0, 0, 6, 2, 3, 1},
    {1, 1, 3, 6, 1, 5, 0},
    {5, 4, 6, -10, 1, 1, 0},
    {6, -3, -7, -7, 1, 2, 0},
    {2, -5, -8, 8, 2, 1, 1},
    {70, -81, -17, 80, 87, 23, 1},
    {41, 366, 218, -240, 3456, 1234, 0},
    {-61972, -39646, -42371, -24854, 573, 238, 0},
    {-84870, -42042, 94570, 98028, 8972, 23345, 1},
    {-58533, -50999, -1007, -59169, 8972, 23345, 0},
    {-100000, -100000, 100000, 100000, 100000, 100000, 1},
    {-100000, -100000, 100000, 100000, 1, 1, 1},
    {5, 2, 5, 3, 1, 1, 0},
    {5, 5, 5, 5, 5, 5, 1},
    {0, 0, 1000, 1000, 1, 1, 1},
    {0, 0, 0, 1, 1, 1, 0},
    {1, 1, 4, 4, 2, 2, 0},
    {100000, 100000, 99999, 99999, 100000, 100000, 0},
    {1, 1, 1, 6, 1, 5, 0},
    {2, 9, 4, 0, 2, 3, 1},
    {0, 0, 0, 9, 2, 3, 0},
    {14, 88, 14, 88, 100, 500, 1},
    {-1, 0, 3, 0, 4, 4, 0},
    {0, 0, 8, 9, 2, 3, 0},
    {-2, 5, 7, -6, 1, 1, 1},
    {3, 7, -8, 8, 2, 2, 0},
    {-4, -8, -6, -1, 1, 3, 0},
    {0, 8, 6, 2, 1, 1, 1},
    {-5, -2, -8, -2, 1, 1, 0},
    {1, 4, -5, 0, 1, 1, 1},
    {8, -4, 4, -7, 1, 2, 0},
    {5, 2, 2, 4, 2, 2, 0},
    {2, 0, -4, 6, 1, 2, 0},
    {-2, 6, -5, -4, 1, 2, 1},
    {-6, 5, 10, 6, 2, 4, 0},
    {3, -7, 1, -8, 1, 2, 0},
    {4, 1, 4, -4, 9, 4, 0},
    {9, -3, -9, -3, 2, 2, 0},
    {-6, -6, -10, -5, 6, 7, 0},
    {-5, -2, 2, 2, 1, 7, 0},
    {9, 0, 8, 1, 7, 10, 0},
    {-1, 6, -7, -6, 6, 4, 1},
    {2, 2, -3, -3, 3, 1, 0},
    {2, -6, 7, 2, 2, 1, 0},
    {-6, 2, -7, -7, 1, 2, 0},
    {-5, -5, -1, -5, 2, 2, 1},
    {0, 5, 3, -6, 2, 2, 0},
    {0, -6, 2, -1, 1, 1, 0},
    {-6, 6, -5, -4, 1, 2, 1},
    {7, -7, 1, -7, 2, 2, 0},
    {99966, -99952, -99966, 99923, 1, 1, 0},
    {99921, 99980, -99956, -99907, 3, 4, 0},
    {100000, 100000, -100000, -100000, 1, 1, 1},
    {1, 0, 2, 0, 5, 1, 0},
    {-3, 0, -8, 0, 7, 2, 0},
    {-9, 4, -5, -1, 8, 2, 0},
    {-99999, -100000, 100000, 100000, 1, 1, 0},
    {0, 0, -100, -100, 2, 2, 1},
    {9, -5, -3, -2, 1, 4, 0},
    {1, -10, -10, 5, 7, 5, 0},
    {6, -9, -1, -9, 1, 9, 0}
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
        out = can_reach_treasure(tests[i].x1, tests[i].y1, tests[i].x2, tests[i].y2, tests[i].x, tests[i].y);

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
        fprintf(file, "        \"input\": {\n");
        fprintf(file, "            \"x1\": %d,\n", tests[i].x1);
        fprintf(file, "            \"y1\": %d,\n", tests[i].y1);
        fprintf(file, "            \"x2\": %d,\n", tests[i].x2);
        fprintf(file, "            \"y2\": %d,\n", tests[i].y2);
        fprintf(file, "            \"x\": %d,\n", tests[i].x);
        fprintf(file, "            \"y\": %d\n", tests[i].y);
        fprintf(file, "        },\n");
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