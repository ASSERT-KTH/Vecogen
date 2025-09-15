
#include <stdio.h>

// The function declaration
int MonthHas31Days(int month);

// A structure for the test cases
typedef struct {
    int x;    // input month
    int out;  // expected output (1 if has 31 days, 0 otherwise)
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1,  1},
    {2,  0},
    {3,  1},
    {4,  0},
    {5,  1},
    {6,  0},
    {7,  1},
    {8,  1},
    {9,  0},
    {10, 1},
    {11, 0},
    {12, 1},
    // repeats for robustness
    {1,  1},
    {4,  0},
    {6,  0},
    {9,  0},
    {11, 0},
    {2,  0},
    {3,  1},
    {5,  1},
    {7,  1},
    {8,  1},
    {10, 1},
    {12, 1},
    // some more repeats to reach 30
    {1,  1},
    {2,  0},
    {5,  1},
    {8,  1},
    {11, 0},
    {12, 1}
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

// The main function
int main(int argc, char *argv[])
{
    if (argc < 2)
    {
        printf("Usage: %s <output_filename>\n", argv[0]);
        return 1;
    }

    const char *filename = argv[1];
    int passed = 0;
    FILE *file = fopen(filename, "w");
    if (file == NULL)
    {
        printf("Failed to open file: %s\n", filename);
        return 1;
    }

    fprintf(file, "[\n");

    for (int i = 0; i < num_tests; i++)
    {
        int out;

        // Run the function
        out = MonthHas31Days(tests[i].x);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (input=%d, expected=%d, got=%d)\n",
                   i + 1, tests[i].x, tests[i].out, out);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"x\": %d},\n", tests[i].x);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    fprintf(file, "    {\n");
    fprintf(file, "        \"summary\": {\n");
    fprintf(file, "            \"total\": %d,\n", num_tests);
    fprintf(file, "            \"passed\": %d,\n", passed);
    fprintf(file, "            \"failed\": %d,\n", num_tests - passed);
    fprintf(file, "            \"pass_rate\": %.2f\n", (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    fprintf(file, "]\n");
    fclose(file);
    return 0;
}