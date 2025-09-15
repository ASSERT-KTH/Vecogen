#include <stdio.h>

// The function declaration
int check(int a, int b, int c);

// A structure for the test cases
typedef struct
{
    int a;
    int b;
    int c;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 2, 1, 0},                            // d = 4 - 4 = 0
    {1, 3, 2, 0},                            // d = 9 - 8 = 1
    {1, 0, 1, 1},                            // d = 0 - 4 = -4
    {1, 0, 0, 0},                            // d = 0 - 0 = 0
    {0, 1, 1, 0},                            // d = 1 - 0 = 1
    {0, 0, 1, 0},                            // d = 0 - 0 = 0
    {0, 0, 0, 0},                            // d = 0 - 0 = 0
    {1, -2, 1, 0},                           // d = 4 - 4 = 0
    {1, 5, 6, 0},                            // d = 25 - 24 = 1
    {1, 5, 7, 1},                            // d = 25 - 28 = -3
    {2, 4, 2, 0},                            // d = 16 - 16 = 0
    {2, 4, 3, 1},                            // d = 16 - 24 = -8
    {2, 0, -2, 0},                           // d = 0 - (-16) = 16
    {-1, 2, 1, 0},                           // d = 4 - (-4) = 8
    {-1, 0, 1, 0},                           // d = 0 - (-4) = 4
    {-1, 0, -1, 1},                          // d = 0 - 4 = -4
    {100, 50, 1, 0},                         // d = 2500 - 400 = 2100
    {100, 50, 100, 1},                       // d = 2500 - 40000 = -37500
    {10, 0, 100, 1},                         // d = 0 - 4000 = -4000
    {10, 0, -100, 0},                        // d = 0 - (-4000) = 4000
    {1, 46340, 1, 0},                        // fits in 64-bit long
    {1, 46341, 1, 0},                        // still positive in 64-bit
    {1, 46341, 2, 0},                        // still positive
    {1, 2, 2147483647, 1},                   // d = 4 - 8.589e9 = neg
    {1, -2, 2147483647, 1},                  // d = 4 - 8.589e9 = neg
    {2147483647, 2147483647, 1, 0},          // huge positive
    {2147483647, 0, 1, 1},                   // d = 0 - 8.589e9 = neg
    {2147483647, 1000000000, 1000000000, 1}, // huge negative
    {2, 3, 1, 0},                            // d = 9 - 8 = 1
    {2, 3, 2, 1}                             // d = 9 - 16 = -7
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
        out = check(tests[i].a, tests[i].b, tests[i].c);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (a=%d,b=%d,c=%d): expected %d, got %d\n",
                   i + 1, tests[i].a, tests[i].b, tests[i].c,
                   tests[i].out, out);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file,
                "        \"inputs\": { \"a\": %d, \"b\": %d, \"c\": %d },\n",
                tests[i].a, tests[i].b, tests[i].c);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n",
                (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    // Summary
    fprintf(file, "    {\n");
    fprintf(file, "        \"summary\": {\n");
    fprintf(file, "            \"total\": %d,\n", num_tests);
    fprintf(file, "            \"passed\": %d,\n", passed);
    fprintf(file, "            \"failed\": %d,\n", num_tests - passed);
    fprintf(file, "            \"pass_rate\": %.2f\n",
            (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    fprintf(file, "]\n");
    fclose(file);
    return 0;
}