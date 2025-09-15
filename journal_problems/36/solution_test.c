
#include <stdio.h>

// The function declaration
char shift_minus32(char c);

// A structure for the test cases
typedef struct {
    int x;    // input value (0..127)
    int out;  // expected output (0..127)
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {0,   96},
    {1,   97},
    {2,   98},
    {10, 106},
    {15, 111},
    {30, 126},
    {31, 127},
    {32,   0},
    {33,   1},
    {45,  13},
    {50,  18},
    {63,  31},
    {64,  32},
    {65,  33},
    {76,  44},
    {89,  57},
    {95,  63},
    {96,  64},
    {100, 68},
    {110, 78},
    {120, 88},
    {127, 95},
    {3,   99},
    {4,  100},
    {29, 125},
    {34,   2},
    {59,  27},
    {90,  58},
    {115, 83},
    {13, 109}
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
        out = (int)shift_minus32((char)tests[i].x);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed\n", i + 1);
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
