
#include <stdio.h>

// The function declaration
int ElementAtIndexAfterRotation(const int *l, int len, int n, int index);

// A structure for the test cases
typedef struct {
    int l[10];
    int len;
    int n;
    int index;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    // 1-element array
    {{42},                     1,  0, 0, 42},
    {{42},                     1,  5, 0, 42},
    // 5-element array, no rotation
    {{1,2,3,4,5},              5,  0, 0, 1},
    {{1,2,3,4,5},              5,  0, 4, 5},
    // small rotations
    {{1,2,3,4,5},              5,  1, 0, 5},
    {{1,2,3,4,5},              5,  1, 2, 2},
    {{1,2,3,4,5},              5,  2, 0, 4},
    {{1,2,3,4,5},              5,  2, 4, 3},
    // rotation equal to length
    {{1,2,3,4,5},              5,  5, 3, 4},
    // rotation greater than length
    {{1,2,3,4,5},              5,  7, 1, 5},
    // 3-element array
    {{10,20,30},               3,  3, 1, 20},
    {{10,20,30},               3,  4, 2, 20},
    {{10,20,30},               3,  5, 0, 20},
    {{10,20,30},               3,  2, 2, 10},
    // all-equal elements
    {{5,5,5,5},                4,  3, 2, 5},
    // negative elements
    {{-1,-2,-3,-4},            4,  1, 0, -4},
    {{-1,-2,-3,-4},            4,  3, 1, -3},
    // zeros and ones
    {{0,1,0,1,0},              5,  4, 3, 0},
    // 10-element array
    {{0,1,2,3,4,5,6,7,8,9},   10,  0, 9, 9},
    {{0,1,2,3,4,5,6,7,8,9},   10,  1, 0, 9},
    {{0,1,2,3,4,5,6,7,8,9},   10,  1, 9, 8},
    {{0,1,2,3,4,5,6,7,8,9},   10,  9, 0, 1},
    {{0,1,2,3,4,5,6,7,8,9},   10, 10, 5, 5},
    {{0,1,2,3,4,5,6,7,8,9},   10, 11, 5, 4},
    {{0,1,2,3,4,5,6,7,8,9},   10, 15, 3, 8},
    // 6-element pi prefix
    {{3,1,4,1,5,9},            6,  2, 4, 4},
    {{3,1,4,1,5,9},            6,  8, 0, 5},
    // 2-element array
    {{100,200},                2,  1, 0, 200},
    {{100,200},                2,  1, 1, 100},
    // another 5-element example
    {{7,8,9,10,11},            5,  3, 2, 11}
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
        out = ElementAtIndexAfterRotation(
            tests[i].l,
            tests[i].len,
            tests[i].n,
            tests[i].index
        );

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed: expected %d, got %d\n",
                   i + 1, tests[i].out, out);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"l\": [");
        for (int j = 0; j < tests[i].len; j++) {
            fprintf(file, "%d", tests[i].l[j]);
            if (j + 1 < tests[i].len) fprintf(file, ", ");
        }
        fprintf(file,
                "], \"len\": %d, \"n\": %d, \"index\": %d},\n",
                tests[i].len, tests[i].n, tests[i].index);
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
    fprintf(file, "            \"pass_rate\": %.2f\n", (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    fprintf(file, "]\n");
    fclose(file);
    return 0;
}