
#include <stdio.h>
#include <limits.h>

// The function declaration
int kth_element(int arr[], int len, int k);

// A structure for the test cases
typedef struct {
    int arr[5];
    int len;
    int k;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {{1, 0, 0, 0, 0}, 1, 1, 1},
    {{5, 10, 0, 0, 0}, 2, 1, 5},
    {{5, 10, 0, 0, 0}, 2, 2, 10},
    {{0, -1, -2, 0, 0}, 3, 1, 0},
    {{0, -1, -2, 0, 0}, 3, 2, -1},
    {{0, -1, -2, 0, 0}, 3, 3, -2},
    {{100, 200, 300, 400, 0}, 4, 2, 200},
    {{100, 200, 300, 400, 0}, 4, 4, 400},
    {{7, 7, 7, 7, 7}, 5, 3, 7},
    {{INT_MAX, INT_MIN, 0, 0, 0}, 3, 1, INT_MAX},
    {{INT_MAX, INT_MIN, 0, 0, 0}, 3, 2, INT_MIN},
    {{INT_MAX, INT_MIN, 0, 0, 0}, 3, 3, 0},
    {{1, 2, 3, 4, 5}, 5, 5, 5},
    {{1, 2, 3, 4, 5}, 5, 1, 1},
    {{1, 2, 3, 4, 5}, 5, 3, 3},
    {{10, -10, 20, -20, 30}, 5, 2, -10},
    {{10, -10, 20, -20, 30}, 5, 4, -20},
    {{0, 1, 0, 1, 0}, 5, 4, 1},
    {{9, 8, 7, 6, 5}, 5, 5, 5},
    {{9, 8, 7, 6, 5}, 5, 1, 9},
    {{1, 1, 2, 3, 5}, 5, 5, 5},
    {{1, 1, 2, 3, 5}, 5, 3, 2},
    {{2, 4, 6, 8, 10}, 5, 2, 4},
    {{2, 4, 6, 8, 10}, 5, 5, 10},
    {{3, 1, 4, 1, 5}, 5, 4, 1},
    {{3, 1, 4, 1, 5}, 5, 5, 5},
    {{9, 0, 9, 0, 9}, 5, 3, 9},
    {{INT_MIN, INT_MIN, INT_MIN, INT_MIN, INT_MIN}, 5, 5, INT_MIN},
    {{INT_MAX, INT_MAX, INT_MAX, INT_MAX, INT_MAX}, 5, 3, INT_MAX},
    {{0, 0, 0, 0, 0}, 5, 1, 0}
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
        out = kth_element(tests[i].arr, tests[i].len, tests[i].k);

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
        fprintf(file, "        \"inputs\": {\"arr\": [");
        for (int j = 0; j < tests[i].len; j++)
        {
            if (j > 0) fprintf(file, ", ");
            fprintf(file, "%d", tests[i].arr[j]);
        }
        fprintf(file, "], \"len\": %d, \"k\": %d},\n", tests[i].len, tests[i].k);
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