
#include <stdio.h>
#include <stddef.h>
#include <limits.h>

// The function declaration
int Max(const int *a, size_t n);

// A structure for the test cases
typedef struct {
    int a[10];
    size_t n;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { { 5 },                                  1,  5 },
    { { -3 },                                 1, -3 },
    { { 0, 1 },                               2,  1 },
    { { 1, 0 },                               2,  1 },
    { { INT_MAX },                            1,  INT_MAX },
    { { INT_MIN },                            1,  INT_MIN },
    { { 3, 3, 3 },                            3,  3 },
    { { -1, -2, -3 },                         3, -1 },
    { { -3, 0, 3 },                           3,  3 },
    { { 1, 2, 3, 4, 5 },                      5,  5 },
    { { 5, 4, 3, 2, 1 },                      5,  5 },
    { { -5, -4, -3, -2, -1 },                 5, -1 },
    { { 2, 9, 7, 9 },                         4,  9 },
    { { INT_MIN, INT_MAX },                   2,  INT_MAX },
    { { 100, 100, 100 },                      3, 100 },
    { { 1, 100, 50, 99 },                     4, 100 },
    { { 1, 2, 2, 1, 2 },                      5,  2 },
    { { 7 },                                  1,  7 },
    { { INT_MAX, 0, -1 },                     3,  INT_MAX },
    { { INT_MIN, -100, -50 },                 3,  -50 },
    { { 0, 0, 0, 0 },                         4,   0 },
    { { 123, 456, 789 },                      3, 789 },
    { { 789, 456, 123 },                      3, 789 },
    { { 5, -5, 5, -5 },                       4,   5 },
    { { 2147483646, 2147483647, 2147483645 }, 3, 2147483647 },
    { { -2147483647, -2147483648 },           2, -2147483647 },
    { { 10, 20, 30, 40, 30, 20, 10 },         7,  40 },
    { { 99, 88, 77, 66, 55 },                 5,  99 },
    { { -10, 10, -10, 10 },                   4,  10 },
    { { 0, -1, 1 },                           3,   1 }
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
        out = Max(tests[i].a, tests[i].n);

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
        fprintf(file, "        \"inputs\": { \"array\": [");
        for (size_t j = 0; j < tests[i].n; j++) {
            fprintf(file, "%d%s", tests[i].a[j],
                    (j + 1 < tests[i].n) ? "," : "");
        }
        fprintf(file, "], \"n\": %zu },\n", tests[i].n);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n",
                (out == tests[i].out) ? "true" : "false");
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
