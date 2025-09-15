
#include <stdio.h>
#include <stddef.h>
#include <limits.h>

// The function declaration
// TODO: use the function signature here
int Min(const int *a, size_t n);

// A structure for the test cases
// TODO:: Write a struct called TestCase that has the inputs and outputs of each test case
typedef struct {
    int a[10];
    size_t x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { { 5 },                                    1,  5 },
    { { -3 },                                   1, -3 },
    { { 0 },                                    1,  0 },
    { { 1, 2 },                                 2,  1 },
    { { 2, 1 },                                 2,  1 },
    { { -1, -2 },                               2, -2 },
    { { INT_MAX, INT_MIN },                     2, INT_MIN },
    { { 3, 3, 3 },                              3,  3 },
    { { 5, 4, 6 },                              3,  4 },
    { { -5, 0, 5 },                             3, -5 },
    { { 7, 2, 5, 1 },                           4,  1 },
    { { 1, 2, 3, 4 },                           4,  1 },
    { { 4, 3, 2, 1 },                           4,  1 },
    { { 10, -10, 10, -10 },                     4, -10 },
    { { 100, 100, 99 },                         3,  99 },
    { { 5, 10, 5, 10, 5 },                      5,   5 },
    { { INT_MAX, 0, INT_MIN, -1 },              4, INT_MIN },
    { { 9, 2, 8, 3, 7, 4 },                     6,   2 },
    { { 0, -1, -2, -3, -4 },                    5,  -4 },
    { { 2, 2, 1, 2, 2 },                        5,   1 },
    { { 8, 1, 6, 2, 7, 3, 5, 4 },               8,   1 },
    { { 1, -1, 0, 1, -1 },                      5,  -1 },
    { { 1000, 999, 1001, 998 },                 4,  998 },
    { { INT_MAX, INT_MAX, INT_MAX },            3, INT_MAX },
    { { INT_MIN, INT_MIN },                     2, INT_MIN },
    { { 123, 45, 67, 89, 23, 1 },               6,   1 },
    { { -100, -200, -300, -50 },                4, -300 },
    { { 50, 40, 30, 20, 10, 0, -10 },           7, -10 },
    { { 1, 2, 3, 2, 1, 2, 3 },                  7,   1 },
    { { 5, 3, 5, 3, 5, 3, 5, 3, 5, 3 },        10,   3 }
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
        // TODO: RUN THE FUNCTION
        out = Min(tests[i].a, tests[i].x);

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
        fprintf(file, "        \"inputs\": {\"x\": %zu},\n", tests[i].x);
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
