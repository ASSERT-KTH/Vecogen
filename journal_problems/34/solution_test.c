
#include <stdio.h>
#include <stdbool.h>
#include <limits.h>

// The function declaration
bool HasOppositeSign(int a, int b);

// A structure for the test cases
typedef struct {
    int a;
    int b;
    bool out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {  1,   1, false },
    { -1,  -1, false },
    {  1,  -1, true  },
    { -1,   1, true  },
    {  0,   0, false },
    {  0,   5, false },
    {  5,   0, false },
    {  0,  -5, false },
    { -5,   0, false },
    {  INT_MAX,  INT_MAX, false },
    {  INT_MIN,  INT_MIN, false },
    {  INT_MAX,  INT_MIN, true  },
    {  INT_MIN,  INT_MAX, true  },
    { 123, -456, true  },
    { -123, 456, true  },
    { 123, 456, false },
    { -123, -456, false },
    { 2147483647, 0, false },
    { -2147483648, 0, false },
    { 100000,    -1, true  },
    { -100000,   1,  true  },
    { 0,         1,  false },
    { 0,        -1,  false },
    { -1,        0,  false },
    { 2,        -3,  true  },
    { -2,        3,  true  },
    { 2,         3,  false },
    { -2,       -3,  false },
    { 100,      100, false },
    { -100,    -100, false }
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
        bool out;

        // Run the function
        out = HasOppositeSign(tests[i].a, tests[i].b);

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
        fprintf(file, "        \"inputs\": {\"a\": %d, \"b\": %d},\n",
                tests[i].a, tests[i].b);
        fprintf(file, "        \"expected_output\": %s,\n",
                tests[i].out ? "true" : "false");
        fprintf(file, "        \"received_output\": %s,\n",
                out ? "true" : "false");
        fprintf(file, "        \"passed\": %s\n",
                (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    // Summary object
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