
#include <stdio.h>
#include <limits.h>

// The function declaration
int CountEqualNumbers(int a, int b, int c);

// A structure for the test cases
typedef struct {
    int a;
    int b;
    int c;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {  1,    2,    3,    1 },
    {  0,    1,    2,    1 },
    { -1,    0,    1,    1 },
    { INT_MAX, 0, INT_MIN, 1 },
    {  1,    1,    1,    3 },
    {  0,    0,    0,    3 },
    { -1,   -1,   -1,    3 },
    { INT_MAX, INT_MAX, INT_MAX, 3 },
    { INT_MIN, INT_MIN, INT_MIN, 3 },
    {  1,    1,    2,    2 },
    {  1,    2,    1,    2 },
    {  2,    1,    1,    2 },
    {  0,    0,    1,    2 },
    {  0,    1,    0,    2 },
    {  1,    0,    0,    2 },
    { -1,   -1,    1,    2 },
    { -1,    1,   -1,    2 },
    {  1,   -1,   -1,    2 },
    {100,  100, -100,   2 },
    {100, -100,  100,   2 },
    {-100,100,   100,   2 },
    {INT_MAX, INT_MAX, INT_MIN, 2 },
    {INT_MAX, INT_MIN, INT_MAX, 2 },
    {INT_MIN, INT_MAX, INT_MIN, 2 },
    {INT_MIN, INT_MIN, INT_MAX, 2 },
    {123, 456, 789,      1 },
    {100, 200, 100,      2 },
    {-100,200, -100,     2 },
    { 50,   60,   70,    1 },
    {-50,   60,   70,    1 }
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
        out = CountEqualNumbers(tests[i].a, tests[i].b, tests[i].c);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (got %d, expected %d)\n",
                   i + 1, out, tests[i].out);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file,
                "        \"inputs\": {\"a\": %d, \"b\": %d, \"c\": %d},\n",
                tests[i].a, tests[i].b, tests[i].c);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    }%s\n", (i < num_tests - 1) ? "," : "");
    }

    // Summary
    fprintf(file, "    ,{\n");
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