
#include <stdio.h>
#include <limits.h>

// The function declaration
int CalculateLoss(int costPrice, int sellingPrice);

// A structure for the test cases
typedef struct {
    int costPrice;
    int sellingPrice;
    int expected;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {   0,           0,           0 },
    {   0,           5,           0 },
    {   5,           0,           5 },
    {   5,           3,           2 },
    {   3,           5,           0 },
    { 100,         100,           0 },
    {1000,         999,           1 },
    { 999,        1000,           0 },
    { INT_MAX,       0,      INT_MAX },
    {   0,      INT_MAX,        0 },
    { INT_MAX,  INT_MAX,        0 },
    { INT_MAX-1, INT_MAX,        0 },
    { INT_MAX,   INT_MAX-1,      1 },
    { 100,          50,         50 },
    {  50,         100,          0 },
    {  20,          20,          0 },
    {   1,           0,          1 },
    {   0,           1,          0 },
    {2000000000,1999999999,      1 },
    {1999999999,2000000000,      0 },
    {  47,          23,         24 },
    {  23,          47,          0 },
    { INT_MAX/2,  INT_MAX/2 - 1,  1 },
    { INT_MAX/2 - 1, INT_MAX/2,    0 },
    {500000000,500000001,          0 },
    {500000001,500000000,          1 },
    {12345,      12344,          1 },
    {12344,      12345,          0 },
    {55555,      33333,      22222 },
    {33333,      55555,          0 }
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
        out = CalculateLoss(tests[i].costPrice, tests[i].sellingPrice);

        if (out == tests[i].expected)
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
        fprintf(file, "        \"inputs\": {\"costPrice\": %d, \"sellingPrice\": %d},\n",
                tests[i].costPrice, tests[i].sellingPrice);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].expected);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].expected) ? "true" : "false");
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
