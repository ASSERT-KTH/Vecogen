
#include <stdio.h>

// The function declaration
int triangular_prism_volume(int base, int height, int length);

// A structure for the test cases
typedef struct {
    int base;
    int height;
    int length;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {   1,     1,     1,           0},
    {   1,     1,     2,           1},
    {   1,     2,     3,           3},
    {   2,     3,     4,          12},
    {   5,     5,     5,          62},
    {  10,    10,    10,         500},
    {   3,     7,     9,          94},
    {   8,     6,     4,          96},
    { 100,   200,   300,      3000000},
    {   1,  1000,  1000,      500000},
    {1000,     1,  1000,      500000},
    {1000,  1000,     1,      500000},
    {46340, 46340,    2, 2147395600},
    {46340, 46340,    1, 1073697800},
    {65535, 65535,    1, 2147418112},
    {65535,     1,65535, 2147418112},
    {    1, 65535, 65535, 2147418112},
    {32768,     2,     1,      32768},
    {32768,     3,     1,      49152},
    {    2,  32768,     3,      98304},
    {12345,  6789,     3,  125715307},
    {1073741823,    2,     1, 1073741823},
    {2147483647,    1,     2, 2147483647},
    { 1234,  5678,     9,   31529934},
    {  999,   999,   999,  498501499},
    {    2,     2,     3,           6},
    {    2,     5,     7,          35},
    {    3,     3,     3,          13},
    {    4,     4,     5,          40},
    {    6,     7,     8,         168}
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
        out = triangular_prism_volume(
            tests[i].base,
            tests[i].height,
            tests[i].length
        );

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
        fprintf(file, 
            "        \"inputs\": {\"base\": %d, \"height\": %d, \"length\": %d},\n",
            tests[i].base,
            tests[i].height,
            tests[i].length
        );
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
