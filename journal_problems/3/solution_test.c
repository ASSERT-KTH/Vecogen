
#include <stdio.h>

// The function declaration
unsigned gcd_rec(unsigned a, unsigned b);

// A structure for the test cases
typedef struct {
    unsigned a;
    unsigned b;
    unsigned out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {   0,           0,           0 },
    {   0,           1,           1 },
    {   1,           0,           1 },
    {   5,           0,           5 },
    {   0,           7,           7 },
    {   1,           1,           1 },
    {   2,           4,           2 },
    {   4,           2,           2 },
    {  18,          24,           6 },
    {  24,          18,           6 },
    { 100,          10,          10 },
    {  10,         100,          10 },
    {  17,          13,           1 },
    {  13,          17,           1 },
    {  21,          14,           7 },
    {  14,          21,           7 },
    { 270,         192,           6 },
    { 192,         270,           6 },
    {  81,          27,          27 },
    {  27,          81,          27 },
    {  48,         180,          12 },
    { 180,          48,          12 },
    { 630,         310,          10 },
    { 310,         630,          10 },
    {1000000000,  500000000,  500000000},
    {500000000,  1000000000,  500000000},
    {1234567890,  987654321,           9},
    { 987654321, 1234567890,           9},
    {  999983,          2,           1},
    {2147483646,2147483646,2147483646}
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
        unsigned out;

        // Run the function
        out = gcd_rec(tests[i].a, tests[i].b);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (got %u, expected %u)\n", i + 1, out, tests[i].out);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"a\": %u, \"b\": %u},\n", tests[i].a, tests[i].b);
        fprintf(file, "        \"expected_output\": %u,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %u,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    }%s\n", (i + 1 < num_tests) ? "," : "");
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
