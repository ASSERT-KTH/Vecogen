#include <stdio.h>

// The function declaration
int NthHexagonalNumber(int n);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { 0, 0 },
    { 1, 1 },
    { 2, 6 },
    { 3, 15 },
    { 4, 28 },
    { 5, 45 },
    { 6, 66 },
    { 7, 91 },
    { 8, 120 },
    { 9, 153 },
    { 10, 190 },
    { 20, 780 },
    { 50, 4950 },
    { 100, 19900 },
    { 999, 1995003 },
    { 1000, 1999000 },
    { 2047, 8378371 },
    { 2048, 8386560 },
    { 2049, 8394753 },
    { 4096, 33550336 },
    { 4097, 33566721 },
    { 9999, 199950003 },
    { 10000, 199990000 },
    { 12345, 304785705 },
    { 20000, 799980000 },
    { 25000, 1249975000 },
    { 30000, 1799970000 },
    { 30001, 1800090001 },
    { 32765, 2147057685 },
    { 32767, 2147319811 }
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
        out = NthHexagonalNumber(tests[i].x);

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