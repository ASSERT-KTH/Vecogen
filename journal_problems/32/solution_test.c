
#include <stdio.h>
#include <stdint.h>

// The function declaration
uint32_t CenteredHexagonalNumber(uint32_t n);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { 0, 1 },
    { 1, 1 },
    { 2, 7 },
    { 3, 19 },
    { 4, 37 },
    { 5, 61 },
    { 6, 91 },
    { 7, 127 },
    { 8, 169 },
    { 9, 217 },
    { 10, 271 },
    { 11, 331 },
    { 12, 397 },
    { 13, 469 },
    { 14, 547 },
    { 15, 631 },
    { 16, 721 },
    { 20, 1141 },
    { 30, 2611 },
    { 50, 7351 },
    { 100, 29701 },
    { 500, 748501 },
    { 1000, 2997001 },
    { 2000, 11994001 },
    { 5000, 74985001 },
    { 10000, 299970001 },
    { 15000, 674955001 },
    { 20000, 1199940001 },
    { 22000, 1451934001 },
    { 26000, 2027922001 }
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
        out = (int)CenteredHexagonalNumber((uint32_t)tests[i].x);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (n=%d: expected %d, got %d)\n",
                   i + 1, tests[i].x, tests[i].out, out);
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
