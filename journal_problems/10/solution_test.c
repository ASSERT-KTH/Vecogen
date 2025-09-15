
#include <stdio.h>

// The function declaration
int NthOctagonalNumber(int n);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { 0,        0 },
    { 1,        1 },
    { 2,        8 },
    { 3,       21 },
    { 4,       40 },
    { 5,       65 },
    { 10,     280 },
    { 17,     833 },
    { 18,     936 },
    { 19,    1045 },
    { 20,    1160 },
    { 25,    1825 },
    { 29,    2465 },
    { 36,    3816 },
    { 37,    4033 },
    { 48,    6816 },
    { 49,    7105 },
    { 50,    7400 },
    { 73,   15841 },
    { 81,   19521 },
    { 99,   29205 },
    { 100,  29800 },
    { 123, 45141 },
    { 1111, 3700741 },
    { 1234, 4565800 },
    { 2023,12273541 },
    { 5000,74990000 },
    { 999, 2992005 },
    { 9999,299920005 },
    {10000,299980000 }
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
        out = NthOctagonalNumber(tests[i].x);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (input=%d, expected=%d, got=%d)\n",
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
