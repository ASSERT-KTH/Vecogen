
#include <stdio.h>
#include <limits.h>

// The function declaration
int Multiply(int a, int b);

// A structure for the test cases
typedef struct {
    int a;
    int b;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {   0,     0,           0 },
    {   0, 12345,           0 },
    {12345,     0,           0 },
    {   1,     1,           1 },
    {  -1,     1,          -1 },
    {   1,    -1,          -1 },
    {  -1,    -1,           1 },
    { 123,   456,       56088 },
    { -123,  456,     -56088 },
    { 123,  -456,     -56088 },
    { -123, -456,       56088 },
    { INT_MAX, 1,   INT_MAX },
    { INT_MIN, 1,   INT_MIN },
    { INT_MAX, 0,         0 },
    { INT_MIN, 0,         0 },
    { 46340, 46340, 2147395600 },
    {-46340, 46340,-2147395600 },
    { 46340,-46340,-2147395600 },
    {-46340,-46340, 2147395600 },
    { 65536, 32767, 2147418112 },
    {-65536, 32767,-2147418112 },
    { 65536,-32767,-2147418112 },
    {-65536,-32767, 2147418112 },
    {100000, 10000, 1000000000 },
    {-100000,10000,-1000000000 },
    {100000,-10000,-1000000000 },
    {-100000,-10000, 1000000000 },
    { 32767, 65535, 2147385345 },
    {-32768, 65535,-2147450880 },
    { 50000, 40000, 2000000000 }
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
        out = Multiply(tests[i].a, tests[i].b);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed: got %d, expected %d\n",
                   i + 1, out, tests[i].out);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"a\": %d, \"b\": %d},\n",
                tests[i].a, tests[i].b);
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
    fprintf(file, "            \"pass_rate\": %.2f\n",
            (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    fprintf(file, "]\n");
    fclose(file);
    return 0;
}
