
#include <stdio.h>

// The function declaration
int LateralSurfaceArea(int size);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {   1,           4 },
    {   2,          16 },
    {   3,          36 },
    {   4,          64 },
    {   5,         100 },
    {  10,         400 },
    {  15,         900 },
    {  50,       10000 },
    { 100,       40000 },
    { 123,       60516 },
    { 127,       64516 },
    { 128,       65536 },
    { 256,      262144 },
    { 512,     1048576 },
    { 999,     3992004 },
    {1000,     4000000 },
    {1023,     4186116 },
    {1024,     4194304 },
    {1025,     4202500 },
    {2048,    16777216 },
    {3000,    36000000 },
    {5000,   100000000 },
    {7777,   241926916 },
    {10000,  400000000 },
    {12345,  609596100 },
    {15000,  900000000 },
    {20000, 1600000000 },
    {23168, 2147024896 },
    {23169, 2147210244 },
    {23170, 2147395600 }
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
        out = LateralSurfaceArea(tests[i].x);

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
