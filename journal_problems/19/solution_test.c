
#include <stdio.h>

// The function declaration
int SquarePyramidSurfaceArea(int baseEdge, int height);

// A structure for the test cases
typedef struct {
    int baseEdge;
    int height;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { 1,      1,          3 },
    { 1,      2,          5 },
    { 2,      1,          8 },
    { 2,      2,         12 },
    { 3,      4,         33 },
    { 5,      5,         75 },
    { 10,     1,        120 },
    { 1,     10,         21 },
    { 10,    10,        300 },
    { 100,   100,     30000 },
    { 123,   456,    127305 },
    { 456,   123,    320112 },
    { 1000,  2000,  5000000 },
    { 2000,  1000,  8000000 },
    { 5000,  5000, 75000000 },
    { 46339,   1, 2147395599 },
    { 30000,20000,2100000000 },
    { 40000, 1000,1680000000 },
    { 30000,15000,1800000000 },
    { 32767,  100,1080229689 },
    { 21474,21474,1383398028 },
    { 9999,  9999,299940003 },
    { 46338,   1,2147302920 },
    { 12345, 6789,320019435 },
    { 2,   1000000,  4000004 },
    { 45000,    2,2025180000 },
    { 123,      1,    15375 },
    {   1,    123,      247 },
    {  50,     50,     7500 },
    {20000, 30000,1600000000 }
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
        out = SquarePyramidSurfaceArea(tests[i].baseEdge, tests[i].height);

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
        fprintf(file, "        \"inputs\": {\"baseEdge\": %d, \"height\": %d},\n",
                tests[i].baseEdge, tests[i].height);
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
    fprintf(file, "            \"pass_rate\": %.2f\n", (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    fprintf(file, "]\n");
    fclose(file);
    return 0;
}
