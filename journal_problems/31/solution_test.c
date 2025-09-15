
#include <stdio.h>

// The function declaration
int CountMonthsWith30Days(int month);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { -3, 0 },   // outside precond; impl returns 0
    { -1, 0 },   // outside precond; impl returns 0
    {  0, 0 },
    {  1, 0 },
    {  2, 0 },
    {  3, 0 },
    {  4, 1 },
    {  5, 1 },
    {  6, 2 },
    {  7, 2 },
    {  8, 2 },
    {  9, 3 },
    { 10, 3 },
    { 11, 4 },
    { 12, 4 },
    { 13, 4 },
    { 14, 4 },
    { 17, 5 },
    { 19, 6 },
    { 20, 6 },
    { 23, 8 },
    { 30, 10 },
    { 31, 10 },
    { 59, 20 },
    { 60, 20 },
    {100, 33 },
    {365, 121},
    {1000, 333},
    {2147483646, 715827882},
    {2147483647, 715827882}
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
        out = CountMonthsWith30Days(tests[i].x);

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
