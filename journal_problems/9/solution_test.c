
#include <stdio.h>

// The function declaration
int foo(int n);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { -1000, 91 },
    { -999, 91 },
    { -500, 91 },
    { -101, 91 },
    { -100, 91 },
    { -50, 91 },
    { -10, 91 },
    {  -1, 91 },
    {   0, 91 },
    {   1, 91 },
    {  10, 91 },
    {  18, 91 },
    {  33, 91 },
    {  50, 91 },
    {  60, 91 },
    {  75, 91 },
    {  90, 91 },
    {  97, 91 },
    {  99, 91 },
    { 100, 91 },
    { 101, 91 },
    { 102, 92 },
    { 105, 95 },
    { 110, 100 },
    { 123, 113 },
    { 150, 140 },
    { 200, 190 },
    { 250, 240 },
    { 512, 502 },
    { 999, 989 },
    { 1000, 990 }
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
        out = foo(tests[i].x);

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
