#include <stdio.h>

// The function declaration
char shift_plus32(char c);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {  0,  32 },
    {  1,  33 },
    {  2,  34 },
    { 10,  42 },
    { 15,  47 },
    { 16,  48 },
    { 23,  55 },
    { 29,  61 },
    { 30,  62 },
    { 31,  63 },
    { 32,  64 },
    { 47,  79 },
    { 48,  80 },
    { 50,  82 },
    { 63,  95 },
    { 64,  96 },
    { 65,  97 },
    { 79, 111 },
    { 80, 112 },
    { 90, 122 },
    { 95, 127 },
    { 96,   0 },
    { 97,   1 },
    {100,   4 },
    {111,  15 },
    {112,  16 },
    {120,  24 },
    {125,  29 },
    {126,  30 },
    {127,  31 }
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

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
        out = (int)shift_plus32((char)tests[i].x);

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