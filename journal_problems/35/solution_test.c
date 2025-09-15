
#include <stdio.h>

// The function declaration
int NthNonagonalNumber(int n);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {  0,       0 },
    {  1,       1 },
    {  2,       9 },
    {  3,      24 },
    {  4,      46 },
    {  5,      75 },
    {  6,     111 },
    {  7,     154 },
    {  8,     204 },
    {  9,     261 },
    { 10,     325 },
    { 11,     396 },
    { 12,     474 },
    { 13,     559 },
    { 14,     651 },
    { 15,     750 },
    { 20,    1350 },
    { 25,    2125 },
    { 47,    7614 },
    { 50,    8625 },
    {100,   34750 },
    {123,   52644 },
    {200,  139500 },
    {300,  314250 },
    {321,  359841 },
    {400,  559000 },
    {500,  873750 },
    {600, 1258500 },
    {700, 1713250 },
    {783, 2143854 }
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
        out = NthNonagonalNumber(tests[i].x);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (expected %d, got %d)\n",
                   i + 1, tests[i].out, out);
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
