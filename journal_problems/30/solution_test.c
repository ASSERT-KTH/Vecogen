
#include <stdio.h>

// The function declaration
int TetrahedralNumber(int n);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { 0, 0 },
    { 1, 1 },
    { 2, 4 },
    { 3, 10 },
    { 4, 20 },
    { 5, 35 },
    { 6, 56 },
    { 7, 84 },
    { 8, 120 },
    { 9, 165 },
    { 10, 220 },
    { 15, 680 },
    { 20, 1540 },
    { 30, 4960 },
    { 50, 22100 },
    { 100, 171700 },
    { 200, 1353400 },
    { 250, 2635500 },
    { 300, 4545100 },
    { 400, 10746800 },
    { 500, 20958500 },
    { 600, 36180200 },
    { 700, 57411900 },
    { 1000, 167167000 },
    { 1500, 563625500 },
    { 1800, 973620600 },
    { 2000, 1335334000 },
    { 2200, 1777087400 },
    { 2291, 2006746466 },
    { 2292, 2009374244 }
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
        out = TetrahedralNumber(tests[i].x);

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
