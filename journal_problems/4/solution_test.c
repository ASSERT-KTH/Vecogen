
#include <stdio.h>

// The function declaration
int p(char *x0);

// A structure for the test cases
typedef struct {
    char x;    // the first character of the input string
    int  out;  // expected output
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { '0',  0 },
    { '1',  1 },
    { '2',  2 },
    { '3',  3 },
    { '4',  4 },
    { '5',  5 },
    { '6',  6 },
    { '7',  7 },
    { '8',  8 },
    { '9',  9 },
    { 'a', -1 },
    { 'z', -1 },
    { 'A', -1 },
    { 'Z', -1 },
    { '/', -1 },  // just before '0'
    { ':', -1 },  // just after '9'
    { ' ', -1 },
    { '\n', -1 },
    { '\t', -1 },
    { '.', -1 },
    { '?', -1 },
    { '!', -1 },
    { '*', -1 },
    { '@', -1 },
    { '[', -1 },
    { 'a', -1 },
    { '{', -1 },
    { '}', -1 },
    { '~', -1 },
    { '-', -1 }
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
        // Build a one-character string from tests[i].x
        char input_str[2] = { tests[i].x, '\0' };

        // Run the function
        out = p(input_str);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (input char code %d)\n", i + 1, (int)tests[i].x);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"x\": %d},\n", (int)tests[i].x);
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
