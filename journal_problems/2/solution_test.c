
#include <stdio.h>

// The function declaration
int submatcher_0(char * x22);

// A structure for the test cases
typedef struct {
    char *x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { "",    1 },
    { "a",   1 },
    { "aa",  1 },
    { "aaa", 1 },
    { "aaaa",    1 },
    { "aaaaa",   1 },
    { "aaaaaa",  1 },
    { "aaaaaaaa",    1 },
    { "aaaaaaaaaaaa",    1 },
    { "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",    1 }, // 30 'a's
    { "b",   0 },
    { "ab",  0 },
    { "ba",  0 },
    { "aab", 0 },
    { "aba", 0 },
    { "baa", 0 },
    { "abc", 0 },
    { "aaaaab",   0 },
    { "baaaa",    0 },
    { "abab",     0 },
    { "baba",     0 },
    { "a_a",      0 },
    { "a a",      0 },
    { " a ",      0 },
    { "aaaaaaaaabaaaaaaaa",    0 },
    { "aaaaaaaaaaaaaaaaaaaa",  1 }, // 20 'a's
    { "aaaaaaaaaaaaaaabaaaa",  0 },
    { "bbbbbbbbbb",            0 },
    { "aaaaaaaaaaaaaaaaaaaaaa",    1 }, // 22 'a's
    { "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 1 } // 31 'a's
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
        out = submatcher_0(tests[i].x);

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
        fprintf(file, "        \"inputs\": {\"x\": \"%s\"},\n", tests[i].x);
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