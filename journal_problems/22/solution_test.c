
#include <stdio.h>
#include <stdbool.h>

// The function declaration
int countTo(bool *a, int n);

// A structure for the test cases
typedef struct {
    bool *a;
    int x;      // the length n of the array
    int out;    // expected output
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { NULL,                                           0,  0 },
    { (bool[]){ false },                              1,  0 },
    { (bool[]){ true  },                              1,  1 },
    { (bool[]){ false, false },                       2,  0 },
    { (bool[]){ false, true  },                       2,  1 },
    { (bool[]){ true,  false },                       2,  1 },
    { (bool[]){ true,  true  },                       2,  2 },
    { (bool[]){ true, false, true, false, true },     5,  3 },
    { (bool[]){ false, false, false, false, false },  5,  0 },
    { (bool[]){ true, true, true, true, true },       5,  5 },
    { (bool[]){ true, false, false },                 3,  1 },
    { (bool[]){ false, true,  true  },                3,  2 },
    { (bool[]){ false, true,  false },                3,  1 },
    { (bool[]){ true, true, false, true, false },     5,  3 },
    { (bool[]){ true, true, true,  true,  true,
                true, true, true,  true,  true },    10, 10 },
    { (bool[]){ false, false, false, false, false,
                false, false, false, false, false }, 10,  0 },
    { (bool[]){ true, false, true,  false, true,
                false, true,  false, true, false },  10,  5 },
    { (bool[]){ false, true,  false, true,  false,
                true,  false, true,  false, true  }, 10,  5 },
    { (bool[]){ true, false, false, false, false,
                false, false, false, false, false }, 10,  1 },
    { (bool[]){ false, false, false, false, false,
                false, false, false, false, true  }, 10,  1 },
    { (bool[]){ true, false, false, true,  true,
                false, false, true,  false, true  }, 10,  5 },
    { (bool[]){ true, true,  false, false, true,
                false, true,  false, false, true,
                false, true,  false, true,  false }, 15,  7 },
    { (bool[]){ true, true,  false, false, false,
                false, false, false, false, false,
                false, false, false, false, false,
                false },                              16,  2 },
    { (bool[]){ true, true,  true,  true,  true,
                true,  true,  true,  true,  true,
                true,  true,  true,  true,  true,
                true },                               16, 16 },
    { (bool[]){ false, false, false, false, false,
                false, false, false, false, false,
                false, false, false, false, false,
                false },                              16,  0 },
    { (bool[]){ false, true,  false, true },          4,   2 },
    { (bool[]){ true,  true,  true,  false, false, false }, 6, 3 },
    { (bool[]){ false, false, false, true,  true, true }, 6, 3 },
    { (bool[]){ true,  false, true,  false, true, false, true }, 7, 4 },
    { (bool[]){ false, true,  false, true,  false, true, false }, 7, 3 }
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
        out = countTo(tests[i].a, tests[i].x);

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
