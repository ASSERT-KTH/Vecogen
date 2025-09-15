
#include <stdio.h>
#include <limits.h>

// The function declaration
typedef enum { Max, Min } kind;
int extremum(kind k, int x, int y);

// A structure for the test cases
typedef struct {
    kind k;
    int x;
    int y;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { Max,  1,   2,   2 },
    { Max,  2,   1,   2 },
    { Max,  5,   5,   5 },
    { Min,  1,   2,   1 },
    { Min,  2,   1,   1 },
    { Min,  5,   5,   5 },
    { Max, -1,  -2,  -1 },
    { Min, -1,  -2,  -2 },
    { Max,  INT_MAX,   0,        INT_MAX },
    { Min,  INT_MAX,   0,        0       },
    { Max,  INT_MIN,   0,        0       },
    { Min,  INT_MIN,   0,        INT_MIN },
    { Max,  INT_MAX,   INT_MAX-1, INT_MAX   },
    { Min,  INT_MAX,   INT_MAX-1, INT_MAX-1 },
    { Max,  INT_MIN+1, INT_MIN,    INT_MIN+1 },
    { Min,  INT_MIN+1, INT_MIN,    INT_MIN   },
    { Max,  100,      -100,     100    },
    { Min,  100,      -100,    -100    },
    { Max, -100,      100,      100    },
    { Min, -100,      100,     -100    },
    { Max,   0,        0,        0     },
    { Min,   0,        0,        0     },
    { Max,  -5,        5,        5     },
    { Min,  -5,        5,       -5     },
    { Max,  INT_MAX,   INT_MIN, INT_MAX  },
    { Min,  INT_MAX,   INT_MIN, INT_MIN  },
    { Max, 12345,   12345,   12345 },
    { Min, 12345,   12345,   12345 },
    { Max, -12345, -12346, -12345 },
    { Min, -12345, -12346, -12346 }
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
        out = extremum(tests[i].k, tests[i].x, tests[i].y);

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
