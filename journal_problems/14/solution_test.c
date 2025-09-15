
#include <stdio.h>
#include <limits.h>

// The function declaration
long long sumTo(int *a, int n);

// A structure for the test cases
typedef struct {
    int a[10];
    int n;
    long long out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    { {0},                                 0,           0LL              },
    { {0},                                 1,           0LL              },
    { {5},                                 1,           5LL              },
    { {1,1},                               2,           2LL              },
    { {1,2,3},                             3,           6LL              },
    { {0,1,2,3,4},                         5,           10LL             },
    { {5,5,5,5,5},                         5,           25LL             },
    { {INT_MAX,0,0,0},                     4,           (long long)INT_MAX },
    { {1,INT_MAX,1,INT_MAX},               4,           4294967296LL     },
    { {0,1,2,3,4,5,6,7,8,9},               10,          45LL             },
    { {1,1,1,1,1,1,1,1,1,1},               10,          10LL             },
    { {INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX}, 10, 21474836470LL },
    { {3,7,2,9},                           4,           21LL             },
    { {INT_MAX},                           1,           (long long)INT_MAX },
    { {INT_MAX,INT_MAX},                   2,           4294967294LL     },
    { {1,0,1,0,1},                         5,           3LL              },
    { {0,0,0,0,0,0,0},                     7,           0LL              },
    { {2,3,5,7,11,13},                     6,           41LL             },
    { {1,1,2,3,5,8,13},                    7,           33LL             },
    { {1,2,4,8,16},                        5,           31LL             },
    { {5,10,15,20},                        4,           50LL             },
    { {100,200,300},                       3,           600LL            },
    { {100000,200000,300000,400000,500000},5,           1500000LL        },
    { {INT_MAX,0,INT_MAX,0,INT_MAX},       5,           6442450941LL     },
    { {12,34,56,78,90,11,22,33,44,55},     10,          435LL            },
    { {9,8,7,6,5,4,3,2,1},                 9,           45LL             },
    { {1000000000,1000000000,1000000000},  3,           3000000000LL     },
    { {INT_MAX,1,1,INT_MAX},               4,           4294967296LL     },
    { {INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX,INT_MAX}, 6, 12884901882LL },
    { {INT_MAX,0,INT_MAX,0,INT_MAX,0,INT_MAX,0,INT_MAX,0}, 10, 10737418235LL }
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
        long long out;

        // Run the function
        out = sumTo(tests[i].a, tests[i].n);

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
        fprintf(file, "        \"inputs\": {\"a\": [");
        for (int j = 0; j < tests[i].n; j++) {
            fprintf(file, "%d%s", tests[i].a[j], (j + 1 < tests[i].n) ? ", " : "");
        }
        fprintf(file, "], \"n\": %d},\n", tests[i].n);
        fprintf(file, "        \"expected_output\": %lld,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %lld,\n", out);
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
