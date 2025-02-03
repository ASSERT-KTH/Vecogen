The results folder contains all the results from the experiments done using VeCoGen on different LLMs.

The following naming convention is used:
1.  LLM_name                                        -
2.  number_of_candidate_programs_per_invocation     -
3.  feedback_iteratinos                             -
4.  temperature                                     -
5.  prompt_type                                     -
6. specification_type

Each configuration has a folder with each of the 15 problems. Each problem has a folder name associated with an index used in the Code4bench dataset:
86, 124, 139, 237, 301, 376, 379, 427, 757, 834, 932, 976, 1166, 1347

For each of these folders there will be two files, the last generated C code and the results file. The last generated C code can either be the verifying file in case a valid solution was found, or the last generated solution that does not verify. The results.txt file in each folder contains all information that is relevant to generating andverifyhing the generated code files. 