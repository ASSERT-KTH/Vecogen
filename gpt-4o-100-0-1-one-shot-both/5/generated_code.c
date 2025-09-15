struct SolutionComparator {
  int getValue;
  int solutionCost;
};

/*The function deals with the comparison of two structures, each of which contains an integer value and a solution cost. This comparison is carried out with respect to an integer value 'h'. The structures to be compared are instances of the struct 'SolutionComparator'. The comparison is done on various conditions involving the 'value' and 'solutionCost' of the 'SolutionComparator' objects and the integer 'h'.

  The main objective of the code is to compare two 'SolutionComparator' structures based on their 'getValue' and 'solutionCost' properties in relation to a given integer 'h'. The comparison results in three possible outcomes: -1, 0, or 1. This result is determined based on a series of conditions pertaining to the 'getValue' and 'solutionCost' of the 'SolutionComparator' structures and their relation to 'h'.

  Input
  The input to the function 'compare' consists of three parameters: two instances of the 'SolutionComparator' structure (o1 and o2), and an integer 'h'. The 'SolutionComparator' structure consists of two integer properties: 'getValue' and 'solutionCost'. For both the 'SolutionComparator' instances and the integer 'h', the input values should meet the following conditions:
  - 'h' should be a non-negative integer less than 100.
  - The 'getValue' and 'solutionCost' properties of the 'SolutionComparator' instances (o1 and o2) should be non-negative integers less than or equal to 10.

  Output
  The output of the 'compare' function is an integer that can be -1, 0, or 1. The result is determined by the following conditions:
  - The function returns 0 if the 'getValue' of both 'SolutionComparator' instances is -1, or if the 'getValue' and 'solutionCost' of the structures are equal, or if the absolute difference between 'h' and the 'getValue' of each structure is the same.
  - The function returns -1 if the 'getValue' of o1 is not -1 and that of o2 is -1, or if the 'getValue' of both structures is the same and the 'solutionCost' of o1 is less than that of o2, or if the 'getValue' of both structures is not the same and the absolute difference between 'h' and the 'getValue' of o1 is less than that of o2.
  - The function returns 1 if the 'getValue' of o1 is -1 and that of o2 is not -1, or if the 'getValue' of both structures is the same and the 'solutionCost' of o1 is greater than that of o2, or if the 'getValue' of both structures is not the same and the absolute difference between 'h' and the 'getValue' of o1 is greater than that of o2.
*/

/*@
  requires 0 <= h < 100;
  requires 0 <= o1.getValue <= 10 && 0 <= o1.solutionCost <= 10;
  requires 0 <= o2.getValue <= 10 && 0 <= o2.solutionCost <= 10;
  assigns \nothing;

  ensures \result == 0 <==>
    ((o1.getValue == o2.getValue && o1.solutionCost == o2.solutionCost) ||
     (o1.getValue != o2.getValue &&
      \abs(h - o1.getValue) == \abs(h - o2.getValue)));

  ensures \result == -1 <==>
    ((o1.getValue == o2.getValue && o1.solutionCost < o2.solutionCost) ||
     (o1.getValue != o2.getValue &&
      \abs(h - o1.getValue) < \abs(h - o2.getValue)));

  ensures \result == 1 <==>
    ((o1.getValue == o2.getValue && o1.solutionCost > o2.solutionCost) ||
     (o1.getValue != o2.getValue &&
      \abs(h - o1.getValue) > \abs(h - o2.getValue)));
*/

int compare(struct SolutionComparator o1, struct SolutionComparator o2, int h) {
    if (o1.getValue == o2.getValue) {
        if (o1.solutionCost < o2.solutionCost) {
            return -1;
        } else if (o1.solutionCost > o2.solutionCost) {
            return 1;
        } else {
            return 0;
        }
    } else {
        int absDiff1 = (h > o1.getValue) ? h - o1.getValue : o1.getValue - h;
        int absDiff2 = (h > o2.getValue) ? h - o2.getValue : o2.getValue - h;
        if (absDiff1 < absDiff2) {
            return -1;
        } else if (absDiff1 > absDiff2) {
            return 1;
        } else {
            return 0;
        }
    }
}
