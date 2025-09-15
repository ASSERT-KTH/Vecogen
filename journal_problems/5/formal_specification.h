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
