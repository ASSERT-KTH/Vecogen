/*Today Patrick waits for a visit from his friend Spongebob. To prepare for the visit, Patrick needs to buy some goodies in two stores located near his house. There is a d1 meter long road between his house and the first shop and a d2 meter long road between his house and the second shop. Also, there is a road of length d3 directly connecting these two shops to each other. Help Patrick calculate the minimum distance that he needs to walk in order to go to both shops and return to his house. Patrick always starts at his house. He should visit both shops moving only along the three existing roads and return back to his house. He doesn't mind visiting the same shop or passing the same road multiple times. The only goal is to minimize the total distance traveled.

  Input
  The input contains three integers d1 , d2 , d3 (1 <= d1 , d2 , d3 <= 10^8 ) — the lengths of the paths. d1 is the length of the path connecting Patrick's house and the first shop; d2 is the length of the path connecting Patrick's house and the second shop; d3 is the length of the path connecting both shops.

  Output
  Return the minimum distance that Patrick will have to walk in order to visit both shops and return to his house.
*/

/*@
logic integer route1(integer d1, integer d2, integer d3) = d1 + d3 + d2;
  logic integer route2(integer d1, integer d2, integer d3) = 2*(d1 + d2);
  logic integer route3(integer d1, integer d2, integer d3) = 2*(d1 + d3);
  logic integer route4(integer d1, integer d2, integer d3) = 2*(d2 + d3);
*/

/*@
requires 1 <= d1 <= 100000000;
  requires 1 <= d2 <= 100000000;
  requires 1 <= d3 <= 100000000;
  assigns \nothing;
  ensures \result <= route1(d1,d2,d3);
  ensures \result <= route2(d1,d2,d3);
  ensures \result <= route3(d1,d2,d3);
  ensures \result <= route4(d1,d2,d3);
  ensures \result == route1(d1,d2,d3)
       || \result == route2(d1,d2,d3)
       || \result == route3(d1,d2,d3)
       || \result == route4(d1,d2,d3);
*/

int minWalkingDistance(int d1, int d2, int d3) {
    int r1 = d1 + d2 + d3;
    int r2 = 2 * (d1 + d2);
    int r3 = 2 * (d1 + d3);
    int r4 = 2 * (d2 + d3);
    int min12 = r1 < r2 ? r1 : r2;
    int min34 = r3 < r4 ? r3 : r4;
    return min12 < min34 ? min12 : min34;
}
