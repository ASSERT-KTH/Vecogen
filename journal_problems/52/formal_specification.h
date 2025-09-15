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

