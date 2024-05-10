/*
    Today Patrick waits for a visit from his friend Spongebob. To prepare for the visit, Patrick needs to buy some goodies in two stores located near his house. There is a d1 meter long road between his house and the first shop and a d2 meter long road between his house and the second shop. Also, there is a road of length d3 directly connecting these two shops to each other. Help Patrick calculate the minimum distance that he needs to walk in order to go to both shops and return to his house. Patrick always starts at his house. He should visit both shops moving only along the three existing roads and return back to his house. He doesn't mind visiting the same shop or passing the same road multiple times. The only goal is to minimize the total distance traveled.

    Input
    The input contains three integers d1 , d2 , d3 ( 1 ≤ d1 , d2 , d3 ≤ 10^8) — the lengths of the paths. d1 is the length of the path connecting Patrick's house and the first shop; d2 is the length of the path connecting Patrick's house and the second shop; d3 is the length of the path connecting both shops.

    Output
    The minimum distance that Patrick will have to walk in order to visit both shops and return to his house.
*/

/*@
    requires \valid(out);
    requires d1 > 1 && d1 <= 100000000;
    requires d2 > 1 && d2 <= 100000000;
    requires d3 > 1 && d3 <= 100000000;
    assigns *out;
    // Get the minimum of all four possible paths
    ensures *out == \min(2 * d1 + 2 * d2, \min(d1 + d2 + d3, \min(2 * d1 + 2 * d3, 2 * d2 + 2 * d3)));
*/
void calculateMinimumDistanceForShopping(int d1, int d2, int d3, int *out);