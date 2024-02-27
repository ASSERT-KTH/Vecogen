
/*  A. Patrick and Shopping
    Today Patrick waits for a visit from his friend Spongebob. To prepare for the visit, Patrick needs to buy some goodies in two stores located near his house. There is a d1 meter long road between his house and the first shop and a d2 meter long road between his house and the second shop. Also, there is a road of length d3 directly connecting these two shops to each other. Help Patrick calculate the minimum distance that he needs to walk in order to go to both shops and return to his house. Patrick always starts at his house. He should visit both shops moving only along the three existing roads and return back to his house. He doesn't mind visiting the same shop or passing the same road multiple times. The only goal is to minimize the total distance traveled. */

/*@
    requires \valid(out);
    requires d1 > 1 && d1 <= 100000000;
    requires d2 > 1 && d2 <= 100000000;
    requires d3 > 1 && d3 <= 100000000;
    assigns *out;
    behavior distance_house_and_shops_equal_to_direct_distance:
        assumes (d1 + d2) == d3;
        ensures *out == 2 * d3;
    behavior distance_house_and_shops_smaller_than_direct_distance:
        assumes (d1 + d2) < d3;
        ensures *out == 2 * (d1 + d2);
    behavior distance_house_and_shops_greater_than_direct_distance_1:
        assumes (d1 + d2) > d3 && (d1 + d3) < d2;
        ensures *out == 2 * (d1 + d3);
    behavior distance_house_and_shops_greater_than_direct_distance_2:
        assumes (d1 + d2) > d3 && (d2 + d3) < d1;
        ensures *out == 2 * (d2 + d3);
    behavior distance_house_and_shops_greater_than_direct_distance_3:
        assumes (d1 + d2) > d3 && ((d1 + d3) > d2) && ((d2 + d3) > d1);
        ensures *out == d1 + d2 + d3;
*/
void problem(int d1, int d2, int d3, int *out)
{
    if (d1 + d2 == d3)
    {
        *out = 2 * d3;
    }
    else if (d1 + d2 < d3)
    {
        *out = 2 * (d1 + d2);
    }
    else if (d1 + d2 > d3)
    {
        if (d1 + d3 < d2)
        {
            *out = 2 * (d1 + d3);
        }
        else if (d2 + d3 < d1)
        {
            *out = 2 * (d2 + d3);
        }
        else
        {
            *out = d1 + d2 + d3;
        }
    }
}