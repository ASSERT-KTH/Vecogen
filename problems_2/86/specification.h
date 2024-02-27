/*  A. Elephant
    An elephant decided to visit his friend. It turned out that the elephant's house is located at point 0 and his friend's house is located at point x ( x > 0) of the coordinate line. In one step the elephant can move 1 , 2 , 3 , 4 or 5 positions forward. Determine, what is the minimum number of steps he need to make in order to get to his friend's house.*/

/*@
    requires \valid(out);
    requires 1 <=  x <= 1000000;
    assigns *out;
    ensures *out == (x + 4) / 5;
*/
void problem(int x, int *out);