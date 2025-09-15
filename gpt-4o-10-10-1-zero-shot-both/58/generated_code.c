struct SantaSpot {
    int lane;
    int desk;
    char side;
};

/*Santa Claus is the first who came to the Christmas Olympiad, and he is going to be the first to take his place at a desk! In the classroom there are n lanes of m desks each, and there are two working places at each of the desks. The lanes are numbered from 1 to n from the left to the right, the desks in a lane are numbered from 1 to m starting from the blackboard.

    Note
    that the lanes go perpendicularly to the blackboard, not along it. The organizers numbered all the working places from 1 to 2*n*m . The places are numbered by lanes (i. e. all the places of the first lane go first, then all the places of the second lane, and so on), in a lane the places are numbered starting from the nearest to the blackboard (i. e. from the first desk in the lane), at each desk, the place on the left is numbered before the place on the right. The picture illustrates the first and the second samples. Santa Clause knows that his place has number k . Help him to determine at which lane at which desk he should sit, and whether his place is on the left or on the right!

    Input
    The input contains three integers n , m and k (1 <= n, m <= 10000, 1 <= k <= 2*n*m) — the number of lanes, the number of desks in each lane and the number of Santa Claus' place.

    Output
    Return a struct with three fields: the number of lane r , the number of desk d , and a character s , which stands for the side of the desk Santa Claus. The character s should be " L ", if Santa Clause should sit on the left, and " R " if his place is on the right.
*/


/*Struct to hold the decoded spot
*/

/*@
// Compute the global place number for (lane,desk,side) in an n×m classroom
    logic integer place_index(integer lane, integer desk, char side,
                              integer n, integer m) =
      ((lane - 1) * m + (desk - 1)) * 2
      + (side == 'L' ? 1 : 2);
*/

/*@
requires 1 <= n <= 10000;
    requires 1 <= m <= 10000;
    requires 1 <= k <= 2 * n * m;
    assigns \nothing;
    ensures 1 <= \result.lane && \result.lane <= n;
    ensures 1 <= \result.desk  && \result.desk  <= m;
    ensures \result.side == 'L' || \result.side == 'R';
    ensures place_index(\result.lane, \result.desk, \result.side, n, m) == k;
*/

struct SantaSpot verify_santa_spot(int n, int m, int k) {
    struct SantaSpot spot;
    int lane = (k - 1) / (2 * m) + 1;
    int desk = ((k - 1) % (2 * m)) / 2 + 1;
    char side = ((k - 1) % 2 == 0) ? 'L' : 'R';

    spot.lane = lane;
    spot.desk = desk;
    spot.side = side;

    return spot;
}
