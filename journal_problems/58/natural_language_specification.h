
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

