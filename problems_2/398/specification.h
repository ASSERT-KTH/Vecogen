/*  A. Santa Claus and a Place in a Class
    Santa Claus is the first who came to the Christmas Olympiad, and he is going to be the first to take his place at a desk! In the classroom there are n lanes of m desks each, and there are two working places at each of the desks. The lanes are numbered from 1 to n from the left to the right, the desks in a lane are numbered from 1 to m starting from the blackboard.

Note
that the lanes go perpendicularly to the blackboard, not along it (see picture). The organizers numbered all the working places from 1 to 2 nm . The places are numbered by lanes (i. e. all the places of the first lane go first, then all the places of the second lane, and so on), in a lane the places are numbered starting from the nearest to the blackboard (i. e. from the first desk in the lane), at each desk, the place on the left is numbered before the place on the right. The picture illustrates the first and the second samples. Santa Clause knows that his place has number k . Help him to determine at which lane at which desk he should sit, and whether his place is on the left or on the right!
*/

/*@
    requires \valid(out_1) && \valid(out_2) && \valid(out_3) && \separated(out_1, out_2) && \separated(out_1, out_3) && \separated(out_2, out_3);

    assigns *out_1, *out_2, *out_3;
*/