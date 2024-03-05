/* Tram time limit per test 1 second memory limit per test 256 megabytes input standard input output standard output The tram in Berland goes along a straight line from the point 0 to the point s and back, passing 1 meter per t 1 seconds in both directions. It means that the tram is always in the state of uniform rectilinear motion, instantly turning around at points x = 0 and x = s . Igor is at the point x 1 . He should reach the point x 2 . Igor passes 1 meter per t 2 seconds. Your task is to determine the minimum time Igor needs to get from the point x 1 to the point x 2 , if it is known where the tram is and in what direction it goes at the moment Igor comes to the point x 1 . Igor can enter the tram unlimited number of times at any moment when his and the tram's positions coincide. It is not obligatory that points in which Igor enter and exit the tram are integers. Assume that any boarding and unboarding happens instantly. Igor can move arbitrary along the line (but not faster than 1 meter per t 2 seconds). He can also stand at some point for some time.*/

/*@
    requires 2 <= s <= 1000;
    requires 0 <= x1 <= s;
    requires 0 <= x2 <= s;
    requires x1 != x2;
    requires 1 <= t1 <= 1000;
    requires 1 <= t2 <= 1000;
    requires 1 <= p <= s - 1;
    requires d == 1 || d == -1;
    requires \valid(out);
    assigns *out;
    behavior x1_less_than_x2_and_d_equals_1_and_p_less_than_x1:
        assumes x1 < x2 && d == 1 && p <= x1;
        ensures *out == \min((x2 - x1) * t2, (x2 - x1) * t1 + (x1 - p) * t1);
    behavior x1_less_than_x2_and_d_equals_1_and_p_less_than_x2:
        assumes x1 < x2 && d == 1 && p <= x2;
        ensures *out == \min((x2 - x1) * t2, (2 * s - p + x2) * t1);
    behavior x1_less_than_x2_and_d_equals_1_and_p_greater_than_x2:
        assumes x1 < x2 && d == 1 && p > x2;
        ensures *out == \min((x2 - x1) * t2, (2 * s - p + x2) * t1);
    behavior x1_less_than_x2_and_d_not_equals_1:
        assumes x1 < x2 && d == -1;
        ensures *out == \min((x2 - x1) * t2, (x2 - x1) * t1 + (p + x1) * t1);
    behavior x1_greater_than_x2_and_d_equals_1_and_p_greater_than_x1:
        assumes x1 >= x2 && d == 1 && p >= x1;
        ensures *out == \min((x1 - x2) * t2, (x1 - x2) * t1 + (x1 - p) * t1);
    behavior x1_greater_than_x2_and_d_equals_1_and_p_greater_than_x2:
        assumes x1 >= x2 && d == 1 && p >= x2;
        ensures *out == \min((x1 - x2) * t2, (2 * s + p - x2) * t1);
    behavior x1_greater_than_x2_and_d_equals_1_and_p_less_than_x2:
        assumes x1 >= x2 && d == 1 && p < x2;
        ensures *out == \min((x1 - x2) * t2, (2 * s + p - x2) * t1);
    behavior x1_greater_than_x2_and_d_not_equals_1:
        assumes x1 >= x2 && d == -1;
        ensures *out == \min((x1 - x2) * t2, (x1 - x2) * t1 + (2 * s - p - x1) * t1);
    complete behaviors;
    disjoint behaviors;
*/

void tram(long s, long x1, long x2, long t1, long t2, long p, long d, long *out)
{
    if (x1 >= x2)
    {
        x1 = s - x1;
        x2 = s - x2;
        d *= -1;
        p = s - p;
    }

    long d2 = x2 - x1;
    long t_igor = d2 * t2;
    long t_tram = d2 * t1;

    long ext = 0;

    if (d == 1)
    {
        if (p <= x1)
        {
            ext = (x1 - p) * t1;
        }
        else if (p <= x2)
        {
            ext = (2 * s - p + x1) * t1;
        }
        else
        {
            ext = (2 * s - p + x1) * t1;
        }
    }
    else
    {
        ext = (p + x1) * t1;
    }
    t_tram += ext;
    *out = (t_igor < t_tram) ? t_igor : t_tram;
}