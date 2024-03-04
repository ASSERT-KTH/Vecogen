/*  Tram
    The tram in Berland goes along a straight line from the point 0 to the point s and back, passing 1 meter per t 1 seconds in both directions. It means that the tram is always in the state of uniform rectilinear motion, instantly turning around at points x = 0 and x = s . Igor is at the point x 1 . He should reach the point x 2 . Igor passes 1 meter per t 2 seconds. Your task is to determine the minimum time Igor needs to get from the point x 1 to the point x 2 , if it is known where the tram is and in what direction it goes at the moment Igor comes to the point x 1 . Igor can enter the tram unlimited number of times at any moment when his and the tram's positions coincide. It is not obligatory that points in which Igor enter and exit the tram are integers. Assume that any boarding and unboarding happens instantly. Igor can move arbitrary along the line (but not faster than 1 meter per t 2 seconds). He can also stand at some point for some time.*/
/*@ requires 2 <= s <= 1000;
    requires 0 <= x1 <= s;
    requires 0 <= x2 <= s;
    requires x1 != x2;
    requires 1 <= t1 <= 1000;
    requires 1 <= t2 <= 1000;
    requires 1 <= p <= s - 1;
    requires d == 1 || d == -1;
    requires \valid(out);
    assigns *out;
    ensures \result == \min(\abs(start - end) * myt, \abs(start - tramnow) * tramt + \abs(tramnow - end) * tramt);
*/
int problem(int s, int x1, int x2, int t1, int t2, int p, int d, int *out)
{
    int n, start, end, myt, tramt, tramnow, d;
    scanf("%d %d %d", &n, &start, &end);
    scanf("%d %d", &tramt, &myt);
    scanf("%d %d", &tramnow, &d);
    int mytime = abs(start - end) * myt;
    int tramtime = 0;
    if ((start >= tramnow && d == 1) || (start <= tramnow && d == -1))
    {
        tramtime += abs(start - tramnow) * tramt;
    }
    else
    {
        if (d == -1)
        {
            tramtime += (tramnow + start) * tramt;
            d = 1;
        }
        else
        {
            d = -1;
            tramtime += (n - tramnow + n - start) * tramt;
        }
    }
    if ((end >= start && d == 1) || (end <= start && d == -1))
        tramtime += abs(start - end) * tramt;
    else
    {
        if (d == 1)
        {
            tramtime += (n - start + n - end) * tramt;
        }
        else
        {
            tramtime += (start + end) * tramt;
        }
    }
    if (mytime < tramtime)
        printf("%d", mytime);
    else
        printf("%d", tramtime);
    return 0;
}