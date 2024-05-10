/*
    Luke Skywalker got locked up in a rubbish shredder between two presses. R2D2 is already working on his rescue, but Luke needs to stay alive as long as possible. For simplicity we will assume that everything happens on a straight line, the presses are initially at coordinates 0 and L , and they move towards each other with speed v1 and v2 , respectively. Luke has width d and is able to choose any position between the presses. Luke dies as soon as the distance between the presses is less than his width. Your task is to determine for how long Luke can stay alive.

    Input
    The input contains four integers d, L, v1 , v2 (1 ≤ d, L , v1 , v2 ≤ 10000, d < L ) — Luke's width, the initial position of the second press and the speed of the first and second presses, respectively.

    Output
    Output a single real value — the maximum period of time Luke can stay alive for. Your answer will be considered correct if its absolute or relative error does not exceed 10^ -6 . Namely: let's assume that your answer is a , and the answer of the jury is b.
*/

/*@
    requires \valid(out);
    requires 1 <= d < 10000;
    requires 1 <= L < 10000;
    requires 1 <= v1 < 10000;
    requires 1 <= v2 < 10000;
    requires d < L;
    assigns *out;
    ensures *out == ((L - d) / (v1 + v2));
*/
void calculateMaxSurvivalTime(int d, int L, int v1, int v2, int *out)
{
    *out = ((L - d) / (v1 + v2));
}
