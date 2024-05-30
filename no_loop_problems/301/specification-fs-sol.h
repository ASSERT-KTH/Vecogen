/*@
    requires \valid(out);
    requires 1 <= x1 <= 100;
    requires 1 <= x2 <= 100;
    requires 1 <= x3 <= 100;
    assigns *out;
    ensures *out == (\max(x1, \max(x2, x3)) - \min(x1, \min(x2, x3)));
*/
void calculateOptimalMeetingPointDistance(int x1, int x2, int x3, int *out);
