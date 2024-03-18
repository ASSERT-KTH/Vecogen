/*  Compote
    Nikolay has a lemons, b apples and c pears. He decided to cook a compote. According to the recipe the fruits should be in the ratio 1: 2: 4 . It means that for each lemon in the compote should be exactly 2 apples and exactly 4 pears. You can't crumble up, break up or cut these fruits into pieces. These fruits — lemons, apples and pears — should be put in the compote as whole fruits. Your task is to determine the maximum total number of lemons, apples and pears from which Nikolay can cook the compote. It is possible that Nikolay can't use any fruits, in this case print 0 .
*/

/*@
    requires \valid(out);
    requires 1 <= a <= 1000;
    requires 1 <= b <= 1000;
    requires 1 <= c <= 1000;
    assigns *out;
    ensures *out == 7 * \min(a / 1, \min(b / 2, c / 4));
*/
void problem(int a, int b, int c, int *out)
{
    int d, e, f;
    d = a / 1;
    e = b / 2;
    f = c / 4;
    if (d <= e && d <= f)
        *out = 7 * d;
    else if (e <= d && e <= f)
        *out = 7 * e;
    else if (f <= d && f <= e)
        *out = 7 * f;
}
