/*
    B. The Easter Rabbit laid n eggs in a circle and is about to paint them. Each egg should be painted one color out of 7: red, orange, yellow, green, blue, indigo or violet.  Also, the following conditions should be satisfied: Each of the seven colors should be used to paint at least one egg. Any four eggs lying sequentially should be painted different colors. Help the Easter Rabbit paint the eggs in the required manner. We know that it is always possible.

    Input
    The only line contains an integer n — the amount of eggs ( 7 ≤ n ≤ 100 ).

    Output
    Output an array consisting of n integers. The i-th integer should describe the color of the i-th egg in the order they lie in the circle. The colors should be represented as follows: 0 refers to  red, 1 refers to orange, 2 refers to yellow, 3 refers to green, 4 refers to blue, 5 refers to indigo, 6 refers to violet. If there are several answers, output any of them.
*/

/*@
    requires 7 <= n <= 100;
    requires \valid(out + (0 .. n-1));
    assigns out[0 .. n-1];
    ensures \forall integer i; 0 <= i < n ==> 0 <= out[i] <= 6;
    ensures \forall integer c; 0 <= c <= 6 ==> \exists integer i; 0 <= i < n && out[i] == c;
    ensures \forall integer i; 0 <= i < n-3 ==>
        out[i] != out[i+1] &&
        out[i] != out[i+2] &&
        out[i] != out[i+3] &&
        out[i+1] != out[i+2] &&
        out[i+1] != out[i+3] &&
        out[i+2] != out[i+3];
    // ensures out[n-1] != out[0] &&
        // out[n-1] != out[1] &&
        // out[n-1] != out[2] &&
        // out[n-2] != out[0] &&
        // out[n-2] != out[1] &&
        // out[n-3] != out[0];
*/
void EasterEggs(int n, int *out)
{
    int pattern[7] = {0, 1, 2, 3, 4, 5, 6};

    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer x; 0 <= x < i ==> out[x] == pattern[x % 7];
        loop assigns out[0..n - 1], i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++)
    {
        out[i] = pattern[i % 7];
    }
}