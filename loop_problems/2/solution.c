/*
    Limak is a little polar bear. He has n balls, the i-th ball has size ti . Limak wants to give one ball to each of his three friends. Giving gifts isn't easy — there are two rules Limak must obey to make friends happy: No two friends can get balls of the same size. No two friends can get balls of sizes that differ by more than 2. For example, Limak can choose balls with sizes 4 , 5 and 3 , or balls with sizes 90 , 91 and 92 . But he can't choose balls with sizes 5 , 5 and 6 (two friends would get balls of the same size), and he can't choose balls with sizes 30 , 31 and 33 (because sizes 30 and 33 differ by more than 2 ). Your task is to check whether Limak can choose three balls that satisfy conditions above.

    Input
    The first input is an integer n ( 3 <= n <= 50 ) — the number of balls Limak has. The second input contains n integers in an array: t1 , t2 , ..., tn ( 1 <= ti <= 1000 ) where ti denotes the size of the i-th ball.

    Output
    output to variable *out, which is 1 if Limak can choose three balls of distinct sizes, such that any two of them differ by no more than 2. Otherwise, output 0. Examples

*/

/*@
    requires 3 <= n <= 50;
    requires \valid_read(t + (0..n-1));
    requires \valid(out);
    requires \separated(t + (0..n-1), out);
    requires \forall integer i; 0 <= i < n ==> 1 <= t[i] <= 1000;
    assigns *out;
    behavior can_choose:
        assumes \exists integer i, j, k;
            0 <= i < n &&
            0 <= j < n &&
            0 <= k < n &&
            t[i] == t[j] + 1 == t[k] + 2;
        ensures *out == 1;
    behavior cannot_choose:
        assumes !\exists integer i, j, k;
            0 <= i < n &&
            0 <= j < n &&
            0 <= k < n &&
            t[i] != t[j] &&
            t[j] != t[k] &&
            t[i] != t[k] &&
            t[i] == t[j] + 1 == t[k] + 2;
        ensures *out == 0;
    complete behaviors;
    disjoint behaviors;
*/
void bear_and_three_balls(int n, int t[], int *out)
{
    // Create an array for each size of ball to store if we have the ball
    int balls[1001] = {0};

    // Iterate over the balls and mark the size of the ball
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer j; 0 <= j < 1001 ==> (balls[j] == 1 || balls[j] == 0);
        loop invariant \forall integer j; 0 <= j < i ==> balls[t[j]] == 1;
        loop invariant \forall integer j; 0 <= j < 1001 && !(\exists integer k; 0 <= k < i && t[k] == j) ==> balls[j] == 0;
        loop assigns i, balls[0..1000];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++)
    {
        balls[t[i]] = 1;
    }

    // Iterate over the balls and check if we can find three balls that satisfy the conditions

    /*@
        loop invariant 0 <= i <= 999;
        loop invariant \forall integer j; 0 <= j < i ==> (balls[j] == 0 || balls[j + 1] == 0 || balls[j + 2] == 0);
        loop assigns i;
        loop variant 998 - i;
    */
    for (int i = 0; i <= 998; i++)
    {
        // Check if we can find three balls that satisfy the conditions
        if (balls[i] == 1 && balls[i + 1] == 1 && balls[i + 2] == 1)
        {
            *out = 1;
            return;
        }
    }
    *out = 0;
}