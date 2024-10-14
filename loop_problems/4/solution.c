/*
There are n walruses sitting in a circle. All of them are numbered in the clockwise order: the walrus number 2 sits to the left of the walrus number 1, the walrus number 3 sits to the left of the walrus number 2, ..., the walrus number 1 sits to the left of the walrus number n.

The presenter has m chips. The presenter stands in the middle of the circle and starts giving the chips to the walruses starting from walrus number 1 and moving clockwise. The walrus number i gets i chips. If the presenter can't give the current walrus the required number of chips, then the presenter takes the remaining chips and the process ends. Determine by the given n and m how many chips the presenter will get in the end.

Input
The first line contains two integers n and m (1 ≤ n ≤ 50, 1 ≤ m ≤ 10^4) — the number of walruses and the number of chips correspondingly.

Output
Print the number of chips the presenter ended up with.
*/

/*@
    requires 1 <= n <= 50;
    requires 1 <= m <= 10000;
    requires \valid(out);
    assigns *out;
    ensures 0 <= *out <= n;
    ensures \exists integer i; 0 <= i < n && *out + i * (i + 1) / 2 == m % (n * (n + 1) / 2);
*/
void calculate_chips(int n, int m, int *out)
{
    // Calculate the sum of the first n natural numbers
    // This will calculate optimally how many chips the presenter can give to all walruses
    int s = n * (n + 1) / 2;

    // This is the remaining chips the presenter will have
    int m_copy = m % s;
    *out = m_copy;

    /*@
        loop invariant i1: 1 <= i <= n;
        loop invariant i2: 0 <= *out <= m_copy;
        loop invariant i3: m_copy == *out + (i - 1) * i / 2;
        loop invariant i4: \exists integer j; 0 <= j < i && *out + j * (j + 1) / 2 == m_copy;
        loop assigns i, *out;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++)
    {
        if (*out >= i)
        {
            *out -= i;
        }
        else
        {
            break;
        }
    }
}