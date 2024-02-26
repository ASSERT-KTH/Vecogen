/*@
    requires 1 <= x <= 10000;
    requires 1 <= y <= 10000;
    requires 1 <= n <= 10000;
    requires  x <= n;
    behavior zero_clones:
        assumes (n * y + 99) / 100 - x <= 0;
        ensures \result == 0;
    behavior positive_clones:
        assumes (n * y + 99) / 100 - x > 0;
        ensures \result == (n * y + 99) / 100 - x;
*/
int problem(int n, int x, int y)
{
    int clones = (n * y + 99) / 100 - x;
    if (clones < 0)
    {
        clones = 0;
    }
    return clones;
}