#include <stdio.h>
#include <math.h>
int main()
{
    int a, b, c, d, e;
    scanf("%d %d %d", &a, &b, &c);
    if (c >= 0)
    {
        if (c <= a - b)
            d = b + c;
        else
            d = (c - a + b) % a;
        if (d == 0)
            d = a;
    }
    if (c < 0)
    {
        if (abs(c) <= b - 1)
        {
            d = b + c;
        }
        else
        {
            e = (abs(c) - b + 1) % a;
            d = a - e + 1;
        }
        if (e == 0)
        {
            d = 1;
        }
    }
    printf("%d", d);
    return 0;
}