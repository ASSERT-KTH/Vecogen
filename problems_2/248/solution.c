#include <math.h>

/*@
    requires \valid(out);
    requires 1 <= n <= 10000;
    requires 1 <= l <= 1000000000;
    requires 1 <= v1 < v2 <= 1000000000;
    requires 1 <= k <= n;
    assigns *out;
    behavior small:
        assumes n <= k;
        ensures *out == l / v2;
    behavior big_and_divisible:
        assumes n > k && n % k == 0;
        ensures *out == l / (1 + v1 * ((n / k) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k))) / v2 + (l - l / (1 + v1 * ((n / k) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k)))) / v1;
    behavior big_and_not_divisible:
        assumes n > k && n % k != 0;
        ensures *out == (l / (1 + v1 * ((n / k - 1) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k - 1)))) / v2 + (l - (l / (1 + v1 * ((n / k - 1) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k - 1))))) / v1;


*/
void problem(long n, long l, long v1, long v2, long k, long long *out)
{
    if (n <= k)
    {
        *out = l / v2;
    }
    else
    {
        if (n % k != 0)
        {
            *out = l / (1 + v1 * ((n / k) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k))) / v2 + (l - l / (1 + v1 * ((n / k) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k)))) / v1;
        }
        else
        {
            *out = (l / (1 + v1 * ((n / k - 1) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k - 1)))) / v2 + (l - (l / (1 + v1 * ((n / k - 1) / v2 + (v2 - v1) / 2 / (v1 + v2) * (n / k - 1))))) / v1;
        }
    }
}
