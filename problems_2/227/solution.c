#include <stdio.h>
unsigned long long int m = 1000000007;

/*
    requires 1 <= x <= 1000000000;
    requires 1 <= n <= 1000000000;
    ensurers \result == (x^n) % 1000000007;

*/
unsigned long long int bigmod(unsigned long long int x, unsigned long long int n)
{
    if (n == 0)
        return 1;
    if (n % 2 == 0)
    {
        unsigned long long int num = bigmod(x, n / 2);
        return ((num % m) * (num % m)) % m;
    }
    else
        return ((x % m) * (bigmod(x, n - 1) % m)) % m;
}
int main()
{
    unsigned long long int sum1 = 0, sum2 = 0, sum = 0, n, A, B, x;
    scanf("%llu %llu %llu %llu", &A, &B, &n, &x);
    if (A == 1)
        printf("%llu\\n", ((x % m) + ((B % m) * (n % m)) % m) % m);
    else
    {
        sum1 = bigmod(A, n) % m;
        sum2 = (sum1 - 1) % m;
        sum1 = ((sum1 % m) * (x % m)) % m;
        sum2 = ((sum2 % m) * (B % m)) % m;
        sum2 = ((sum2 % m) * (bigmod(A - 1, m - 2)) % m) % m;
        sum = ((sum1 % m) + (sum2 % m)) % m;
        printf("%llu\\n", sum % m);
    }
    return 0;
}
