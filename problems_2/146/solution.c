int main()
{
    long long int s, n, k, b;
    scanf("%I64d%I64d", &n, &k);
    if (k >= (n / 2))
    {
        s = ((n - 1) * n) / 2;
        printf("%I64d", s);
    }
    else
    {
        b = n - 1;
        s = ((k * ((2 * b) - (k - 1))) / 2) + (n - (2 * k)) * k + (((k - 1) * (k)) / 2);
        printf("%I64d", s);
    }
}