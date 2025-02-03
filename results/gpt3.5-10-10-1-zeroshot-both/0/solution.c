
void calculateHipsterSockDays(int a, int b, int *out1, int *out2)
{
    if (a > b)
    {
        *out1 = b;
        *out2 = (a - b) / 2;
    }
    else if (b > a)
    {
        *out1 = a;
        *out2 = (b - a) / 2;
    }
    else
    {
        *out1 = a;
        *out2 = 0;
    }
}
