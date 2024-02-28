int main()
{
    int n, start, end, myt, tramt, tramnow, d;
    scanf("%d %d %d", &n, &start, &end);
    scanf("%d %d", &tramt, &myt);
    scanf("%d %d", &tramnow, &d);
    int mytime = abs(start - end) * myt;
    int tramtime = 0;
    if ((start >= tramnow && d == 1) || (start <= tramnow && d == -1))
    {
        tramtime += abs(start - tramnow) * tramt;
    }
    else
    {
        if (d == -1)
        {
            tramtime += (tramnow + start) * tramt;
            d = 1;
        }
        else
        {
            d = -1;
            tramtime += (n - tramnow + n - start) * tramt;
        }
    }
    if ((end >= start && d == 1) || (end <= start && d == -1))
        tramtime += abs(start - end) * tramt;
    else
    {
        if (d == 1)
        {
            tramtime += (n - start + n - end) * tramt;
        }
        else
        {
            tramtime += (start + end) * tramt;
        }
    }
    if (mytime < tramtime)
        printf("%d", mytime);
    else
        printf("%d", tramtime);
    return 0;
}
