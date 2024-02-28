int main()
{
    int n, m, k;
    scanf("%d %d %d", &n, &m, &k);
    k--;       printf ("%d %d %c", k / (2 * m) + 1, k % (m * 2) / 2 + 1, k % 2 ? \'R\' : \'L\');       return 0;   }
