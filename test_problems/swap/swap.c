void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
    return;
}

void main()
{
    int a = 1;
    int b = 2;
    swap(&a, &b);
    return;
}