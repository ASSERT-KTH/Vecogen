/*@
    requires \valid(out);
    requires 1 <= l <= 1000;
    requires 1 <= p <= 500;
    assigns *out;
    ensures (*out) ==   (l / p);
    ensures (*out * p) ==   (l);

*/
void calculateSecondSpellCollisionDistance(int l, int p, int q, double *out)
{
    *out = l / p;
}

int main()
{
}