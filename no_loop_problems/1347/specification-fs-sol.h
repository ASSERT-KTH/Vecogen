/*@
    requires \valid(out_a) && \valid(out_b) && \valid(out_c);
    requires \valid(out_d) && \valid(out_e) && \valid(out_f);
    requires \valid(out_g) && \valid(out_h) && \valid(out_i);
    requires \separated(out_a, out_b, out_c, out_d, out_e, out_f, out_g, out_h, out_i);
    requires a == 0 && e == 0 && i == 0;
    requires 1 <= b <= 100000 && 1 <= c <= 100000 && 1 <= d <= 100000;
    requires 1 <= f <= 100000 && 1 <= g <= 100000 && 1 <= h <= 100000;
    requires ExistsSolution(b, c, d, f, g, h);
    assigns *out_a, *out_b, *out_c, *out_d, *out_e, *out_f, *out_g, *out_h, *out_i;
    ensures * out_a == (int) (a + b + c + d + e + f + g + h + i) / 2 - b - c;
    ensures * out_b == b;
    ensures * out_c == c;
    ensures * out_d == d;
    ensures * out_e == (int) (a + b + c + d + e + f + g + h + i) / 2 - d - f;
    ensures * out_f == f;
    ensures * out_g == g;
    ensures * out_h == h;
    ensures * out_i == (int) (a + b + c + d + e + f + g + h + i) / 2 - h - g;
*/
void restoreMagicSquare(int a, int b, int c, int d, int e, int f, int g, int h, int i, int *out_a, int *out_b, int *out_c, int *out_d, int *out_e, int *out_f, int *out_g, int *out_h, int *out_i);