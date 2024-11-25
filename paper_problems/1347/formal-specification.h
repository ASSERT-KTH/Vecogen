/*@ predicate ExistsSolution(integer b, integer c, integer d, integer f, integer g, integer h) =
    \exists integer a, e, i;
    0 <= a <= 100000 && 0 <= e <= 100000 && 0 <= i <= 100000 &&
    a + b + c == a + d + g && a + b + c == b + e + h && a + b + c == c + f + i &&
    a + b + c == a + e + i && a + b + c == c + e + g && a + b + c == d + e + f &&
    a + b + c == d + e + f && a + b + c == g + h + i;

*/
/*@ predicate IsValidSolution(integer a, integer b, integer c, integer d, integer e, integer f, integer g, integer h, integer i) =
    \exists integer sum;
    0 <= a <= 100000 && 0 <= b <= 100000 && 0 <= c <= 100000 &&
    0 <= d <= 100000 && 0 <= e <= 100000 && 0 <= f <= 100000 &&
    0 <= g <= 100000 && 0 <= h <= 100000 && 0 <= i <= 100000 &&
    0 <= sum && sum == a + b + c && sum == d + e + f && sum == g + h + i &&
    sum == a + d + g && sum == b + e + h && sum == c + f + i &&
    sum == a + e + i && sum == c + e + g;
*/

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
    ensures *out_b == b && *out_c == c && *out_d == d && *out_f == f && *out_g == g && *out_h == h;
    ensures IsValidSolution(*out_a, *out_b, *out_c, *out_d, *out_e, *out_f, *out_g, *out_h, *out_i);
*/