/* A. Theatre Square
    Theatre Square in the capital city of Berland has a rectangular shape with the size n × m meters. On the occasion of the city's anniversary, a decision was taken to pave the Square with square granite flagstones. Each flagstone is of the size a × a . What is the least number of flagstones needed to pave the Square? It's allowed to cover the surface larger than the Theatre Square, but the Square has to be covered. It's not allowed to break the flagstones. The sides of flagstones should be parallel to the sides of the Square.
*/

/*@
    requires \valid(out);
    requires 1 <= n <= 1000000000;
    requires 1 <= m <= 1000000000;
    requires 1 <= a <= 1000000000;
    assigns *out;
    ensures *out == ((n+a-1)/a) * ((m+a-1)/a);
*/
void problem(int n, int m, long a, long *out);