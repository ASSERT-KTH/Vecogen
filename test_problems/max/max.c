// Create a function that returns the maximum of two integers
/*@     assigns \nothing;
        ensures \result >= x && \result >= y;
        ensures \result == x || \result == y;
*/
int max(int x, int y) { return (x > y) ? x : y; }