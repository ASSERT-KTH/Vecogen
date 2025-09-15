/*@
predicate can_reach(int x1, int y1, int x2, int y2, int x, int y) =
    \let dx = x2 - x1;
    \let dy = y2 - y1;
    dx % x == 0 &&
    dy % y == 0 &&
    \abs((dx / x) % 2) == \abs((dy / y) % 2);
*/

/*@
requires -100000 <= x1 <= 100000;
    requires -100000 <= y1 <= 100000;
    requires -100000 <= x2 <= 100000;
    requires -100000 <= y2 <= 100000;
    requires 1 <= x <= 100000;
    requires 1 <= y <= 100000;
    assigns \nothing;
    ensures \result == 1 ==> can_reach(x1, y1, x2, y2, x, y);
    ensures \result == 0 ==> !can_reach(x1, y1, x2, y2, x, y);
    ensures \result == 0 || \result == 1;
*/

