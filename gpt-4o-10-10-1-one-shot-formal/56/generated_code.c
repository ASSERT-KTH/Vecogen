/*Captain Bill the Hummingbird and his crew recieved an interesting challenge offer. Some stranger gave them a map, potion of teleportation and said that only this potion might help them to reach the treasure. Bottle with potion has two values x and y written on it. These values define four moves which can be performed using the potion: Map shows that the position of Captain Bill the Hummingbird is (x1, y1) and the position of the treasure is (x2 , y2) . You task is to tell Captain Bill the Hummingbird whether he should accept this challenge or decline. If it is possible for Captain to reach the treasure using the potion then output 1 , otherwise 0 (without quotes). The potion can be used infinite amount of times.

    Input
    The input contains six integer numbers x1 , y1 , x2 , y2 (-100000 <= x1 , y1 , x2 , y2 <= 100000) — positions of Captain Bill the Hummingbird and treasure respectively and also integer numbers x, y (1 <= x, y <= 100000 ) — values on the potion bottle.

    Output
    Return 1 if it is possible for Captain to reach the treasure using the potion, otherwise return 0. Examples
*/

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

int can_reach_treasure(int x1, int y1, int x2, int y2, int x, int y) {
    int dx = x2 - x1;
    int dy = y2 - y1;
    
    if (dx % x != 0 || dy % y != 0) {
        return 0;
    }
    
    int dx_div_x = dx / x;
    int dy_div_y = dy / y;
    
    if ((dx_div_x % 2 + 2) % 2 != (dy_div_y % 2 + 2) % 2) {
        return 0;
    }
    
    return 1;
}
