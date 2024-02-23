/*  A. Save Luke
    Luke Skywalker got locked up in a rubbish shredder between two presses. R2D2 is already working on his rescue, but Luke needs to stay alive as long as possible. For simplicity we will assume that everything happens on a straight line, the presses are initially at coordinates 0 and L , and they move towards each other with speed v 1 and v 2 , respectively. Luke has width d and is able to choose any position between the presses. Luke dies as soon as the distance between the presses is less than his width. Your task is to determine for how long Luke can stay alive. */

/*@
    requires d > 0;
    requires L > 0;
    requires v1 > 0;
    requires v2 > 0;
    assigns \nothing;
    ensures \result >= 0;
    ensures \result == (L - d) / (v1 + v2);
*/
int problem(int d, int L, int v1, int v2);