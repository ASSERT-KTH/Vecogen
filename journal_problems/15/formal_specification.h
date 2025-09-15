/*@
requires \true;
    assigns \nothing;
    ensures 1 <= \result <= 3;
    ensures (\result == 3) ==> a == b && b == c;
    ensures (\result == 2) ==> (a == b || b == c || a == c) && !(a == b && b == c);
    ensures (\result == 1) ==> a != b && b != c && a != c;
@
*/

