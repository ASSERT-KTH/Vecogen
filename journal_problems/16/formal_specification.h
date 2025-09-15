/*@
requires \true;
  assigns \nothing;
  ensures \result == a || \result == b || \result == c;
  ensures (\result >= a && \result <= b)
        || (\result >= b && \result <= a)
        || (\result >= a && \result <= c)
        || (\result >= c && \result <= a)
        || (\result >= b && \result <= c)
        || (\result >= c && \result <= b);
*/

