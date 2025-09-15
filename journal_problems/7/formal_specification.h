/*@
requires k == Max || k == Min;
  assigns \nothing;
  ensures \result == x || \result == y;
  behavior is_max:
    assumes k == Max;
    ensures \result >= x && \result >= y;
  behavior is_min:
    assumes k == Min;
    ensures \result <= x && \result <= y;
  complete behaviors;
  disjoint behaviors;
*/

