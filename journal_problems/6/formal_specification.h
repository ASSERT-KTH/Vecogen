/*@
requires \valid(tbl);
  requires \valid(tbl->data+(0 .. HASHTBL_LEN - 1));
  requires 0 <= d < HASHTBL_LEN;
  assigns tbl->data[d], tbl->size;
  ensures tbl->data[d].size == 0;
  ensures tbl->size == 0;
  ensures \result == 0;
*/

