/*@
predicate submatcher_0(char *x) = x[0] == '\0' || (x[0] == 'a' && submatcher_0(x + 1));
*/

/*@
requires ((strlen(x22)>=0) && \valid_read(x22+(0..strlen(x22))));
  decreases strlen(x22);
  assigns \nothing;
  ensures \result <==> submatcher_0(x22);
*/