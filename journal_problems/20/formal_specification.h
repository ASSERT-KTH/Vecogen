/*@
requires costPrice >= 0;
  requires sellingPrice >= 0;
  assigns \nothing;
  ensures (costPrice > sellingPrice)  ==> \result == costPrice - sellingPrice;
  ensures (costPrice <= sellingPrice) ==> \result == 0;
@
*/

