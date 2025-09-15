/*
  The program operates on a custom data structure, specifically a hash table (Hashtbl) that contains an array of 'Buckets'. Each Bucket has an integer value 'b' and a size value. The array of Buckets is of fixed length, defined by the constant HASHTBL_LEN. The hash table also has a size value. The 'add' function is used to manipulate this data structure. 

  The function 'add' is designed to add an element to the Hash table. The function is tasked with setting the size of the bucket specified by the input 'd' to zero and also resetting the size of the whole table to zero. It should return a zero after performing these operations.

  Input
  The function 'add' takes in two inputs:
  - A pointer to the Hash table (Hashtbl *tbl) which should be valid and contain a valid data array from the index 0 till HASHTBL_LEN - 1.
  - An integer 'd' which is the index of the bucket in the data array of the hash table. The value of 'd' should be greater than or equal to 0 and less than HASHTBL_LEN.

  Output
  The function 'add' modifies the sizes of the specified bucket and the hash table to zero. Post execution, the size of the bucket at index 'd' in the hash table and the size of the hash table should be zero. The function then returns an integer value of zero.
*/

#define HASHTBL_LEN 17

typedef struct {
  int b;
  int size;
} Buckets;

typedef struct {
  Buckets data[HASHTBL_LEN];
  int size;
} Hashtbl;

/*@
  requires \valid(tbl);
  requires \valid(tbl->data+(0 .. HASHTBL_LEN - 1));
  requires 0 <= d < HASHTBL_LEN;
  assigns tbl->data[d], tbl->size;
  ensures tbl->data[d].size == 0;
  ensures tbl->size == 0;
  ensures \result == 0;
*/
int add(Hashtbl *tbl, int d) {
  unsigned int h = d;
  tbl->data[h].size = 0;
  tbl->size = 0;
  return 0;
}
