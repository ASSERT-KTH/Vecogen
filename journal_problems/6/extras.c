#define HASHTBL_LEN 17

typedef struct
{
  int b;
  int size;
} Buckets;

typedef struct
{
  Buckets data[HASHTBL_LEN];
  int size;
} Hashtbl;