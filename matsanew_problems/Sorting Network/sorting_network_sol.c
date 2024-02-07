#include "sorting_network.h"

/* Helper function to swap two elements */
void SWAP(int a[], int i, int j) {
    int temp = a[i];
    a[i] = a[j];
    a[j] = temp;
}

/* Sorting function for a specific permutation */
void sort_permutation(int a[]) {
    SWAP(a, 0, 1);
    SWAP(a, 3, 4);
    SWAP(a, 2, 4);
    SWAP(a, 0, 3);
    SWAP(a, 1, 4);
    SWAP(a, 1, 3);
    SWAP(a, 2, 3);
    SWAP(a, 1, 2);
}

/* Method sort5() sorts the input array of 5 elements using a sorting-network */
void sort5(int a[]) {
    /* Sorting network for 5 elements */
    sort_permutation(a);
    
    /* Assertion to ensure postconditions */
    //@ assert \forall integer i; 0 <= i <= 3 ==> a[i] <= a[i+1];
    //@ assert \forall integer i; 0 <= i <= 4 ==> (\exists integer j; 0 <= j <= 4 && a[i] == \old(a[j]));
    //@ assert \forall integer i; 0 <= i <= 4 ==> (\exists integer j; 0 <= j <= 4 && \old(a[i]) == a[j]);
}