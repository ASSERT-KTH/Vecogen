#include "gcd.h"

uint euclid(uint A, uint B) {
    /*@
      loop invariant A > 0 && B > 0;
      loop invariant A <= Loop_Entry_A && B <= Loop_Entry_B;
      loop assigns A, B;
      loop variant A + B; // Loop variant
      */
    {
        //@ ghost uint Loop_Entry_A = A;
        //@ ghost uint Loop_Entry_B = B;
    }

    while (A != B) {
        // Assertion: A and B remain positive throughout the loop
        //@ assert A > 0 && B > 0;

        // Assertion: A and B are non-increasing during each loop iteration
        //@ assert A <= Loop_Entry_A && B <= Loop_Entry_B;

        if (A > B) {
            A = A - B;
        } else {
            B = B - A;
        }
    }

    // Assertion: At loop termination, A and B are equal
    //@ assert A == B;

    return A; // or B, as they are equal at this point
}
