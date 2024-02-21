#include <stdio.h>

/* mtype = {msg}; */
typedef enum { msg } mtype;

/* chan c = [10] of { mtype, int }; */
#define BUFFER_SIZE 10
typedef struct {
    mtype type;
    int value;
} message;
message c[BUFFER_SIZE];
int c_in = 0; /* next position to write */
int c_out = 0; /* next position to read */
int c_count = 0; /* number of elements in the buffer */

/* counters */
int sent = 0;
int received = 0;
int processed = 0;

/* value of "i*i"; i is the latest even value received in messages */
int isqr = 0;

/*@ axiomatic MessageQueue {
    predicate full{L}(int count) = count == BUFFER_SIZE;
    predicate empty{L}(int count) = count == 0;
    predicate valid_read{L}(int count) = 0 < count <= BUFFER_SIZE;
    predicate valid_write{L}(int count) = 0 <= count < BUFFER_SIZE;

    predicate in_bound{L}(int index) = 0 <= index < BUFFER_SIZE;
    predicate is_message{L}(message* msg) = \valid(msg) && in_bound((msg - c) % BUFFER_SIZE);
    predicate unchanged{L}(int old_val, int new_val) = old_val == new_val;
}
*/

/*@ requires valid_write{Pre}(c_count) && !full{Pre}(c_count);
    requires \valid(message);
    assigns c[c_in], c_count;
    ensures c_count == \old(c_count) + 1;
    ensures c_in == (\old(c_in) + 1) % BUFFER_SIZE;
    ensures is_message(&c[c_in]);
*/
void send_message(message msg) {
    c[c_in] = msg;
    c_in = (c_in + 1) % BUFFER_SIZE;
    c_count++;
    sent++;
}

/*@ requires valid_read{Pre}(c_count) && !empty{Pre}(c_count);
    assigns c[c_out], c_count;
    ensures c_count == \old(c_count) - 1;
    ensures c_out == (\old(c_out) + 1) % BUFFER_SIZE;
    ensures is_message(&c[\old(c_out)]);
*/
message receive_message() {
    message msg = c[c_out];
    c_out = (c_out + 1) % BUFFER_SIZE;
    c_count--;
    received++;
    return msg;
}

/*@ requires is_message(&msg) && msg.value % 2 == 0;
    assigns isqr, processed;
    ensures isqr == \old(msg.value * msg.value);
    ensures processed == \old(processed) + 1;
*/
void process_message(message msg) {
    isqr = msg.value * msg.value;
    processed++;
}

int main() {
    /* Initialize globals */
    sent = 0;
    received = 0;
    processed = 0;
    isqr = 0;

    /* Loop to send 100 messages */
    for (int i = 0; i < 100; i++) {
        message msg;
        msg.type = msg;
        msg.value = i;
        send_message(msg);
    }

    /* Loop to receive and process messages */
    while (received < 100) {
        message msg = receive_message();
        if (msg.value % 2 == 0)
            process_message(msg);
    }

    /* Assertions for post-conditions */
    //@ assert sent == 100;
    //@ assert received == 100;
    //@ assert processed == 50;

    return 0;
}
