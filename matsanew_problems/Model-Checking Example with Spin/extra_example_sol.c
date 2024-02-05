/* A Promela model with two processes "sender" and "receiver", where the
   sender sends 100 messages to be received and processed by the receiver.
   Refer to the comments accompanying the code below. */

mtype = {msg};

/* a channel with buffer for 10 messages */
chan c = [10] of
{ mtype, int };

/* all the globals below are automatically initialized to 0 */

/* counters */
int sent, received, processed;

/* value of "i*i"; i is the latest even value received in messages */
int isqr;

/* LTL formulae to specify various properties about the global variables */

/* Valid range of variables sent, received and processed (in all states) */
ltl p1{[](0 <= sent &&sent <= 100 && 0 <= received &&received <= sent && 0 <= processed &&processed <= received / 2)}

/* Since isqr is the square of an even "i", it must be a multiple of 4
   (in all states) */
ltl p2{[](isqr % 4 == 0)}

/* In any state with (processed >= 10), (isqr >= 400) must hold */
ltl p3{[]((processed >= 10)->(isqr >= 400))}

/* Some state must be reached with (isqr == 900) ("i" becomes 30) */
ltl p4{<>(isqr == 900)}

/* Some state must be reached with (isqr == 64), and till then (sent < 20)
   must hold */
ltl p5{(sent < 20) U(isqr == 64)}

/* After a state with (sent >= 50), some state must be reached with
   (processed >= 25) */
ltl p6{[]((sent >= 50)-><>(processed >= 25))}

/* After a state with (sent == 100), some state must be reached with
   (received == 100) and (processed == 50) */
ltl p7{[]((sent == 100)-><>(received == 100 &&processed == 50))}

/* The sender process */
active proctype
sender()
{
    /* Send 100 messages with "int" field from 1 to 100. Note that the
       channel c can buffer only upto 10 messages at a time, so waiting
       may happen. */

    do
        ::sent < 100->atomic
        {
            c !msg(sent + 1);
            sent++;
        }

    ::else->break;
    od
}

/* The receiver process */
active proctype receiver()
{
    int i;

    /* Receive each of the 100 messages, while tracking the count in
       "received". Whenever the channel is empty, waiting will happen.
       The messages with even value "i" in the "int" field are "processed"
       by updating "isqr" to "i*i". */

    do
        ::received < 100->c ? msg(i);

    /* example of an assertion */
    assert(i >= 1 && i <= 100);

    received++;

    if
        ::i % 2 == 0->isqr = i * i;
    processed++;
    ::else fi

        ::else->break;
    od
}