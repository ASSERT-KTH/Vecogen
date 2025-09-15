struct counter
{
    int seconds, minutes, hours;
};

struct counter c;

/*The function deals with a counter struct that tracks time in terms of seconds, minutes, and hours. The struct 'c' contains three integer fields: seconds, minutes, and hours. The function 'tick' is used to increment these fields appropriately, simulating the passage of one second of time.

  The goal of the function 'tick' is to accurately simulate the passage of one second of time within the constraints of a 24-hour clock. The function adjusts the seconds, minutes, and hours fields of the struct 'c' as necessary, ensuring that each field stays within its appropriate range (0-59 for seconds and minutes, 0-23 for hours). Different behaviors are defined for different initial states of the clock, covering all possible combinations of seconds, minutes, and hours.
  
  Input
  The function 'tick' does not take any explicit input, but it does operate on the global struct 'c'. Before the function is called, the fields of this struct should be initialized to represent a valid time: 'c.seconds' and 'c.minutes' should be integers in the range 0-59, and 'c.hours' should be an integer in the range 0-23.

  Output
  The function 'tick' does not have a traditional output, as it does not return a value. Instead, it modifies the global struct 'c'. The fields of this struct will represent the time one second after the function was called, with 'c.seconds', 'c.minutes', and 'c.hours' adjusted as appropriate. If the seconds field reaches 59, it is reset to 0 and the minutes field is incremented; if the minutes field reaches 59, it is reset to 0 and the hours field is incremented; if the hours field reaches 23, it is reset to 0.
*/

/*@
requires 0 <= c.seconds < 60;
  requires 0 <= c.minutes < 60;
  requires 0 <= c.hours < 24;
  assigns c.seconds, c.minutes, c.hours;
  behavior one:
    assumes c.seconds < 59 && c.minutes < 59;
    assigns c.seconds;
    ensures c.seconds == \old(c.seconds) + 1;
    ensures c.minutes == \old(c.minutes);
    ensures c.hours == \old(c.hours);
  behavior two:
    assumes c.seconds == 59 && c.minutes < 59;
    assigns c.seconds, c.minutes;
    ensures c.seconds == 0;
    ensures c.minutes == \old(c.minutes) + 1;
    ensures c.hours == \old(c.hours);
  behavior three:
    assumes c.seconds < 59 && c.minutes == 59;
    assigns c.seconds;
    ensures c.seconds == \old(c.seconds) + 1;
    ensures c.minutes == \old(c.minutes);
    ensures c.hours == \old(c.hours);
  behavior four:
    assumes c.seconds == 59 && c.minutes == 59 && c.hours < 23;
    assigns c.seconds, c.minutes, c.hours;
    ensures c.seconds == 0;
    ensures c.minutes == 0;
    ensures c.hours == \old(c.hours) + 1;
  behavior five:
    assumes c.seconds == 59 && c.minutes == 59 && c.hours == 23;
    ensures c.seconds == 0;
    ensures c.minutes == 0;
    ensures c.hours == 0;
  complete behaviors;
  disjoint behaviors;
*/

void tick() {
    if (++c.seconds > 59) {
        c.seconds = 0;
        if (++c.minutes > 59) {
            c.minutes = 0;
            if (++c.hours > 23) {
                c.hours = 0;
            }
        }
    }
}
