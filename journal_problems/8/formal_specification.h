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

