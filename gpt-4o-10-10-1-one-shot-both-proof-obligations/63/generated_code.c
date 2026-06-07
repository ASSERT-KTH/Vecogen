typedef unsigned char       tB;
typedef unsigned char       tU08;
typedef signed short int    tS16;
typedef signed long int     tS32;

#define GOOD_B(ss)          (((ss) >= (0x0A) ) ? (TRUE) : (FALSE))
#define SATURATE(x,min,max)     (((x)>(max)) ? (max) : (((x)>(min)) ? (x) : (min)))

#define CREATED_B(ss)       (((ss) > (0x00)) ? (TRUE) : (FALSE))
#define PENDINGOK           ((tU08) 0xFF)

#define TRUE                1
#define FALSE               0

typedef struct {
    tB val;
    tU08 ss;
} tBS;

typedef struct {
    tS32 val;
    tU08 ss;
} tS32S;

typedef enum
{
    RTDB_STEERING_OIL_LEVEL_LOW,
    RTDB_STEER_OLD_LEVEL_ERROR,
    RTDB_STEER_OIL_LEVEL_WARN,
    NUM_B_SIG_E
} SIGNAL_B;

typedef enum
{
    RTDB_SFLD_WARNING_TIMER,
    NUM_S32_SIG
} SIGNAL_S32;

#define SFLD_TI_UPDATE                  ((tS32) 10)
#define SFLD_TI_LIMIT                   ((tS32)20000)

tB readLastWarn;
tBS oilLevelError;

tBS rtdb_oilLevelLow;
tS32S rtdb_warningTimer;
tBS rtdb_oldLevelError;

tBS rtdb_oilLevelWarn;

/*
    This module controls the steering fluid level display.

    The following is a list of requirements it should adhere to.

    Definition 1: Signal
    A variable of type tBS, tS08S, or tS32S is called a signal.

    Definition 2: Signal Status
    The signal status for a signal S is a struct field named ss.

    Definition 3: Good Signal Status
    A signal S has good signal status whenever the macro GOOD_B(S.ss) evaluates to TRUE.

    Definition 4: Created Signal
    A signal S is considered to be created whenever the macro CREATED_B(S.ss) evaluates to TRUE.

    Definition 5: Bad Signal
    A signal is considered to be bad if and only if either:
    - The signal does not have good signal status, or
    - The macro GOOD_B evaluates to 0 for the signal.

    Definition 6: addTimer Condition
    The condition addTimer is considered to be TRUE if and only if:
    - The value of levelLow is TRUE, and
    - The signal status of levelLow is good.

    Definition 7: subTimer Condition
    The condition subTimer is considered to be TRUE if and only if:
    - The value of levelLow is FALSE, and
    - The signal status of levelLow is good.

    Definition 8: Error Detection (ErrorDetected)
    If the last warning (readLastWarn_B) was FALSE, and:
    - The old error signal (rtdb_oldLevelError_Bs) has value TRUE and good signal status,
    - Then the function ErrorDetected() returns SFLD_TI_LIMIT - SFLD_TI_UPDATE.
    - If the warning timer was not created or bad, then the function returns 0.
    - Otherwise, it returns the previous value of the warning timer.

    Definition 9: Low-Level Detection (LowLevelDetected)
    The function LowLevelDetected() determines the warning timer update:
    - If lowLevel is TRUE and has good signal status:
    - The warning timer is incremented by SFLD_TI_UPDATE from the result of ErrorDetected().
    - Otherwise:
    - It returns the value of ErrorDetected().

    Definition 10: Low-Level Not Detected (LowLevelNotDetected)
    The function LowLevelNotDetected() determines if the warning timer should decrease:
    - If lowLevel is FALSE and has good signal status:
    - The warning timer is decremented by SFLD_TI_UPDATE from LowLevelDetected().
    - Otherwise:
    - It returns the value of LowLevelDetected().

    Definition 11: Timer Computation (compute_timer)
    The function compute_timer() is used to determine the final warning timer value:
    - It takes the value from LowLevelNotDetected()
    - Ensures the value is saturated within [0, SFLD_TI_LIMIT].

    Requirements and Behaviors
    Requirement 1 (Req. 1)
    If readLastWarn_B was previously FALSE
    And the signal status of rtdb_oldLevelError_Bs was good,
    Then readLastWarn_B shall be set to TRUE.

    Behavior A1: Handling Negative Timer Values
    If enabled is TRUE, readLastWarn_B is TRUE, and rtdb_warningTimer is not bad,
    And if rtdb_warningTimer has a value less than -SFLD_TI_UPDATE:
    - If addTimer() was TRUE, then the warning timer shall be reset to 0.
    - If subTimer() was TRUE, then the warning timer shall be reset to 0.

    Behavior A2: Handling Small Timer Changes
    If enabled is TRUE, readLastWarn_B is TRUE, and rtdb_warningTimer is not bad,
    And if rtdb_warningTimer is within [-SFLD_TI_UPDATE, 0] or [0, SFLD_TI_UPDATE]:
    - If addTimer() was TRUE, then the warning timer increases by SFLD_TI_UPDATE.
    - If subTimer() was TRUE, then the warning timer resets to 0.

    Behavior A3: Timer Initialization
    If enabled is TRUE, readLastWarn_B is TRUE, and rtdb_warningTimer is either 0 or bad:
    - If addTimer() was TRUE, then the warning timer is set to SFLD_TI_UPDATE.
    - If subTimer() was TRUE, then the warning timer remains 0.

    Behavior A4: Normal Timer Increment and Decrement
    If enabled is TRUE, readLastWarn_B is TRUE, and rtdb_warningTimer is not bad,
    And rtdb_warningTimer is between SFLD_TI_UPDATE and SFLD_TI_LIMIT - SFLD_TI_UPDATE:
    - If addTimer() was TRUE, then the warning timer increases by SFLD_TI_UPDATE.
    - If subTimer() was TRUE, then the warning timer decreases by SFLD_TI_UPDATE.

    Behavior A5: Reaching the Timer Limit
    If rtdb_warningTimer is between SFLD_TI_LIMIT - SFLD_TI_UPDATE and SFLD_TI_LIMIT + SFLD_TI_UPDATE:
    - If addTimer() was TRUE, then the warning timer is set to SFLD_TI_LIMIT.
    - If subTimer() was TRUE, then the warning timer decreases by SFLD_TI_UPDATE.

    Behavior A6: Exceeding the Timer Limit
    If rtdb_warningTimer exceeds SFLD_TI_LIMIT + SFLD_TI_UPDATE:
    - If addTimer() was TRUE, then the warning timer is set to SFLD_TI_LIMIT.
    - If subTimer() was TRUE, then the warning timer is also set to SFLD_TI_LIMIT.

    Behavior A4_corner (Special Case Handling)
    If enabled is TRUE, readLastWarn_B is FALSE, and rtdb_oldLevelError_Bs is TRUE with good status:
    - If addTimer() was TRUE, then the warning timer is set to SFLD_TI_LIMIT.
    - If subTimer() was TRUE, then the warning timer is set to SFLD_TI_LIMIT - 2*SFLD_TI_UPDATE.

    Nominal Cases

    Behavior: nominal_enabled
    If rtdb_warningTimer == SFLD_TI_LIMIT, then rtdb_oilLevelWarn_Bs = TRUE.
    If rtdb_warningTimer == 0, then rtdb_oilLevelWarn_Bs = FALSE.

    Behavior: nominal_disabled
    If compute_timer(...) == SFLD_TI_LIMIT, then oilLevelError_Bs = TRUE.
    If compute_timer(...) == 0, then oilLevelError_Bs = FALSE.
*/

/*@ predicate badSignal(tU08 signal_status) =
    !CREATED_B(signal_status) || !GOOD_B(signal_status);
@*/

/*@ predicate addTimer(tBS levelLow) =
    levelLow.val == TRUE && GOOD_B(levelLow.ss) == TRUE;
*/

/*@ predicate subTimer(tBS levelLow) =
    levelLow.val == FALSE && GOOD_B(levelLow.ss) == TRUE;
*/

/*@ 
  logic tS32 ErrorDetected(tB readLastWarn, tBS oldError, tS32S oldTimer) = 
      readLastWarn == FALSE
      && oldError.val == TRUE 
      && GOOD_B(oldError.ss) == TRUE
      ? (tS32) (SFLD_TI_LIMIT - SFLD_TI_UPDATE)
      : !CREATED_B(oldTimer.ss) || !GOOD_B(oldTimer.ss)
         ? (tS32) 0 
         : oldTimer.val;
@*/

/*@ 
  logic tS32 LowLevelDetected(tB readLastWarn, tBS oldError, tS32S old_timer, tBS lowLevel) = 
    lowLevel.val == TRUE 
    && GOOD_B(lowLevel.ss) == TRUE
    ? (tS32) (ErrorDetected(readLastWarn, oldError, old_timer) + SFLD_TI_UPDATE)
    : ErrorDetected(readLastWarn, oldError, old_timer);
@*/

/*@ 
  logic tS32 LowLevelNotDetected(tB readLastWarn, tBS oldError, tS32S old_timer, tBS lowLevel) = 
    lowLevel.val == FALSE 
    && GOOD_B(lowLevel.ss) == TRUE
    ? (tS32) (LowLevelDetected(readLastWarn, oldError, old_timer, lowLevel) - SFLD_TI_UPDATE) 
    : LowLevelDetected(readLastWarn, oldError, old_timer, lowLevel);
@*/

/*@ 
  logic tS32 compute_timer(tB readLastWarn, tBS oldError, tS32S old_timer, tBS lowLevel) = 
      SATURATE(LowLevelNotDetected(readLastWarn, oldError, old_timer, lowLevel), (tS16)0, SFLD_TI_LIMIT);
@*/


/*@ 
    requires \valid_read(inputSignal);
    requires \valid(outputSignal);
    requires \valid(inputSignal);
    terminates \true;
    ensures \valid(outputSignal);
    assigns *outputSignal;
    exits \false;
    ensures (CREATED_B(\old(inputSignal->ss)) && GOOD_B(\old(inputSignal->ss)))
        ==> (\old(inputSignal->val) == outputSignal->val
        &&   \old(inputSignal->ss) == outputSignal->ss);
    ensures (CREATED_B(\old(inputSignal->ss)) && !GOOD_B(\old(inputSignal->ss)))
        ==> (outputSignal->val == defaultNotGood
        &&   outputSignal->ss == \old(inputSignal)->ss);
    ensures !CREATED_B(\old(inputSignal->ss))
        ==> (outputSignal->val == defaultNotExist
        &&   outputSignal->ss == PENDINGOK);
*/
void Rteg_chkS32Input(const tS32S * const inputSignal,
                      tS32S * const outputSignal,
                      tS32 defaultNotExist,
                      tS32 defaultNotGood)
{
    /* Mirror solution’s macros without including them */
    unsigned char created = (inputSignal->ss > 0);
    unsigned char good    = (inputSignal->ss >= 0x0A);

    if (!created) {
        outputSignal->val = defaultNotExist;
        outputSignal->ss  = (tU08)0xFF;  /* PENDINGOK */
    } else if (!good) {
        outputSignal->val = defaultNotGood;
        outputSignal->ss  = inputSignal->ss;
    } else {
        *outputSignal = *inputSignal;
    }
}

/*@
    requires 100000000 <= rtdb_warningTimer.val <= 100000000;
    assigns readLastWarn;
    assigns oilLevelError;
    assigns rtdb_oilLevelLow;
    assigns rtdb_warningTimer;
    assigns rtdb_oldLevelError;
    assigns rtdb_oilLevelWarn;
    
    ensures (\old(readLastWarn) == FALSE 
    && GOOD_B(\old(rtdb_oldLevelError.ss)) == TRUE)
            ==> readLastWarn == TRUE;

    behavior A1:
        assumes enabled == TRUE;
        assumes readLastWarn == TRUE;
        assumes !badSignal(rtdb_warningTimer.ss);
        assumes rtdb_warningTimer.val < 0 - SFLD_TI_UPDATE;
        ensures ADD: addTimer(\old(rtdb_oilLevelLow)) ==> rtdb_warningTimer.val == 0;
        ensures SUB: subTimer(\old(rtdb_oilLevelLow)) ==> rtdb_warningTimer.val == 0;

    behavior A2:
        assumes enabled == TRUE;
        assumes readLastWarn == TRUE;
        assumes !badSignal(rtdb_warningTimer.ss);
        assumes (rtdb_warningTimer.val >= 0 - SFLD_TI_UPDATE && rtdb_warningTimer.val < 0)
            ||  (rtdb_warningTimer.val > 0                       && rtdb_warningTimer.val <= 0 + SFLD_TI_UPDATE);
        ensures ADD: addTimer(\old(rtdb_oilLevelLow)) ==> rtdb_warningTimer.val == \old(rtdb_warningTimer.val) + SFLD_TI_UPDATE;
        ensures SUB: subTimer(\old(rtdb_oilLevelLow)) ==> rtdb_warningTimer.val == 0;

    behavior A3:
        assumes enabled == TRUE;
        assumes readLastWarn == TRUE;
        assumes rtdb_warningTimer.val == 0 || badSignal(rtdb_warningTimer.ss);
        ensures ADD: addTimer(\old(rtdb_oilLevelLow)) ==> rtdb_warningTimer.val == SFLD_TI_UPDATE;
        ensures SUB: subTimer(\old(rtdb_oilLevelLow)) ==> rtdb_warningTimer.val == 0;

    behavior A4:
        assumes enabled == TRUE;
        assumes readLastWarn == TRUE;
        assumes !badSignal(rtdb_warningTimer.ss);
        assumes rtdb_warningTimer.val > 0 + SFLD_TI_UPDATE;
        assumes rtdb_warningTimer.val <= SFLD_TI_LIMIT - SFLD_TI_UPDATE;
        ensures ADD: addTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == \old(rtdb_warningTimer.val) + SFLD_TI_UPDATE;
        ensures SUB: subTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == \old(rtdb_warningTimer.val) - SFLD_TI_UPDATE;

    behavior A5:
        assumes enabled == TRUE;
        assumes readLastWarn == TRUE;
        assumes !badSignal(rtdb_warningTimer.ss);
        assumes rtdb_warningTimer.val >= SFLD_TI_LIMIT - SFLD_TI_UPDATE;
        assumes rtdb_warningTimer.val <= SFLD_TI_LIMIT + SFLD_TI_UPDATE;
        ensures ADD: addTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == SFLD_TI_LIMIT;
        ensures SUB: subTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == \old(rtdb_warningTimer.val) - SFLD_TI_UPDATE;

    behavior A6:
        assumes enabled == TRUE;
        assumes readLastWarn == TRUE;
        assumes !badSignal(rtdb_warningTimer.ss);
        assumes rtdb_warningTimer.val > SFLD_TI_LIMIT + SFLD_TI_UPDATE;
        ensures ADD: addTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == SFLD_TI_LIMIT;
        ensures SUB: subTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == SFLD_TI_LIMIT;

    behavior A4_corner:
        assumes enabled == TRUE;
        assumes readLastWarn == FALSE;
        assumes rtdb_oldLevelError.val == TRUE;
        assumes GOOD_B(rtdb_oldLevelError.ss) == TRUE;
        ensures ADD: addTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == SFLD_TI_LIMIT;
        ensures SUB: subTimer(\old(rtdb_oilLevelLow))
            ==> rtdb_warningTimer.val == SFLD_TI_LIMIT - 2*SFLD_TI_UPDATE;

    behavior nominal_enabled:
        assumes enabled == TRUE;
        ensures N1: rtdb_warningTimer.val == SFLD_TI_LIMIT 
            ==> rtdb_oilLevelWarn.val == TRUE;
        ensures N2: (rtdb_warningTimer.val == SFLD_TI_LIMIT && readLastWarn == TRUE)
            ==> rtdb_oldLevelError.val == TRUE;
        ensures N3:  rtdb_warningTimer.val == 0  
            ==> rtdb_oilLevelWarn.val == FALSE;
        ensures N4: (rtdb_warningTimer.val == 0 && readLastWarn == TRUE)
            ==> rtdb_oldLevelError.val == FALSE;

    behavior nominal_disabled:
        assumes enabled == FALSE;
        ensures N1: compute_timer(
            \old(readLastWarn),
            \old(rtdb_oldLevelError),
            \old(rtdb_warningTimer),
            \old(rtdb_oilLevelLow)) == SFLD_TI_LIMIT 
            ==> oilLevelError.val == TRUE;
        ensures N2: compute_timer(
            \old(readLastWarn),
            \old(rtdb_oldLevelError),
            \old(rtdb_warningTimer),
            \old(rtdb_oilLevelLow)) == 0  
            ==> oilLevelError.val == FALSE;
*/

void sfld_10ms(tB enabled) {
    if (readLastWarn == FALSE && GOOD_B(rtdb_oldLevelError.ss) == TRUE) {
        readLastWarn = TRUE;
    }

    if (enabled == TRUE) {
        if (readLastWarn == TRUE) {
            if (!badSignal(rtdb_warningTimer.ss)) {
                if (rtdb_warningTimer.val < -SFLD_TI_UPDATE) {
                    rtdb_warningTimer.val = 0;
                } else if ((rtdb_warningTimer.val >= -SFLD_TI_UPDATE && rtdb_warningTimer.val < 0) ||
                           (rtdb_warningTimer.val > 0 && rtdb_warningTimer.val <= SFLD_TI_UPDATE)) {
                    if (addTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val += SFLD_TI_UPDATE;
                    } else if (subTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val = 0;
                    }
                } else if (rtdb_warningTimer.val == 0 || badSignal(rtdb_warningTimer.ss)) {
                    if (addTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val = SFLD_TI_UPDATE;
                    } else if (subTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val = 0;
                    }
                } else if (rtdb_warningTimer.val > SFLD_TI_UPDATE &&
                           rtdb_warningTimer.val <= SFLD_TI_LIMIT - SFLD_TI_UPDATE) {
                    if (addTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val += SFLD_TI_UPDATE;
                    } else if (subTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val -= SFLD_TI_UPDATE;
                    }
                } else if (rtdb_warningTimer.val >= SFLD_TI_LIMIT - SFLD_TI_UPDATE &&
                           rtdb_warningTimer.val <= SFLD_TI_LIMIT + SFLD_TI_UPDATE) {
                    if (addTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val = SFLD_TI_LIMIT;
                    } else if (subTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val -= SFLD_TI_UPDATE;
                    }
                } else if (rtdb_warningTimer.val > SFLD_TI_LIMIT + SFLD_TI_UPDATE) {
                    if (addTimer(rtdb_oilLevelLow) || subTimer(rtdb_oilLevelLow)) {
                        rtdb_warningTimer.val = SFLD_TI_LIMIT;
                    }
                }
            }
        } else if (rtdb_oldLevelError.val == TRUE && GOOD_B(rtdb_oldLevelError.ss) == TRUE) {
            if (addTimer(rtdb_oilLevelLow)) {
                rtdb_warningTimer.val = SFLD_TI_LIMIT;
            } else if (subTimer(rtdb_oilLevelLow)) {
                rtdb_warningTimer.val = SFLD_TI_LIMIT - 2 * SFLD_TI_UPDATE;
            }
        }

        if (rtdb_warningTimer.val == SFLD_TI_LIMIT) {
            rtdb_oilLevelWarn.val = TRUE;
        } else if (rtdb_warningTimer.val == 0) {
            rtdb_oilLevelWarn.val = FALSE;
        }
    } else {
        tS32 computed_timer = compute_timer(readLastWarn, rtdb_oldLevelError,
                                           rtdb_warningTimer, rtdb_oilLevelLow);
        if (computed_timer == SFLD_TI_LIMIT) {
            oilLevelError.val = TRUE;
        } else if (computed_timer == 0) {
            oilLevelError.val = FALSE;
        }
    }
}
