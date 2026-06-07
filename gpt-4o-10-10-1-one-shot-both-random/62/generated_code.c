typedef unsigned char       tB;
typedef unsigned char       tU08;
typedef signed char         tS08;
typedef signed short int    tS16;
typedef signed long int     tS32;

typedef struct {
    tB val;
    tU08 ss_U08;
} tBS;

typedef struct {
    tU08 val;
    tU08 ss_U08;
} tU08S;

typedef struct {
    tS08 val;
    tU08 ss_U08;
} tS08S;

typedef struct {
    tS32 val;
    tU08 ss_U08;
} tS32S;

#define INT_MAX		            2147483647
#define MAX_S32                 ((tS32) 2147483647)

#define GOOD_B(ss)              ( ((ss) >= (0xA) ) ? (TRUE) : (FALSE))
#define CREATED_B(ss)           ( ((ss) > (0x00)) ? (TRUE) : (FALSE))

#define TRUE                    1
#define FALSE                   0

#define Intended                1
#define NotIntended             0

#define OK                      ((tU08) 0xFF)

#define REMOTE_REQUEST_OFF      ((tU08)0)
#define REMOTE_REQUEST_ON       ((tU08)1)
#define REMOTE_REQUEST_NONE     ((tU08)3)

#define VOLTAGE_NORMAL          ((tU08) 2)
#define VOLTAGE_LOW             ((tU08) 4)

#define NORMAL_OPERATION		((tU08)3)
#define EMERGENCY_STOP_LIMITED	((tU08)5)

// Input variables:
tU08S rtdb_state;
tBS rtdb_engineStart;
tBS rtdb_blackOut;
tBS rtdb_req;
tU08S rtdb_remoteReq;
tU08S rtdb_supplyVoltageLevel;

// Output variables:
tBS rtdb_truck;
tBS rtdb_trailer;

/*

This module controls the brake light activation.

The following is a list of requirements it should adhere to.

Definition 1:
A variable of type tBS, tS08S or tS32S is called a signal.

Definition 2:
The signal status for a signal S is a struct field named ss_U08.

Definition 3:
A signal S has good signal status whenever the macro GOOD_B(S.ss_U08) evaluates to true.

Definition 4:
A signal S is considered to be created whenever the macro CREATED_B(S.ss_U08) evaluates to true.

Definition 4:
A signal is considered to be bad if and only if either
the the signal does not have good signal status,
or the macro GOOD_B evaluates to 0 over the signal.

Definition 5:
The brake light is considered to be enabled if and only if
either the three conditions
rtdb_state has the value NORMAL_OPERATION
or rtdb_state has the value EMERGENCY_STOP_LIMITED
or the signal status of rtdb_state is bad
is evaluated to TRUE,
and
either rtdb_supplyVoltageLevel has bad signal status or rtdb_supplyVoltageLevel does not have the value VOLTAGE_LOW.

Definition 6:
The brake light is considered to be enabled and a good req has value TRUE if and only if
either the two conditions
the signal status of rtdb_req is bad
or rtdb_req has the value TRUE
is evaluated to TRUE,
and 
the brake light is considered to be enabled.

Definition 7:
The brake light is considered to be active if and only if
either rtdb_remoteReq has bad signal status or rtdb_remoteReq does not have the value REMOTE_REQUEST_OFF
and
either rtdb_engineStart has bad signal status or rtdb_engineStart has the value FALSE
and
either The brake light is considered to be enabled and a good req has value TRUE
or the signal status of rtdb_remoteReq is not bad and rtdb_remoteReq has value REMOTE_REQUEST_ON,

Req. 1:
If the brake light is not active,
then rtdb_truck shall have value FALSE
and rtdb_trailer shall have value FALSE.

Req. 2:
If either of the two conditions
rtdb_blackOut has a bad signal status,
or rtdb_blackOut has the value NotIntended,
and the brake light is active,
then rtdb_trailer shall have value TRUE.

Req. 3:
If rtdb_blackOut does not have a bad signal status,
and rtdb_blackOut has the value Intended,
and the brake light is active,
then rtdb_trailer shall have value FALSE.

Req. 4:
It is always the case that
rtdb_truck shall have the signal status value OK.

Req. 5:
It is always the case that
rtdb_trailer shall have the signal status value OK.
*/

/*@ 
    requires \valid(inSig_pBs);
    requires \valid(outSig_pBs);
    terminates \true;
    ensures \valid(outSig_pBs);
    assigns *outSig_pBs;
    exits \false;
    ensures (CREATED_B(\old(inSig_pBs->ss_U08)) && GOOD_B(\old(inSig_pBs->ss_U08)))
        ==> (\old(inSig_pBs->val) == outSig_pBs->val
        &&   \old(inSig_pBs->ss_U08) == outSig_pBs->ss_U08);
    ensures (CREATED_B(\old(inSig_pBs->ss_U08)) && !GOOD_B(\old(inSig_pBs->ss_U08)))
        ==> (outSig_pBs->val == defaultNotGood_B
        &&   outSig_pBs->ss_U08 == \old(inSig_pBs->ss_U08));
    ensures !CREATED_B(\old(inSig_pBs->ss_U08))
        ==> (outSig_pBs->val == defaultNotExist_B
        &&   outSig_pBs->ss_U08 == OK);
*/
void validateInputBool(const tBS * const inSig_pBs,
                       tBS * const outSig_pBs,
                       tB defaultNotExist_B,
                       tB defaultNotGood_B)
{
    tU08 ss = inSig_pBs->ss_U08;
    if (CREATED_B(ss)) {
        if (GOOD_B(ss)) {
            outSig_pBs->val    = inSig_pBs->val;
            outSig_pBs->ss_U08 = ss;
        } else {
            outSig_pBs->val    = defaultNotGood_B;
            outSig_pBs->ss_U08 = ss;
        }
    } else {
        outSig_pBs->val    = defaultNotExist_B;
        outSig_pBs->ss_U08 = OK;
    }
}

/*@ 
    requires \valid(inSig_pU08s);
    requires \valid(outSig_pU08s);
    terminates \true;
    ensures \valid(outSig_pU08s);
    assigns *outSig_pU08s;
    exits \false;
    ensures a: (CREATED_B(\old(inSig_pU08s->ss_U08)) && GOOD_B(\old(inSig_pU08s->ss_U08)))
        ==> (\old(inSig_pU08s->val) == outSig_pU08s->val
        &&   \old(inSig_pU08s->ss_U08) == outSig_pU08s->ss_U08);
    ensures b: (CREATED_B(\old(inSig_pU08s->ss_U08)) && !GOOD_B(\old(inSig_pU08s->ss_U08)))
        ==> (outSig_pU08s->val == defaultNotGood_U08
        &&   outSig_pU08s->ss_U08 == \old(inSig_pU08s->ss_U08));
    ensures c: !CREATED_B(\old(inSig_pU08s->ss_U08))
        ==> (outSig_pU08s->val == defaultNotExist_U08
        &&   outSig_pU08s->ss_U08 == OK);
*/
void validateInputU08(const tU08S * const inSig_pU08s,
                      tU08S * const outSig_pU08s,
                      tU08 defaultNotExist_U08,
                      tU08 defaultNotGood_U08)
{
    tU08 ss = inSig_pU08s->ss_U08;
    if (CREATED_B(ss)) {
        if (GOOD_B(ss)) {
            outSig_pU08s->val    = inSig_pU08s->val;
            outSig_pU08s->ss_U08 = ss;
        } else {
            outSig_pU08s->val    = defaultNotGood_U08;
            outSig_pU08s->ss_U08 = ss;
        }
    } else {
        outSig_pU08s->val    = defaultNotExist_U08;
        outSig_pU08s->ss_U08 = OK;
    }
}

/*@ predicate badSignal(tU08 signal_status) =
    !CREATED_B(signal_status) || !GOOD_B(signal_status);
  @*/

/*@ predicate brakeLightEnabled(tU08S state, tU08S supplyVoltageLevel) =
    (
        (  state.val == NORMAL_OPERATION 
        || state.val == EMERGENCY_STOP_LIMITED 
        || badSignal(state.ss_U08)
        )
        && (badSignal(supplyVoltageLevel.ss_U08) || supplyVoltageLevel.val != VOLTAGE_LOW)
    );
  @*/

  /*@ predicate ReqAndbrakeLightEnabled(
            tBS req,
            tU08S state,
            tU08S supplyVoltage
        ) =
    (
        (badSignal(req.ss_U08) || req.val == TRUE) 
        && brakeLightEnabled(state, supplyVoltage)
    );
  @*/

  /*@ predicate brakeLightActive(
            tU08S remoteReq,
            tU08S supplyVoltage,
            tBS req,
            tU08S state,
            tBS engineStart
        ) =
        (   (badSignal(remoteReq.ss_U08) || remoteReq.val != REMOTE_REQUEST_OFF)
        &&  (badSignal(engineStart.ss_U08) || engineStart.val == FALSE))
        &&  (
                ReqAndbrakeLightEnabled(req, state, supplyVoltage)
                ||
                ((!badSignal(remoteReq.ss_U08) && remoteReq.val == REMOTE_REQUEST_ON))
        );
  @*/

/*@
    assigns rtdb_truck, rtdb_trailer;

    ensures R1:
    !brakeLightActive(rtdb_remoteReq, rtdb_supplyVoltageLevel, rtdb_req, rtdb_state, rtdb_engineStart) 
    ==> (rtdb_truck.val == FALSE && rtdb_trailer.val == FALSE);

    ensures R2:
    ((badSignal(rtdb_blackOut.ss_U08) || rtdb_blackOut.val == NotIntended)
    && brakeLightActive(rtdb_remoteReq, rtdb_supplyVoltageLevel, rtdb_req, rtdb_state, rtdb_engineStart))
    ==> rtdb_trailer.val == TRUE;

    ensures R3:
    ((!badSignal(rtdb_blackOut.ss_U08) && rtdb_blackOut.val == Intended)
    && brakeLightActive(rtdb_remoteReq, rtdb_supplyVoltageLevel, rtdb_req, rtdb_state, rtdb_engineStart))
    ==> rtdb_trailer.val == FALSE;

    ensures R4:
        rtdb_truck.ss_U08 == OK;
    
    ensures R5:
        rtdb_trailer.ss_U08 == OK;
*/

void Brak_10ms(void) {
    tB reqValid = CREATED_B(rtdb_req.ss_U08) && GOOD_B(rtdb_req.ss_U08);
    tB stateValid = CREATED_B(rtdb_state.ss_U08) && GOOD_B(rtdb_state.ss_U08);
    tB supplyVoltageValid = CREATED_B(rtdb_supplyVoltageLevel.ss_U08) && GOOD_B(rtdb_supplyVoltageLevel.ss_U08);
    tB remoteReqValid = CREATED_B(rtdb_remoteReq.ss_U08) && GOOD_B(rtdb_remoteReq.ss_U08);
    tB engineStartValid = CREATED_B(rtdb_engineStart.ss_U08) && GOOD_B(rtdb_engineStart.ss_U08);
    tB blackOutValid = CREATED_B(rtdb_blackOut.ss_U08) && GOOD_B(rtdb_blackOut.ss_U08);

    tB brakeLightEnabled = (
        (!stateValid || rtdb_state.val == NORMAL_OPERATION || rtdb_state.val == EMERGENCY_STOP_LIMITED) &&
        (!supplyVoltageValid || rtdb_supplyVoltageLevel.val != VOLTAGE_LOW)
    );

    tB reqAndBrakeLightEnabled = (
        (!reqValid || rtdb_req.val == TRUE) && brakeLightEnabled
    );

    tB brakeLightIsActive = (
        (!remoteReqValid || rtdb_remoteReq.val != REMOTE_REQUEST_OFF) &&
        (!engineStartValid || rtdb_engineStart.val == FALSE) &&
        (
            reqAndBrakeLightEnabled ||
            (remoteReqValid && rtdb_remoteReq.val == REMOTE_REQUEST_ON)
        )
    );

    rtdb_truck.ss_U08 = OK;
    rtdb_trailer.ss_U08 = OK;

    if (!brakeLightIsActive) {
        rtdb_truck.val = FALSE;
        rtdb_trailer.val = FALSE;
    } else {
        if (!blackOutValid || rtdb_blackOut.val == NotIntended) {
            rtdb_trailer.val = TRUE;
        } else if (blackOutValid && rtdb_blackOut.val == Intended) {
            rtdb_trailer.val = FALSE;
        }
    }
}
