typedef unsigned char      tB;
typedef unsigned char      tU08;
typedef signed char        tS08;
typedef unsigned short int tU16;
typedef signed short int   tS16;
typedef unsigned long int  tU32;
typedef signed long int    tS32;
typedef unsigned long long tU64;
typedef signed   long long tS64;
typedef float              tF32;
typedef double             tF64;
typedef unsigned char      ss_U08;

typedef struct {
    tU08 val_U08;
    tU08 ss_U08;
} tU08S;

typedef struct {
    tB   val_B;
    tU08 ss_U08;
} tBS;

typedef struct {
    tF32 val_F32;
    tU08 ss_U08;
} tF32S;

typedef struct {
    tS08 val_S08;
    tU08 ss_U08;
} tS08S;

#define MOTOROVERSPEEDLIMIT_F32     ((tF32) 6000)
#define GEARRATIO_F32               ((tF32) 3.320)
#define WAITTIMESET_U08             ((tU08) 2000)
#define FLAWLESS_B(ss_U08)          ((((ss_U08) & (0xFF)) == (0xFF) ) ? (TRUE) : (FALSE))
#define SAMPLETIME_U16              ((tU16) 10)
#define TRUE (1)
#define FALSE (0)

/* local state */
tB          lowMagneticValue_B;
tB          highMagneticValue_B;
tU08        lowMagneticValueMeasurement_U08;
tU08        highMagneticValueMeasurement_U08;
tS08S       currentGear_S08s;
tF32S       electricMotorMeasuredSpeed_F32s;
tF32S       intermediateShaftSpeed_F32s;


/* Reading from */
tS08S rtdb_current_gear;
tF32S rtdb_intermediate_shaft_speed;
tF32S rtdb_electric_motor_measured_speed;
tU08S rtdb_low_magnetic_value_measurement;
tU08S rtdb_high_magnetic_value_measurement;

/* Writing to */
tB rtdb_low_magnetic_value;
tB rtdb_high_magnetic_value;

/*This module handles a safe activation of the magnetic valves

    The following is a list of requirements the code should adhere to.

    Req. 1:
    If the signal of rtdb_low_magnetic_value_measurement is not FLAWLESS,
        or the signal of rtdb_high_magnetic_value_measurement is not FLAWLESS,
    then the low side magnetic valve activation shall be blocked by setting rtdb_low_magnetic_value to FALSE
        and the high side magnetic valve activation shall be blocked by setting rtdb_high_magnetic_value to FALSE.

    Req. 2:  
    If the signal of rtdb_current_gear is not FLAWLESS
        and the signal of rtdb_intermediate_shaft_speed is not FLAWLESS
    then the low side magnetic valve activation shall be blocked by setting rtdb_low_magnetic_value to FALSE
        and the high side magnetic valve activation shall be blocked by setting rtdb_high_magnetic_value to FALSE.

    Req. 3:
    If the signal of rtdb_electric_motor_measured_speed is not FLAWLESS,
    then the low side magnetic valve activation shall be blocked by setting rtdb_low_magnetic_value to FALSE
        and the high side magnetic valve activation shall be blocked by setting rtdb_high_magnetic_value to FALSE.

    Req. 4:
    If the signal of rtdb_low_magnetic_value_measurement is FLAWLESS
        and the signal of rtdb_high_magnetic_value_measurement is FLAWLESS
        and the signal of rtdb_intermediate_shaft_speed is FLAWLESS 
        and the signal of rtdb_electric_motor_measured_speed is FLAWLESS 
        and either the value of rtdb_electric_motor_measured_speed > MOTOROVERSPEEDLIMIT_F32 RPM
            or the calculated input shaft speed rtdb_intermediate_shaft_speed.val_F32 * GEARRATIO_F32 > MOTOROVERSPEEDLIMIT_F32 RPM
    then the low side magnetic valve activation shall be blocked by setting rtdb_low_magnetic_value to FALSE
        and the high side magnetic valve activation shall be blocked by setting rtdb_high_magnetic_value to FALSE.

    Req. 5:
    If the signal of rtdb_intermediate_shaft_speed is not FLAWLESS
        and the signal of rtdb_current_gear is FLAWLESS
        and the value of rtdb_current_gear is not 0
    then the low side magnetic valve activation shall be blocked by setting rtdb_low_magnetic_value_measurement to FALSE
        and the high side magnetic valve activation shall be blocked by setting rtdb_high_magnetic_value_measurement to FALSE.

    Utility req. 1:
    A variable of type tU08, tBS, tF32 or tS08 is called a signal.

    Utility req. 2:
    The signal status for a signal S is a struct field named ss_U08.

    Utility req. 3:
    A signal S has FLAWLESS signal status whenever the macro FLAWLESS_B(S.ss_U08) evaluates to true.
*/


/*local state
*/


/*Reading from
*/


/*Writing to
*/


/*-----------------------------------------------------------
     * Inline rtdbInput()
     *-----------------------------------------------------------
*/


/*-----------------------------------------------------------
     * Inline chckMvFbSs()
     *-----------------------------------------------------------
*/


/*-----------------------------------------------------------
     * Inline chckEmOverSpeed()
     *-----------------------------------------------------------
*/


/*-----------------------------------------------------------
     * Inline ChckSsInterShftAndCurrGear()
     *-----------------------------------------------------------
*/


/*Intermediate shaft is flawless
*/


/*Intermediate shaft not flawless; check current gear
*/


/*-----------------------------------------------------------
     * Replicate the logic of the final if-else from sgmm_10ms,
     * inlining blockBoth() and noBlock().
     *-----------------------------------------------------------
*/


/*blockBoth() inlined
*/


/*blockBoth() inlined
*/


/*blockBoth() inlined
*/


/*noBlock() inlined
*/

/*@
predicate SignalFlawless{L}(tBS signal_E) = FLAWLESS_B(\at(signal_E.ss_U08, L)) == TRUE;
    predicate SignalFlawless{L}(tU08S signal_E) = FLAWLESS_B(\at(signal_E.ss_U08, L)) == TRUE;
    predicate SignalFlawless{L}(tF32S signal_E) =  FLAWLESS_B(\at(signal_E.ss_U08, L)) == TRUE;
    predicate SignalFlawless{L}(tS08S signal_E) = FLAWLESS_B(\at(signal_E.ss_U08, L)) == TRUE;
    predicate SignalFlawless{L}(tS08 signal_E) = FLAWLESS_B(\at(signal_E, L)) == TRUE;
    predicate SignalFlawless{L}(tU08 signal_E) = FLAWLESS_B(\at(signal_E, L)) == TRUE;
    predicate SignalNotFlawless{L}(tBS signal_E) = FLAWLESS_B(\at(signal_E.ss_U08, L)) == FALSE;
    predicate SignalNotFlawless{L}(tU08S signal_E) = FLAWLESS_B(\at(signal_E.ss_U08, L)) == FALSE;
    predicate SignalNotFlawless{L}(tF32S signal_E) = FLAWLESS_B(\at(signal_E.ss_U08, L)) == FALSE;
    predicate SignalNotFlawless{L}(tS08S signal_E) = FLAWLESS_B(\at(signal_E.ss_U08, L)) == FALSE;
    predicate SignalNotFlawless{L}(tS08 signal_E) = FLAWLESS_B(\at(signal_E, L)) == FALSE;
    predicate SignalNotFlawless{L}(tU08 signal_E) = FLAWLESS_B(\at(signal_E, L)) == FALSE;
@
*/

/*@
predicate HighAndLowBlocked = 
    rtdb_low_magnetic_value == FALSE && rtdb_high_magnetic_value == FALSE;
@
*/

/*@
predicate HighAndLowNotBlocked = 
    rtdb_low_magnetic_value == TRUE && rtdb_high_magnetic_value == TRUE;
@
*/

/*@
assigns lowMagneticValue_B;
    assigns highMagneticValue_B;
    assigns lowMagneticValueMeasurement_U08;
    assigns highMagneticValueMeasurement_U08;
    assigns currentGear_S08s;
    assigns electricMotorMeasuredSpeed_F32s;
    assigns intermediateShaftSpeed_F32s;
    assigns rtdb_low_magnetic_value, rtdb_high_magnetic_value;

    // ----------------------------- Main requirements -----------------------------------

    ensures RQ1:
    (   SignalNotFlawless{Old}(rtdb_low_magnetic_value_measurement)
    ||  SignalNotFlawless{Old}(rtdb_high_magnetic_value_measurement))
        ==> HighAndLowBlocked;

    ensures RQ2:
    (   SignalNotFlawless{Old}(rtdb_current_gear)
    &&  SignalNotFlawless{Old}(rtdb_intermediate_shaft_speed))
        ==> HighAndLowBlocked;

    ensures RQ3: 
    (   SignalNotFlawless{Old}(rtdb_electric_motor_measured_speed))
        ==> HighAndLowBlocked;

    ensures RQ4: 
    (   SignalFlawless{Old}(rtdb_low_magnetic_value_measurement)
    &&  SignalFlawless{Old}(rtdb_high_magnetic_value_measurement)
    &&  SignalFlawless{Old}(rtdb_intermediate_shaft_speed)
    &&  SignalFlawless{Old}(rtdb_electric_motor_measured_speed)
    &&  (   \old(rtdb_electric_motor_measured_speed.val_F32 > MOTOROVERSPEEDLIMIT_F32)
        ||  \old(rtdb_intermediate_shaft_speed.val_F32) * GEARRATIO_F32 > MOTOROVERSPEEDLIMIT_F32))
        ==> HighAndLowBlocked;

    ensures RQ5: 
    (   SignalNotFlawless{Old}(rtdb_intermediate_shaft_speed)
    &&  SignalFlawless{Old}(rtdb_current_gear)
    &&  \old(rtdb_current_gear.val_S08 != 0))
        ==> HighAndLowBlocked;
*/

void sgmm_10ms_single_function(void) {
    // Evaluate the conditions for each requirement to block the valves.
    tB blockValves_R1 = !(FLAWLESS_B(rtdb_low_magnetic_value_measurement.ss_U08) && 
                          FLAWLESS_B(rtdb_high_magnetic_value_measurement.ss_U08));

    tB blockValves_R2 = !(FLAWLESS_B(rtdb_current_gear.ss_U08) || 
                          FLAWLESS_B(rtdb_intermediate_shaft_speed.ss_U08));

    tB blockValves_R3 = !FLAWLESS_B(rtdb_electric_motor_measured_speed.ss_U08);

    tB allFlawless = FLAWLESS_B(rtdb_low_magnetic_value_measurement.ss_U08) &&
                     FLAWLESS_B(rtdb_high_magnetic_value_measurement.ss_U08) &&
                     FLAWLESS_B(rtdb_intermediate_shaft_speed.ss_U08) &&
                     FLAWLESS_B(rtdb_electric_motor_measured_speed.ss_U08);

    tB blockValves_R4 = allFlawless && 
                        (rtdb_electric_motor_measured_speed.val_F32 > MOTOROVERSPEEDLIMIT_F32 ||
                         rtdb_intermediate_shaft_speed.val_F32 * GEARRATIO_F32 > MOTOROVERSPEEDLIMIT_F32);

    tB blockValves_R5 = !FLAWLESS_B(rtdb_intermediate_shaft_speed.ss_U08) &&
                        FLAWLESS_B(rtdb_current_gear.ss_U08) &&
                        rtdb_current_gear.val_S08 != 0;

    // Determine if the valves should be blocked.
    tB blockValves = blockValves_R1 || blockValves_R2 || blockValves_R3 || blockValves_R4 || blockValves_R5;

    // Set valve activation based on the block condition.
    if (blockValves) {
        rtdb_low_magnetic_value = FALSE;
        rtdb_high_magnetic_value = FALSE;
    } else {
        rtdb_low_magnetic_value = TRUE;
        rtdb_high_magnetic_value = TRUE;
    }
}
