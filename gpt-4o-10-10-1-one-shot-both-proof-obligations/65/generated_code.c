#define FALSE 0
#define TRUE  1

#ifndef VEH_MOVING_LIMIT
#define VEH_MOVING_LIMIT 1
#endif

enum SENSOR_STATE { WORKING = 0, NO_FLOW = 1, SHORT_CIRCUIT = 2 };
int state_WHEEL_BASED_SPEED;
int state_PARKING_BRAKE_APPLIED;
int state_PRIMARY_CIRCUIT_LOW_FLOW;
int state_PRIMARY_CIRCUIT_HIGH_VOLTAGE;
int state_SECONDARY_CIRCUIT_HANDLES_STEERING;
int state_ELECTRIC_MOTOR_ACTIVATED;

/*

Req. 1 — Primary PS unavailable on fault:
  If the primary circuit reports high voltage OR low flow, the primary circuit
  shall NOT be considered to provide power steering.

Req. 2 — Vehicle moving classification:
  If wheel-based speed is strictly greater than VEH_MOVING_LIMIT, the vehicle
  shall be classified as “moving”.

Req. 3 — Moving without primary PS:
  If the vehicle is moving and the primary circuit is NOT providing power
  steering, then the vehicle is “moving without primary PS”.

Req. 4 — Secondary circuit takeover:
  If the vehicle is moving without primary PS, the secondary circuit shall
  handle steering.

Req. 5 — Electric motor activation:
  If the secondary circuit handles steering and the parking brake is NOT
  applied, the electric motor shall be activated.
*/

/* Small predicates capturing requirement-level meaning (no ghost state) */
/*@ predicate PrimPS   (integer hv, integer lf) = !(hv == TRUE || lf == TRUE);
    predicate VehMoving(integer ws)            = ws > VEH_MOVING_LIMIT;
    predicate MovingNoPrimPS(integer ws, integer hv, integer lf) =
        VehMoving(ws) && !PrimPS(hv, lf);
*/

/*@ 
  assigns
      state_SECONDARY_CIRCUIT_HANDLES_STEERING,
      state_ELECTRIC_MOTOR_ACTIVATED;


  ensures (\old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) == TRUE ||
           \old(state_PRIMARY_CIRCUIT_LOW_FLOW)    == TRUE)
          ==> !PrimPS(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE,
                      state_PRIMARY_CIRCUIT_LOW_FLOW);

  ensures \old(state_WHEEL_BASED_SPEED) > VEH_MOVING_LIMIT
          ==> VehMoving(state_WHEEL_BASED_SPEED);

  ensures (VehMoving(state_WHEEL_BASED_SPEED) &&
           !PrimPS(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE,
                   state_PRIMARY_CIRCUIT_LOW_FLOW))
          ==> MovingNoPrimPS(state_WHEEL_BASED_SPEED,
                             state_PRIMARY_CIRCUIT_HIGH_VOLTAGE,
                             state_PRIMARY_CIRCUIT_LOW_FLOW);

  ensures MovingNoPrimPS(state_WHEEL_BASED_SPEED,
                         state_PRIMARY_CIRCUIT_HIGH_VOLTAGE,
                         state_PRIMARY_CIRCUIT_LOW_FLOW)
          ==> state_SECONDARY_CIRCUIT_HANDLES_STEERING == TRUE;

  ensures state_SECONDARY_CIRCUIT_HANDLES_STEERING == TRUE &&
          \old(state_PARKING_BRAKE_APPLIED) == FALSE
          ==> state_ELECTRIC_MOTOR_ACTIVATED == TRUE;
*/

void stee_10ms(void) {
    int primaryPSUnavailable = state_PRIMARY_CIRCUIT_HIGH_VOLTAGE == TRUE || state_PRIMARY_CIRCUIT_LOW_FLOW == TRUE;
    int vehicleMoving = state_WHEEL_BASED_SPEED > VEH_MOVING_LIMIT;
    int movingWithoutPrimaryPS = vehicleMoving && primaryPSUnavailable;

    if (movingWithoutPrimaryPS) {
        state_SECONDARY_CIRCUIT_HANDLES_STEERING = TRUE;
    }

    if (state_SECONDARY_CIRCUIT_HANDLES_STEERING == TRUE && state_PARKING_BRAKE_APPLIED == FALSE) {
        state_ELECTRIC_MOTOR_ACTIVATED = TRUE;
    }
}
