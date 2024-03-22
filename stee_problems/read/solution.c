/*
    This module controls the steering system of vehicles.

    The following is a list of requirements it should adhere to.

    Req. 1:
    If the primary circuit has no flow
    or a short circuit is detected
    then the primary circuit cannot provide power steering.

    Req. 2:
    The vehicle is considered to be moving
    if the wheel based speed signal is greater than 3 km/h.

    Req. 3:
    If the vehicle is moving
    and the primary circuit cannot provide power steering
    then the vehicle is moving without primary power steering.

    Req. 4:
    If the vehicle is moving without primary power steering
    then the secondary circuit should handle power steering.

    Req. 5:
    If the secondary circuit is providing power steering
    and the parking brake is not set
    then the electric motor must be activated.
 */

enum SIGNAL
{
    PARKING_BRAKE_APPLIED,
    PRIMARY_CIRCUIT_LOW_FLOW,
    PRIMARY_CIRCUIT_HIGH_VOLTAGE,
    WHEEL_BASED_SPEED,
    SECONDARY_CIRCUIT_HANDLES_STEERING,
    ELECTRIC_MOTOR_ACTIVATED,
    NUM_SIGNALS
};

// ghost variables representing model_variables in requirements
// note: these should all be booleans
//@ ghost int model_vehicleIsMoving;
//@ ghost int model_vehicleMovingWithoutPrimaryPowerSteering;
//@ ghost int model_primaryCircuitProvidingPowerSteering;

int state_PARKING_BRAKE_APPLIED;
int state_PRIMARY_CIRCUIT_LOW_FLOW;
int state_PRIMARY_CIRCUIT_HIGH_VOLTAGE;
int state_WHEEL_BASED_SPEED;
int state_SECONDARY_CIRCUIT_HANDLES_STEERING;
int state_ELECTRIC_MOTOR_ACTIVATED;

// int state[NUM_SIGNALS]; // Global state

/*
    Reads the specified signal from the state.
 */
/*@
  requires idx == 4 || idx == 5 || idx == 3 || idx == 0 || idx == 1 || idx == 2;
  ensures state_ELECTRIC_MOTOR_ACTIVATED == \old(state_ELECTRIC_MOTOR_ACTIVATED) && state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && state_WHEEL_BASED_SPEED == \old(state_WHEEL_BASED_SPEED) && state_PRIMARY_CIRCUIT_HIGH_VOLTAGE == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) && state_PRIMARY_CIRCUIT_LOW_FLOW == \old(state_PRIMARY_CIRCUIT_LOW_FLOW) && state_PARKING_BRAKE_APPLIED == \old(state_PARKING_BRAKE_APPLIED) && model_primaryCircuitProvidingPowerSteering == \old(model_primaryCircuitProvidingPowerSteering) && model_vehicleMovingWithoutPrimaryPowerSteering == \old(model_vehicleMovingWithoutPrimaryPowerSteering) && model_vehicleIsMoving == \old(model_vehicleIsMoving) && (\result != \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) || ((\old(idx) != 5 || \old(state_ELECTRIC_MOTOR_ACTIVATED) == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE)) && (\old(idx) != 4 || \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE)) && (\old(idx) != 3 || \old(state_WHEEL_BASED_SPEED) == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE)) && (\old(idx) != 1 || \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) == \old(state_PRIMARY_CIRCUIT_LOW_FLOW)) && (\old(idx) == 5 || \old(idx) == 4 || \old(idx) == 3 || \old(idx) == 2 || \old(idx) == 1 || \old(idx) == 0))) && (\old(idx) != 0 || \result == \old(state_PARKING_BRAKE_APPLIED)) && (\result == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) || ((\result != \old(state_WHEEL_BASED_SPEED) || ((\old(idx) != 5 || \old(state_ELECTRIC_MOTOR_ACTIVATED) == \old(state_WHEEL_BASED_SPEED)) && (\old(idx) != 4 || \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) == \old(state_WHEEL_BASED_SPEED)) && (\old(idx) != 1 || \old(state_WHEEL_BASED_SPEED) == \old(state_PRIMARY_CIRCUIT_LOW_FLOW)) && (\old(idx) == 5 || \old(idx) == 4 || \old(idx) == 3 || \old(idx) == 1 || \old(idx) == 0))) && (\result == \old(state_WHEEL_BASED_SPEED) || ((\result != \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) || ((\old(idx) != 5 || \old(state_ELECTRIC_MOTOR_ACTIVATED) == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING)) && (\old(idx) != 1 || \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) == \old(state_PRIMARY_CIRCUIT_LOW_FLOW)) && (\old(idx) == 5 || \old(idx) == 4 || \old(idx) == 1 || \old(idx) == 0))) && (\result == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) || ((\result != \old(state_PRIMARY_CIRCUIT_LOW_FLOW) || ((\old(idx) != 5 || \old(state_ELECTRIC_MOTOR_ACTIVATED) == \old(state_PRIMARY_CIRCUIT_LOW_FLOW)) && (\old(idx) == 5 || \old(idx) == 1 || \old(idx) == 0))) && (\result == \old(state_PRIMARY_CIRCUIT_LOW_FLOW) || ((\result != \old(state_ELECTRIC_MOTOR_ACTIVATED) || \old(idx) == 5 || \old(idx) == 0) && (\result == \old(state_ELECTRIC_MOTOR_ACTIVATED) || \old(idx) == 0)))))))));
*/
int read(enum SIGNAL idx)
{
    if (idx < NUM_SIGNALS)
    {
        if (idx == PARKING_BRAKE_APPLIED)
            return state_PARKING_BRAKE_APPLIED;
        if (idx == PRIMARY_CIRCUIT_LOW_FLOW)
            return state_PRIMARY_CIRCUIT_LOW_FLOW;
        if (idx == PRIMARY_CIRCUIT_HIGH_VOLTAGE)
            return state_PRIMARY_CIRCUIT_HIGH_VOLTAGE;
        if (idx == WHEEL_BASED_SPEED)
            return state_WHEEL_BASED_SPEED;
        if (idx == SECONDARY_CIRCUIT_HANDLES_STEERING)
            return state_SECONDARY_CIRCUIT_HANDLES_STEERING;
        if (idx == ELECTRIC_MOTOR_ACTIVATED)
            return state_ELECTRIC_MOTOR_ACTIVATED;
    }
}