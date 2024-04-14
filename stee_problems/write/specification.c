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
    Writes the specified signal to the state.
 */
/*@
  requires (model_vehicleIsMoving == 0 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 5 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0) || (model_vehicleIsMoving == 0 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 4 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0) || (model_vehicleMovingWithoutPrimaryPowerSteering == 1 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 5 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0) || (model_vehicleMovingWithoutPrimaryPowerSteering == 1 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 4 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0) || (model_primaryCircuitProvidingPowerSteering == 1 && idx == 5 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0) || (model_primaryCircuitProvidingPowerSteering == 1 && idx == 4 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0);
  ensures model_primaryCircuitProvidingPowerSteering == \old(model_primaryCircuitProvidingPowerSteering) && model_vehicleMovingWithoutPrimaryPowerSteering == \old(model_vehicleMovingWithoutPrimaryPowerSteering) && model_vehicleIsMoving == \old(model_vehicleIsMoving) && (\old(idx) != 5 || ((state_SECONDARY_CIRCUIT_HANDLES_STEERING != \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) || ((state_ELECTRIC_MOTOR_ACTIVATED != \old(val) || ((\old(model_primaryCircuitProvidingPowerSteering) != 1 || (1 >= \old(model_vehicleMovingWithoutPrimaryPowerSteering) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) >= 0 && 1 >= \old(model_vehicleIsMoving) && \old(model_vehicleIsMoving) >= 0)) && (\old(model_primaryCircuitProvidingPowerSteering) == 1 || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (state_ELECTRIC_MOTOR_ACTIVATED == \old(val) || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (\old(idx) != 4 || ((state_SECONDARY_CIRCUIT_HANDLES_STEERING != \old(val) || ((\old(model_primaryCircuitProvidingPowerSteering) != 1 || (1 >= \old(model_vehicleMovingWithoutPrimaryPowerSteering) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) >= 0 && 1 >= \old(model_vehicleIsMoving) && \old(model_vehicleIsMoving) >= 0)) && (\old(model_primaryCircuitProvidingPowerSteering) == 1 || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(val) || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (\old(model_primaryCircuitProvidingPowerSteering) != 0 || ((\old(model_vehicleIsMoving) != 0 || ((\old(idx) != 5 || (state_ELECTRIC_MOTOR_ACTIVATED == \old(val) && state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && (\old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 || \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 0))) && (\old(idx) != 4 || (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(val) && (\old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 || \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 0))) && (\old(idx) == 5 || \old(idx) == 4))) && (\old(idx) == 5 || \old(idx) == 4 || \old(model_vehicleIsMoving) == 0) && (\old(model_vehicleIsMoving) == 0 || ((\old(idx) != 5 || (state_ELECTRIC_MOTOR_ACTIVATED == \old(val) && state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 && \old(model_vehicleIsMoving) == 1)) && (\old(idx) != 4 || (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(val) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 && \old(model_vehicleIsMoving) == 1)))))) && (\old(idx) == 5 || \old(idx) == 4 || \old(model_primaryCircuitProvidingPowerSteering) == 0);
*/
void write(enum SIGNAL idx, int val)
{
    switch (idx)
    {
    case SECONDARY_CIRCUIT_HANDLES_STEERING:
        state_SECONDARY_CIRCUIT_HANDLES_STEERING = val;
        if (val && !state_PARKING_BRAKE_APPLIED)
        {
            state_ELECTRIC_MOTOR_ACTIVATED = 1;
        }
        break;
    case ELECTRIC_MOTOR_ACTIVATED:
        state_ELECTRIC_MOTOR_ACTIVATED = val;
        break;
    default:
        break;
    }
}
