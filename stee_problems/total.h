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

// #define _(...) /* nothing */
//
// #define VEH_MOVING_LIMIT 3
//
// #define TRUE 1
// #define FALSE 0

enum SENSOR_STATE
{
    WORKING,
    NO_FLOW,
    SHORT_CIRCUIT
};

struct VEHICLE_INFO
{
    int wheelSpeed;
    int parkingBrake;
    int primLowFlow;
    int primHighVoltage;
    int secondCircHandlesStee;
    int electricMotorAct;
};

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

/*
    Writes the specified signal to the state.
 */
/*@
  requires (model_vehicleIsMoving == 0 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 5 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0) || (model_vehicleIsMoving == 0 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 4 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0) || (model_vehicleMovingWithoutPrimaryPowerSteering == 1 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 5 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0) || (model_vehicleMovingWithoutPrimaryPowerSteering == 1 && model_primaryCircuitProvidingPowerSteering == 0 && idx == 4 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0) || (model_primaryCircuitProvidingPowerSteering == 1 && idx == 5 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0) || (model_primaryCircuitProvidingPowerSteering == 1 && idx == 4 && 1 >= model_vehicleIsMoving && model_vehicleIsMoving >= 0 && 1 >= model_vehicleMovingWithoutPrimaryPowerSteering && model_vehicleMovingWithoutPrimaryPowerSteering >= 0);
  ensures model_primaryCircuitProvidingPowerSteering == \old(model_primaryCircuitProvidingPowerSteering) && model_vehicleMovingWithoutPrimaryPowerSteering == \old(model_vehicleMovingWithoutPrimaryPowerSteering) && model_vehicleIsMoving == \old(model_vehicleIsMoving) && (\old(idx) != 5 || ((state_SECONDARY_CIRCUIT_HANDLES_STEERING != \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) || ((state_ELECTRIC_MOTOR_ACTIVATED != \old(val) || ((\old(model_primaryCircuitProvidingPowerSteering) != 1 || (1 >= \old(model_vehicleMovingWithoutPrimaryPowerSteering) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) >= 0 && 1 >= \old(model_vehicleIsMoving) && \old(model_vehicleIsMoving) >= 0)) && (\old(model_primaryCircuitProvidingPowerSteering) == 1 || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (state_ELECTRIC_MOTOR_ACTIVATED == \old(val) || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (\old(idx) != 4 || ((state_SECONDARY_CIRCUIT_HANDLES_STEERING != \old(val) || ((\old(model_primaryCircuitProvidingPowerSteering) != 1 || (1 >= \old(model_vehicleMovingWithoutPrimaryPowerSteering) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) >= 0 && 1 >= \old(model_vehicleIsMoving) && \old(model_vehicleIsMoving) >= 0)) && (\old(model_primaryCircuitProvidingPowerSteering) == 1 || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(val) || \old(model_primaryCircuitProvidingPowerSteering) == 0))) && (\old(model_primaryCircuitProvidingPowerSteering) != 0 || ((\old(model_vehicleIsMoving) != 0 || ((\old(idx) != 5 || (state_ELECTRIC_MOTOR_ACTIVATED == \old(val) && state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && (\old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 || \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 0))) && (\old(idx) != 4 || (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(val) && (\old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 || \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 0))) && (\old(idx) == 5 || \old(idx) == 4))) && (\old(idx) == 5 || \old(idx) == 4 || \old(model_vehicleIsMoving) == 0) && (\old(model_vehicleIsMoving) == 0 || ((\old(idx) != 5 || (state_ELECTRIC_MOTOR_ACTIVATED == \old(val) && state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 && \old(model_vehicleIsMoving) == 1)) && (\old(idx) != 4 || (state_SECONDARY_CIRCUIT_HANDLES_STEERING == \old(val) && \old(model_vehicleMovingWithoutPrimaryPowerSteering) == 1 && \old(model_vehicleIsMoving) == 1)))))) && (\old(idx) == 5 || \old(idx) == 4 || \old(model_primaryCircuitProvidingPowerSteering) == 0);
*/
void write(enum SIGNAL idx, int val);

/*
    Reads the current state of the system.
 */
/*@
  requires \true;
  ensures \result.parkingBrake == state_PARKING_BRAKE_APPLIED && \result.primLowFlow == state_PRIMARY_CIRCUIT_LOW_FLOW && \result.primHighVoltage == state_PRIMARY_CIRCUIT_HIGH_VOLTAGE && \result.wheelSpeed == state_WHEEL_BASED_SPEED && \result.secondCircHandlesStee == state_SECONDARY_CIRCUIT_HANDLES_STEERING && \result.electricMotorAct == state_ELECTRIC_MOTOR_ACTIVATED && \result.parkingBrake == \old(state_PARKING_BRAKE_APPLIED) && \result.primLowFlow == \old(state_PRIMARY_CIRCUIT_LOW_FLOW) && \result.primHighVoltage == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) && \result.wheelSpeed == \old(state_WHEEL_BASED_SPEED) && \result.secondCircHandlesStee == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && \result.electricMotorAct == \old(state_ELECTRIC_MOTOR_ACTIVATED) && \old(model_vehicleIsMoving) == model_vehicleIsMoving && \old(model_vehicleMovingWithoutPrimaryPowerSteering) == model_vehicleMovingWithoutPrimaryPowerSteering && \old(model_primaryCircuitProvidingPowerSteering) == model_primaryCircuitProvidingPowerSteering;
*/
struct VEHICLE_INFO get_system_state();

/*
    Evaluates the state of the primary steering circuit sensors.
 */
/*@
  requires ((veh_info.primLowFlow == 1 && 3 >= veh_info.wheelSpeed) || (veh_info.primLowFlow == 1 && veh_info.wheelSpeed >= 4) || (veh_info.primHighVoltage == 1 && 3 >= veh_info.wheelSpeed) || (veh_info.primHighVoltage == 1 && veh_info.wheelSpeed >= 4) || (veh_info.primLowFlow != 1 && 3 >= veh_info.wheelSpeed) || (veh_info.primLowFlow != 1 && veh_info.wheelSpeed >= 4)) && veh_info.parkingBrake == state_PARKING_BRAKE_APPLIED && veh_info.primLowFlow == state_PRIMARY_CIRCUIT_LOW_FLOW && veh_info.primHighVoltage == state_PRIMARY_CIRCUIT_HIGH_VOLTAGE && veh_info.wheelSpeed == state_WHEEL_BASED_SPEED && veh_info.secondCircHandlesStee == state_SECONDARY_CIRCUIT_HANDLES_STEERING && veh_info.electricMotorAct == state_ELECTRIC_MOTOR_ACTIVATED;
  ensures (\result == 2 || (\result == 1 && \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) != 1) || (\result == 0 && \old(state_PRIMARY_CIRCUIT_LOW_FLOW) != 1 && \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) != 1)) && \old(veh_info).parkingBrake == state_PARKING_BRAKE_APPLIED && \old(veh_info).wheelSpeed == state_WHEEL_BASED_SPEED && \old(veh_info).secondCircHandlesStee == state_SECONDARY_CIRCUIT_HANDLES_STEERING && \old(veh_info).electricMotorAct == state_ELECTRIC_MOTOR_ACTIVATED && \old(veh_info).parkingBrake == \old(state_PARKING_BRAKE_APPLIED) && \old(veh_info).wheelSpeed == \old(state_WHEEL_BASED_SPEED) && \old(veh_info).secondCircHandlesStee == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && \old(veh_info).electricMotorAct == \old(state_ELECTRIC_MOTOR_ACTIVATED) && \old(model_vehicleIsMoving) == model_vehicleIsMoving && \old(model_vehicleMovingWithoutPrimaryPowerSteering) == model_vehicleMovingWithoutPrimaryPowerSteering && \old(model_primaryCircuitProvidingPowerSteering) == model_primaryCircuitProvidingPowerSteering && \old(state_PRIMARY_CIRCUIT_LOW_FLOW) == state_PRIMARY_CIRCUIT_LOW_FLOW && \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) == state_PRIMARY_CIRCUIT_HIGH_VOLTAGE;
*/
enum SENSOR_STATE eval_prim_sensor_state(struct VEHICLE_INFO veh_info);

/*
    Evaluates whether steering should be
    handled by the secondary circuit.
 */
/*@
  requires ((model_primaryCircuitProvidingPowerSteering == 1 && sensor_state == 0 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 1 && sensor_state == 0 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 2 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 2 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 1 && veh_info.primHighVoltage != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 1 && veh_info.primHighVoltage != 1 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primHighVoltage == 1 && sensor_state == 2 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primHighVoltage == 1 && sensor_state == 2 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 2 && veh_info.primLowFlow != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 2 && veh_info.primLowFlow != 1 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 1 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 1 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && veh_info.wheelSpeed >= 4)) && veh_info.parkingBrake == state_PARKING_BRAKE_APPLIED && veh_info.primLowFlow == state_PRIMARY_CIRCUIT_LOW_FLOW && veh_info.primHighVoltage == state_PRIMARY_CIRCUIT_HIGH_VOLTAGE && veh_info.wheelSpeed == state_WHEEL_BASED_SPEED && veh_info.secondCircHandlesStee == state_SECONDARY_CIRCUIT_HANDLES_STEERING && veh_info.electricMotorAct == state_ELECTRIC_MOTOR_ACTIVATED;
  ensures ((\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 2 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 2 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 1 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 1 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 0 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 0 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\result.secondCircHandlesStee == 1 && \old(sensor_state) == 2 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \old(sensor_state) == 1 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\old(sensor_state) == 2 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 2 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 1 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 1 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed)) && \old(veh_info).primLowFlow == state_PRIMARY_CIRCUIT_LOW_FLOW && \old(veh_info).primHighVoltage == state_PRIMARY_CIRCUIT_HIGH_VOLTAGE && \old(veh_info).wheelSpeed == state_WHEEL_BASED_SPEED && \old(veh_info).secondCircHandlesStee == state_SECONDARY_CIRCUIT_HANDLES_STEERING && \old(veh_info).electricMotorAct == state_ELECTRIC_MOTOR_ACTIVATED && \old(veh_info).primLowFlow == \old(state_PRIMARY_CIRCUIT_LOW_FLOW) && \old(veh_info).primHighVoltage == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) && \old(veh_info).wheelSpeed == \old(state_WHEEL_BASED_SPEED) && \old(veh_info).secondCircHandlesStee == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && \old(veh_info).electricMotorAct == \old(state_ELECTRIC_MOTOR_ACTIVATED) && \old(model_primaryCircuitProvidingPowerSteering) == model_primaryCircuitProvidingPowerSteering && \old(state_PARKING_BRAKE_APPLIED) == state_PARKING_BRAKE_APPLIED;
*/
struct VEHICLE_INFO secondary_steering(struct VEHICLE_INFO veh_info, enum SENSOR_STATE sensor_state);

/*
    Module entry point function.
 */
/*@
    // requires \valid(state + (0..NUM_SIGNALS-1));
    decreases 0;
    assigns
            state_PARKING_BRAKE_APPLIED,
            state_PRIMARY_CIRCUIT_LOW_FLOW,
            state_PRIMARY_CIRCUIT_HIGH_VOLTAGE,
            state_WHEEL_BASED_SPEED,
            // the above should not really need to be here
            state_SECONDARY_CIRCUIT_HANDLES_STEERING, state_ELECTRIC_MOTOR_ACTIVATED,
            model_vehicleIsMoving, model_vehicleMovingWithoutPrimaryPowerSteering,
            model_primaryCircuitProvidingPowerSteering;

    // Req. 1-4 without intermediary variables *
    ensures (\old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) == 1
          || \old(state_PRIMARY_CIRCUIT_LOW_FLOW) == 1)
            && \old(state_WHEEL_BASED_SPEED) > 3
            ==> state_SECONDARY_CIRCUIT_HANDLES_STEERING == 1;

    // Req. 1 *
    ensures (\old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) == 1
          || \old(state_PRIMARY_CIRCUIT_LOW_FLOW) == 1)
               ==> model_primaryCircuitProvidingPowerSteering == 0;

    // Req. 2
    ensures \old(state_WHEEL_BASED_SPEED) > 3
            ==> model_vehicleIsMoving == 1;

    // Req. 3
    ensures model_vehicleIsMoving == 1
            && model_primaryCircuitProvidingPowerSteering == 0
            ==> model_vehicleMovingWithoutPrimaryPowerSteering == 1;

    // Req. 4
    ensures model_vehicleMovingWithoutPrimaryPowerSteering == 1
            ==> state_SECONDARY_CIRCUIT_HANDLES_STEERING == 1;

    // Req. 5
    ensures state_SECONDARY_CIRCUIT_HANDLES_STEERING == 1
            && \old(state_PARKING_BRAKE_APPLIED) == 0
            ==> state_ELECTRIC_MOTOR_ACTIVATED == 1;
  */
void steering();