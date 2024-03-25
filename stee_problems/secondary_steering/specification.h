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
    Evaluates whether steering should be
    handled by the secondary circuit.
 */
/*@
  requires ((model_primaryCircuitProvidingPowerSteering == 1 && sensor_state == 0 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 1 && sensor_state == 0 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 2 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 2 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 1 && veh_info.primHighVoltage != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primLowFlow == 1 && sensor_state == 1 && veh_info.primHighVoltage != 1 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primHighVoltage == 1 && sensor_state == 2 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && veh_info.primHighVoltage == 1 && sensor_state == 2 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 2 && veh_info.primLowFlow != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 2 && veh_info.primLowFlow != 1 && veh_info.wheelSpeed >= 4) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 1 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && 3 >= veh_info.wheelSpeed) || (model_primaryCircuitProvidingPowerSteering == 0 && sensor_state == 1 && veh_info.primLowFlow != 1 && veh_info.primHighVoltage != 1 && veh_info.wheelSpeed >= 4)) && veh_info.parkingBrake == state_PARKING_BRAKE_APPLIED && veh_info.primLowFlow == state_PRIMARY_CIRCUIT_LOW_FLOW && veh_info.primHighVoltage == state_PRIMARY_CIRCUIT_HIGH_VOLTAGE && veh_info.wheelSpeed == state_WHEEL_BASED_SPEED && veh_info.secondCircHandlesStee == state_SECONDARY_CIRCUIT_HANDLES_STEERING && veh_info.electricMotorAct == state_ELECTRIC_MOTOR_ACTIVATED;
  ensures ((\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 2 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 2 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 1 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 1 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 0 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \result.electricMotorAct == 1 && \old(sensor_state) == 0 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\result.secondCircHandlesStee == 1 && \old(sensor_state) == 2 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\result.secondCircHandlesStee == 1 && \old(sensor_state) == 1 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 1 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\old(sensor_state) == 2 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 2 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 1 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 1 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 1 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \old(state_PARKING_BRAKE_APPLIED) != 0 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed) || (\old(sensor_state) == 0 && model_vehicleIsMoving == 0 && model_vehicleMovingWithoutPrimaryPowerSteering == 0 && \result.secondCircHandlesStee != 1 && 1 >= \old(model_primaryCircuitProvidingPowerSteering) && \old(model_primaryCircuitProvidingPowerSteering) >= 0 && 3 >= \old(veh_info).wheelSpeed)) && \old(veh_info).primLowFlow == state_PRIMARY_CIRCUIT_LOW_FLOW && \old(veh_info).primHighVoltage == state_PRIMARY_CIRCUIT_HIGH_VOLTAGE && \old(veh_info).wheelSpeed == state_WHEEL_BASED_SPEED && \old(veh_info).secondCircHandlesStee == state_SECONDARY_CIRCUIT_HANDLES_STEERING && \old(veh_info).electricMotorAct == state_ELECTRIC_MOTOR_ACTIVATED && \old(veh_info).primLowFlow == \old(state_PRIMARY_CIRCUIT_LOW_FLOW) && \old(veh_info).primHighVoltage == \old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) && \old(veh_info).wheelSpeed == \old(state_WHEEL_BASED_SPEED) && \old(veh_info).secondCircHandlesStee == \old(state_SECONDARY_CIRCUIT_HANDLES_STEERING) && \old(veh_info).electricMotorAct == \old(state_ELECTRIC_MOTOR_ACTIVATED) && \old(model_primaryCircuitProvidingPowerSteering) == model_primaryCircuitProvidingPowerSteering && \old(state_PARKING_BRAKE_APPLIED) == state_PARKING_BRAKE_APPLIED;
*/
struct VEHICLE_INFO secondary_steering(struct VEHICLE_INFO veh_info, enum SENSOR_STATE sensor_state);