# Lifecycle Node Design

## Scenario

You are building a ROS 2 Jazzy driver for a robotic arm that communicates
over serial (USB-to-UART). The driver must:

- Open the serial port during configuration
- Start a 100 Hz control loop during activation
- Send zero-velocity commands on deactivation (safety requirement)
- Close the serial port cleanly on shutdown
- Handle transient serial errors with retry logic
- Handle fatal errors by transitioning to error state

## Question

Design this node as a lifecycle (managed) node. Show the state transition
diagram, the class definition with all lifecycle callbacks, and explain
how the system manager (launch file) should orchestrate the transitions.
