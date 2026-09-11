# Package Scaffolding

## Scenario

Create a ROS 2 Jazzy C++ package for a motor controller node called `arm_controller`.

## Requirements

- The node must be a lifecycle node (managed node)
- It should support composition (component loading)
- It must declare parameters for PID gains: `controller.kp`, `controller.ki`, `controller.kd`
- It should include a launch file with lifecycle state management
- It should include unit tests using gtest
- Target distribution: Jazzy

## Question

Generate the complete package structure with all necessary files.
Show the file tree and key file contents.
