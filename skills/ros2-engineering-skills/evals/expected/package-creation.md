# Expected: Package Scaffolding

## Required Elements

### 1. Directory Structure
Must include at minimum:
```
arm_controller/
  CMakeLists.txt
  package.xml
  include/arm_controller/arm_controller_node.hpp
  src/arm_controller_node.cpp
  src/main.cpp
  launch/bringup.launch.py
  config/params.yaml
  test/test_arm_controller.cpp
```

### 2. Naming Conventions
- Package name: `arm_controller` (snake_case)
- Class name: `ArmControllerNode` (PascalCase)
- Node name: `arm_controller` (snake_case)
- Parameter namespace: `controller.kp`, `controller.ki`, `controller.kd`

### 3. Lifecycle Node
- Class must inherit from `rclcpp_lifecycle::LifecycleNode`
- Must implement: `on_configure`, `on_activate`, `on_deactivate`, `on_cleanup`, `on_shutdown`
- Constructor must accept `const rclcpp::NodeOptions & options`

### 4. Component Support
- Must include `RCLCPP_COMPONENTS_REGISTER_NODE` macro
- CMakeLists.txt must have `rclcpp_components_register_node`

### 5. package.xml
- Format 3
- Dependencies: `rclcpp`, `rclcpp_lifecycle`, `rclcpp_components`
- License: Apache-2.0

### 6. Launch File
- Must use `LifecycleNode` action
- Must include lifecycle state transitions (configure, activate)
- Must load parameters from config/params.yaml

### 7. Parameters
- `controller.kp`, `controller.ki`, `controller.kd` with ParameterDescriptor
- Must include FloatingPointRange for bounds validation

### 8. Tests
- gtest-based test file
- CMakeLists.txt must include `ament_add_gtest`
