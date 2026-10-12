# Hardware Interface (ros2_control)

## Table of contents
1. ros2_control architecture
2. Writing a hardware interface plugin
3. Controller types and selection
4. Controller chaining and cascade control
5. Hardware modularization
6. GPIO interface
7. Serial, CAN, and EtherCAT communication patterns
8. Configuration and parameter loading
9. Real hardware bring-up workflow
10. Hardware error recovery patterns
11. Common failures and fixes

---

## 1. ros2_control architecture

```
                  ┌──────────────────────┐
                  │   Controller Manager  │
                  │  (reads/writes at     │
                  │   fixed frequency)    │
                  └───────┬──────────────┘
                          │
              ┌───────────┼───────────────┐
              ▼           ▼               ▼
     ┌──────────────┐ ┌──────────┐ ┌──────────────┐
     │ Controller A  │ │ Ctrl B   │ │ Controller C  │
     │ (JointTraj)   │ │ (Diff)   │ │ (Gripper)     │
     └──────┬───────┘ └────┬─────┘ └──────┬───────┘
            │              │              │
            ▼              ▼              ▼
     ┌─────────────────────────────────────────┐
     │           Hardware Interface             │
     │  (your plugin: reads sensors,            │
     │   writes actuator commands)              │
     └─────────────────────────────────────────┘
            │              │              │
            ▼              ▼              ▼
     ┌──────────┐  ┌──────────┐  ┌──────────┐
     │  Motor 1  │  │  Motor 2  │  │  Gripper  │
     │ (serial)  │  │ (CAN)    │  │ (GPIO)    │
     └──────────┘  └──────────┘  └──────────┘
```

**Key concept:** The hardware interface is the bridge between ros2_control's
abstract command/state model and physical hardware communication. Controllers
never talk to hardware directly.

### Actuator vs. System vs. Sensor

When creating a `<ros2_control>` tag, you must specify the `type`:

| Type | Use Case | Characteristics |
|---|---|---|
| **System** | Multi-joint mechanisms (Robot arms, mobile bases) | Read/writes to multiple joints simultaneously. Best for buses (CAN/EtherCAT) where one frame contains all joint data. |
| **Actuator** | Single-joint mechanisms (Smart motors, simple grippers) | Read/writes to a single joint. The manager will span an instance per joint. Best for independent motors (e.g., individual PWM/Dir pins). |
| **Sensor** | Read-only hardware (IMUs, force-torque sensors) | Only exports StateInterfaces. Cannot accept commands. |

**When to use which?**
- Use **System** for 95% of real-world robots. Even if you have 6 independent serial motors, mapping them as a single System plugin often reduces thread contention and simplifies port management compared to 6 Actuator plugins fighting for USB access.
- Use **Actuator** only if each motor is truly independent (e.g., driven by separate GPIO pins) and you want maximum modularity.
- Use **Sensor** for dedicated measurement devices that don't belong to a specific actuator.

## 2. Writing a hardware interface plugin

### System interface (Jazzy 4.x API)

In Jazzy, Command-/StateInterfaces are **automatically created and exported** by the
framework based on the `<ros2_control>` URDF tag. You no longer need to override
`export_state_interfaces()` / `export_command_interfaces()` or manage memory manually.

The framework provides maps to access interfaces:
- `joint_state_interfaces_` / `joint_command_interfaces_` — keyed by fully qualified name
- `sensor_state_interfaces_` / `gpio_command_interfaces_` — for sensors and GPIO

```cpp
#include <hardware_interface/system_interface.hpp>
#include <hardware_interface/types/hardware_interface_type_values.hpp>
#include "rclcpp/rclcpp.hpp"

namespace my_robot_driver
{

class MyRobotHardware : public hardware_interface::SystemInterface
{
public:
  // Called once at startup — parse URDF, validate config
  hardware_interface::CallbackReturn on_init(
    const hardware_interface::HardwareInfo & info) override
  {
    if (hardware_interface::SystemInterface::on_init(info) !=
        hardware_interface::CallbackReturn::SUCCESS)
    {
      return hardware_interface::CallbackReturn::ERROR;
    }

    // Extract parameters from URDF <hardware><param>
    // info_ is still available as a member variable
    auto it_port = info_.hardware_parameters.find("serial_port");
    auto it_baud = info_.hardware_parameters.find("baud_rate");
    if (it_port == info_.hardware_parameters.end() ||
        it_baud == info_.hardware_parameters.end()) {
      RCLCPP_FATAL(get_logger(), "Missing required <param> in URDF: serial_port, baud_rate");
      return hardware_interface::CallbackReturn::ERROR;
    }
    port_ = it_port->second;
    try {
      baud_ = std::stoi(it_baud->second);
    } catch (const std::exception & e) {
      RCLCPP_FATAL(get_logger(), "Invalid baud_rate '%s': %s",
                   it_baud->second.c_str(), e.what());
      return hardware_interface::CallbackReturn::ERROR;
    }

    // Validate joint configuration from URDF
    for (const auto & joint : info_.joints) {
      if (joint.command_interfaces.size() != 1 ||
          joint.command_interfaces[0].name != hardware_interface::HW_IF_POSITION) {
        RCLCPP_FATAL(get_logger(), "Joint '%s' needs exactly 1 position command interface",
                     joint.name.c_str());
        return hardware_interface::CallbackReturn::ERROR;
      }
    }

    // No need to allocate std::vector<double> for states/commands —
    // the framework manages interface memory in Jazzy 4.x

    return hardware_interface::CallbackReturn::SUCCESS;
  }

  // NOTE: export_state_interfaces() and export_command_interfaces() are
  // NO LONGER needed in Jazzy 4.x. The framework auto-generates them
  // from the <ros2_control> URDF tag.
  //
  // To ADD custom interfaces beyond what the URDF defines (e.g., internal
  // temperature, bus voltage), override on_export_state_interfaces():
  //
  //   std::vector<hardware_interface::StateInterface::ConstSharedPtr>
  //   on_export_state_interfaces() override {
  //     auto interfaces = SystemInterface::on_export_state_interfaces();
  //     interfaces.push_back(std::make_shared<StateInterface>(
  //         info_.joints[0].name, "temperature", &temperature_value_));
  //     return interfaces;
  //   }
  //
  // The base class implementation returns the auto-generated interfaces.
  // Your override should call the base and extend, not replace.

  // Open hardware connection
  hardware_interface::CallbackReturn on_activate(
    const rclcpp_lifecycle::State &) override
  {
    serial_ = open_serial(port_, baud_);
    if (!serial_.is_open()) {
      return hardware_interface::CallbackReturn::ERROR;
    }

    // Initialize commands to current positions to prevent jumps on activation.
    // Iterate command interfaces (not state interfaces) — there may be fewer
    // command interfaces than state interfaces (e.g. position cmd vs position+velocity state).
    // The map key is the fully qualified name, e.g. "joint_1/position".
    for (const auto & [name, descr] : joint_command_interfaces_) {
      set_command(name, get_state(name));
    }

    return hardware_interface::CallbackReturn::SUCCESS;
  }

  // Close hardware connection
  hardware_interface::CallbackReturn on_deactivate(
    const rclcpp_lifecycle::State &) override
  {
    serial_.close();
    return hardware_interface::CallbackReturn::SUCCESS;
  }

  // Called at controller_manager frequency — READ from hardware
  hardware_interface::return_type read(
    const rclcpp::Time &, const rclcpp::Duration &) override
  {
    // Read encoder data from serial/CAN/EtherCAT
    auto data = read_encoders(serial_);
    if (!data.valid) {
      RCLCPP_ERROR_THROTTLE(get_logger(), *get_clock(), 1000,
                            "Failed to read encoder data");
      return hardware_interface::return_type::ERROR;
    }

    // Write values into framework-managed interfaces using set_state().
    // IMPORTANT: joint_state_interfaces_ is an unordered_map — iteration order
    // is NOT guaranteed. Always use explicit fully-qualified names to avoid
    // mixing up position/velocity data.
    for (size_t i = 0; i < info_.joints.size(); i++) {
      set_state(info_.joints[i].name + "/" + hardware_interface::HW_IF_POSITION,
                data.positions[i]);
      set_state(info_.joints[i].name + "/" + hardware_interface::HW_IF_VELOCITY,
                data.velocities[i]);
    }
    return hardware_interface::return_type::OK;
  }

  // Called at controller_manager frequency — WRITE to hardware
  hardware_interface::return_type write(
    const rclcpp::Time &, const rclcpp::Duration &) override
  {
    // Read commands from framework-managed interfaces using get_command()
    std::vector<double> commands;
    for (const auto & [name, descr] : joint_command_interfaces_) {
      commands.push_back(get_command(name));
    }
    if (!send_commands(serial_, commands)) {
      RCLCPP_ERROR_THROTTLE(get_logger(), *get_clock(), 1000,
                            "Failed to send commands to hardware");
      return hardware_interface::return_type::ERROR;
    }
    return hardware_interface::return_type::OK;
  }

private:
  std::string port_;
  int baud_;
  SerialPort serial_;
};

}  // namespace my_robot_driver

#include <pluginlib/class_list_macros.hpp>
PLUGINLIB_EXPORT_CLASS(my_robot_driver::MyRobotHardware,
                       hardware_interface::SystemInterface)
```

### Humble (2.x) compatibility

If targeting Humble, you must still manually override `export_state_interfaces()` and
`export_command_interfaces()` and manage your own `std::vector<double>` for storage:

```cpp
// Humble 2.x — manual interface export (not needed in Jazzy 4.x)
std::vector<hardware_interface::StateInterface> export_state_interfaces() override
{
  std::vector<hardware_interface::StateInterface> interfaces;
  for (size_t i = 0; i < info_.joints.size(); i++) {
    interfaces.emplace_back(
      info_.joints[i].name, hardware_interface::HW_IF_POSITION, &hw_positions_[i]);
    interfaces.emplace_back(
      info_.joints[i].name, hardware_interface::HW_IF_VELOCITY, &hw_velocities_[i]);
  }
  return interfaces;
}
// Also store: std::vector<double> hw_positions_, hw_velocities_, hw_commands_;
```

### Plugin registration (CMakeLists.txt addition)

```cmake
pluginlib_export_plugin_description_file(
  hardware_interface my_robot_hardware_plugin.xml)
```

### Plugin descriptor (my_robot_hardware_plugin.xml)

```xml
<library path="my_robot_driver">
  <class name="my_robot_driver/MyRobotHardware"
         type="my_robot_driver::MyRobotHardware"
         base_class_type="hardware_interface::SystemInterface">
    <description>Hardware interface for My Robot</description>
  </class>
</library>
```

**Hardware-layer joint limiters (2025+):** ros2_control now supports joint limits enforced directly at the hardware interface layer via `<limits>` tags in the URDF. These act as a safety net below the controller -- even if a controller sends an out-of-range command, the hardware interface clips it. Configure in URDF:
```xml
<joint name="joint_1">
  <command_interface name="position">
    <param name="min">-3.14</param>
    <param name="max">3.14</param>
  </command_interface>
  <!-- Hardware-layer limits (enforced by framework, not controller) -->
  <limit effort="100.0" velocity="2.0" lower="-3.14" upper="3.14"/>
</joint>
```

## 3. Controller types and selection

| Controller | Command interface | Use case |
|---|---|---|
| `joint_trajectory_controller` | position/velocity | Smooth multi-joint trajectories |
| `forward_command_controller` | position/velocity/effort | Direct pass-through, simple control |
| `diff_drive_controller` | velocity | Differential drive mobile base |
| `joint_state_broadcaster` | (none — reads only) | Publish joint states for TF/visualization |
| `parallel_gripper_action_controller` | position | Parallel gripper with action interface (Jazzy+; replaces deprecated `gripper_action_controller`) |
| `pid_controller` | effort | Low-level PID for torque control |
| `admittance_controller` | position | Force-compliant manipulation |

### Controller configuration (YAML)

```yaml
controller_manager:
  ros__parameters:
    update_rate: 500  # Hz — must match or exceed your control loop needs

    joint_state_broadcaster:
      type: joint_state_broadcaster/JointStateBroadcaster

    arm_controller:
      type: joint_trajectory_controller/JointTrajectoryController

arm_controller:
  ros__parameters:
    joints:
      - joint_1
      - joint_2
      - joint_3
      - joint_4
      - joint_5
      - joint_6
    command_interfaces:
      - position
    state_interfaces:
      - position
      - velocity
    state_publish_rate: 100.0
    action_monitor_rate: 20.0
    allow_partial_joints_goal: false
    constraints:
      stopped_velocity_tolerance: 0.01
      goal_time: 0.0
```

**Migration: gripper_action_controller -> parallel_gripper_action_controller (Jazzy)**

The `gripper_action_controller` is deprecated in Jazzy. Replace with `parallel_gripper_action_controller`:
- Action interface changes from `control_msgs/GripperCommand` to the same interface but with updated parameter naming
- YAML change: `type: gripper_action_controller/GripperActionController` -> `type: parallel_gripper_action_controller/GripperActionController`
- The `parallel_gripper` supports both position and effort control modes

## 4. Controller chaining and cascade control

Controller chaining (Jazzy+) allows controllers to feed their output into other controllers, enabling cascade control architectures. A `ChainableController` exports **reference interfaces** that other controllers can write to.

Example: A velocity PID controller that accepts reference commands from a joint_trajectory_controller:

```cpp
#include <controller_interface/chainable_controller_interface.hpp>

class VelocityPidController : public controller_interface::ChainableControllerInterface
{
public:
  // Reference interfaces: what upstream controllers write TO this controller
  std::vector<hardware_interface::CommandInterface> on_export_reference_interfaces() override
  {
    std::vector<hardware_interface::CommandInterface> refs;
    for (const auto & joint : joint_names_) {
      refs.emplace_back(get_node()->get_name(),
                        joint + "/velocity_reference",
                        &reference_commands_[joint]);
    }
    return refs;
  }

  // State interfaces: what this controller reads (e.g., current velocity)
  controller_interface::InterfaceConfiguration state_interface_configuration() const override
  {
    controller_interface::InterfaceConfiguration config;
    config.type = controller_interface::interface_configuration_type::INDIVIDUAL;
    for (const auto & joint : joint_names_) {
      config.names.push_back(joint + "/velocity");
    }
    return config;
  }

  // Command interfaces: what this controller writes (e.g., effort to hardware)
  controller_interface::InterfaceConfiguration command_interface_configuration() const override
  {
    controller_interface::InterfaceConfiguration config;
    config.type = controller_interface::interface_configuration_type::INDIVIDUAL;
    for (const auto & joint : joint_names_) {
      config.names.push_back(joint + "/effort");
    }
    return config;
  }

  controller_interface::return_type update_and_write_commands(
    const rclcpp::Time & time, const rclcpp::Duration & period) override
  {
    for (size_t i = 0; i < joint_names_.size(); ++i) {
      double ref = reference_commands_[joint_names_[i]];
      double vel = state_interfaces_[i].get_value();
      double effort = pid_controllers_[i].computeCommand(ref - vel, period.seconds());
      command_interfaces_[i].set_value(effort);
    }
    return controller_interface::return_type::OK;
  }

private:
  std::vector<std::string> joint_names_;
  std::unordered_map<std::string, double> reference_commands_;
  std::vector<control_toolbox::Pid> pid_controllers_;
};
```

YAML configuration for chaining:
```yaml
controller_manager:
  ros__parameters:
    update_rate: 1000

    velocity_pid:
      type: my_controllers/VelocityPidController

    trajectory_controller:
      type: joint_trajectory_controller/JointTrajectoryController

trajectory_controller:
  ros__parameters:
    joints: [joint_1, joint_2]
    command_interfaces: [velocity_pid/joint_1/velocity_reference,
                         velocity_pid/joint_2/velocity_reference]
    state_interfaces: [position, velocity]
```

Activation order matters: activate the downstream controller (velocity_pid) before the upstream (trajectory_controller).

## 5. Hardware modularization

Split a robot into multiple independent `<ros2_control>` tags when subsystems have different update rates, failure modes, or lifecycle requirements.

```xml
<!-- Separate hardware interfaces for arm and mobile base -->
<ros2_control name="ArmSystem" type="system">
  <hardware>
    <plugin>my_robot_driver/ArmHardware</plugin>
    <param name="can_interface">can0</param>
  </hardware>
  <joint name="shoulder">...</joint>
  <joint name="elbow">...</joint>
</ros2_control>

<ros2_control name="BaseSystem" type="system">
  <hardware>
    <plugin>my_robot_driver/BaseHardware</plugin>
    <param name="serial_port">/dev/ttyUSB0</param>
  </hardware>
  <joint name="left_wheel">...</joint>
  <joint name="right_wheel">...</joint>
</ros2_control>

<ros2_control name="GripperSystem" type="actuator">
  <hardware>
    <plugin>my_robot_driver/GripperHardware</plugin>
  </hardware>
  <joint name="gripper_finger">
    <command_interface name="position"/>
    <state_interface name="position"/>
  </joint>
</ros2_control>
```

Benefits: Each subsystem can be activated/deactivated independently. If the gripper loses communication, the arm and base continue operating. Controller manager calls read()/write() for each hardware interface separately.

## 6. GPIO interface

```cpp
// GPIO hardware interface for digital I/O (e-stop, LEDs, limit switches)
hardware_interface::CallbackReturn on_init(
  const hardware_interface::HardwareInfo & info) override
{
  // GPIO interfaces are defined in URDF under <gpio> tags
  for (const auto & gpio : info_.gpios) {
    RCLCPP_INFO(get_logger(), "GPIO: %s, cmd_ifs=%zu, state_ifs=%zu",
                gpio.name.c_str(),
                gpio.command_interfaces.size(),
                gpio.state_interfaces.size());
  }
  return hardware_interface::CallbackReturn::SUCCESS;
}
```

URDF GPIO definition:
```xml
<ros2_control name="GPIOSystem" type="system">
  <hardware>
    <plugin>my_robot_driver/GPIOHardware</plugin>
  </hardware>
  <gpio name="digital_io">
    <command_interface name="led_red"/>
    <command_interface name="led_green"/>
    <state_interface name="estop_active"/>
    <state_interface name="limit_switch_1"/>
  </gpio>
</ros2_control>
```

Access in read()/write():
```cpp
// In read():
set_state("digital_io/estop_active", read_gpio_pin(ESTOP_PIN) ? 1.0 : 0.0);
set_state("digital_io/limit_switch_1", read_gpio_pin(LIMIT_PIN) ? 1.0 : 0.0);

// In write():
set_gpio_pin(LED_RED_PIN, get_command("digital_io/led_red") > 0.5);
set_gpio_pin(LED_GREEN_PIN, get_command("digital_io/led_green") > 0.5);
```

Use `gpio_command_controller` (from ros2_controllers) to expose GPIO as a ROS service/topic.

### URDF integration

```xml
<robot xmlns:xacro="http://www.ros.org/wiki/xacro" name="my_robot">

  <ros2_control name="MyRobotSystem" type="system">
    <hardware>
      <plugin>my_robot_driver/MyRobotHardware</plugin>
      <param name="serial_port">/dev/ttyUSB0</param>
      <param name="baud_rate">115200</param>
    </hardware>

    <joint name="joint_1">
      <command_interface name="position">
        <param name="min">-3.14</param>
        <param name="max">3.14</param>
      </command_interface>
      <state_interface name="position"/>
      <state_interface name="velocity"/>
    </joint>

    <joint name="joint_2">
      <command_interface name="position">
        <param name="min">-1.57</param>
        <param name="max">1.57</param>
      </command_interface>
      <state_interface name="position"/>
      <state_interface name="velocity"/>
    </joint>
  </ros2_control>

</robot>
```

## 7. Serial, CAN, and EtherCAT communication patterns

### Serial protocol best practices

```cpp
class SerialTransport
{
public:
  // Non-blocking read with timeout
  std::optional<Frame> read_frame(std::chrono::milliseconds timeout)
  {
    auto start = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - start < timeout) {
      if (auto byte = serial_.read_byte()) {
        parser_.feed(*byte);
        if (parser_.has_frame()) {
          return parser_.extract_frame();
        }
      } else {
        std::this_thread::sleep_for(std::chrono::microseconds(100));  // Avoid busy-wait
      }
    }
    return std::nullopt;  // Timeout — caller decides how to handle
  }

  // Batched write — send all joint commands in one frame
  bool write_commands(const std::vector<double> & commands)
  {
    auto frame = protocol_.encode_position_commands(commands);
    return serial_.write(frame.data(), frame.size()) == frame.size();
  }

private:
  Serial serial_;
  FrameParser parser_;
  Protocol protocol_;
};
```

**Timing discipline:**
- The ros2_control `read()` and `write()` are called by the controller manager
  at a fixed rate. Your serial communication must complete within one cycle.
- If serial read takes longer than the cycle period, you get jitter. Solutions:
  - Use a separate thread for serial I/O with a shared buffer
  - Increase baud rate
  - Reduce message size
  - Lower the controller manager update rate

### CAN bus pattern (SocketCAN)

```cpp
#include <linux/can.h>
#include <linux/can/raw.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <fcntl.h>
#include <unistd.h>
#include <cstring>

class CanBus
{
public:
  ~CanBus() { if (sock_ >= 0) { close(sock_); sock_ = -1; } }

  bool init(const std::string & interface)
  {
    sock_ = socket(PF_CAN, SOCK_RAW, CAN_RAW);
    if (sock_ < 0) { return false; }
    // Set non-blocking
    if (fcntl(sock_, F_SETFL, O_NONBLOCK) < 0) { close(sock_); sock_ = -1; return false; }
    // Bind to interface
    struct ifreq ifr{};
    std::strncpy(ifr.ifr_name, interface.c_str(), IFNAMSIZ - 1);
    if (ioctl(sock_, SIOCGIFINDEX, &ifr) < 0) { close(sock_); sock_ = -1; return false; }
    struct sockaddr_can addr{};
    addr.can_family = AF_CAN;
    addr.can_ifindex = ifr.ifr_ifindex;
    if (bind(sock_, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
      close(sock_); sock_ = -1; return false;
    }
    return true;
  }

  bool send(uint32_t id, const uint8_t * data, uint8_t len)
  {
    if (len > CAN_MAX_DLEN) { return false; }  // Prevent buffer overflow
    struct can_frame frame{};
    frame.can_id = id;
    frame.can_dlc = len;
    std::memcpy(frame.data, data, len);
    return ::write(sock_, &frame, sizeof(frame)) == sizeof(frame);
  }

  std::optional<can_frame> receive()
  {
    struct can_frame frame{};
    auto n = ::read(sock_, &frame, sizeof(frame));
    if (n < 0) { return std::nullopt; }         // Error (EAGAIN for non-blocking = no data)
    if (n != sizeof(frame)) { return std::nullopt; }  // Partial read
    return frame;
  }
};
```

### EtherCAT pattern (SOEM)

```cpp
#include <soem/ethercat.h>

class EtherCATBus
{
public:
  bool init(const std::string & ifname, int expected_slaves)
  {
    if (ec_init(ifname.c_str()) <= 0) { return false; }
    if (ec_config_init(FALSE) < expected_slaves) {
      ec_close();
      return false;
    }
    // Map PDO (Process Data Objects)
    ec_config_map(&io_map_);
    // Set all slaves to SAFE_OP, then OP
    ec_statecheck(0, EC_STATE_SAFE_OP, EC_TIMEOUTSTATE);
    ec_slave[0].state = EC_STATE_OPERATIONAL;
    ec_writestate(0);
    ec_statecheck(0, EC_STATE_OPERATIONAL, EC_TIMEOUTSTATE);
    return ec_slave[0].state == EC_STATE_OPERATIONAL;
  }

  void process_cycle()
  {
    ec_send_processdata();
    ec_receive_processdata(EC_TIMEOUTRET);  // Deterministic timing critical
  }

  // Access PDO data via mapped memory (io_map_)
  template<typename T>
  T read_input(int slave, int offset) {
    return *reinterpret_cast<T*>(ec_slave[slave].inputs + offset);
  }

  template<typename T>
  void write_output(int slave, int offset, T value) {
    *reinterpret_cast<T*>(ec_slave[slave].outputs + offset) = value;
  }

  void close() { ec_close(); }

private:
  char io_map_[4096];
};
```

Integration with ros2_control: call `process_cycle()` in `read()`, then extract encoder values from PDO inputs. In `write()`, write command values to PDO outputs, then `process_cycle()` sends them. EtherCAT requires deterministic timing -- pair with PREEMPT_RT and CPU isolation (see `references/realtime.md`).

## 8. Configuration and parameter loading

### Launch file for ros2_control

```python
from launch import LaunchDescription
from launch_ros.actions import Node
from launch.substitutions import Command, PathJoinSubstitution
from launch_ros.substitutions import FindPackageShare

def generate_launch_description():
    robot_description = Command([
        'xacro ',
        PathJoinSubstitution([
            FindPackageShare('my_robot_description'),
            'urdf', 'robot.urdf.xacro'
        ])
    ])

    controller_params = PathJoinSubstitution([
        FindPackageShare('my_robot_control'),
        'config', 'controllers.yaml'
    ])

    return LaunchDescription([
        Node(
            package='controller_manager',
            executable='ros2_control_node',
            parameters=[
                {'robot_description': robot_description},
                controller_params,
            ],
            output='screen',
        ),
        Node(
            package='controller_manager',
            executable='spawner',
            arguments=['joint_state_broadcaster',
                       '--controller-manager', '/controller_manager'],
        ),
        Node(
            package='controller_manager',
            executable='spawner',
            arguments=['arm_controller',
                       '--controller-manager', '/controller_manager',
                       '--param-file', controller_params],
        ),
    ])
```

## 9. Real hardware bring-up workflow

1. **Start with mock hardware** — ros2_control has a built-in mock system:
   ```xml
   <plugin>mock_components/GenericSystem</plugin>
   <param name="mock_sensor_commands">true</param>
   ```
   Verify controllers and TF work before touching real hardware.

2. **Implement `on_init`** — validate URDF parsing and joint configuration.
   In Jazzy 4.x, interface export is automatic; in Humble, also implement
   `export_*_interfaces`.

3. **Implement `on_activate`** — open the hardware connection. Test that
   the connection succeeds and fails gracefully.

4. **Implement `read()`** — start reading real sensor data. Verify values
   in RViz with `joint_state_broadcaster`.

5. **Implement `write()`** — send commands. Start with very slow, small
   movements. Have an emergency stop within reach.

6. **Tune update rate** — start low (100 Hz), increase until you hit
   serial/CAN bandwidth limits or jitter thresholds.

## 10. Hardware error recovery patterns

### Transient vs fatal errors

Not all hardware errors are equal. Distinguish between transient (retry-safe) and
fatal (requires operator intervention) errors in `read()` and `write()`:

```cpp
hardware_interface::return_type MyHardware::read(
  const rclcpp::Time &, const rclcpp::Duration &)
{
  auto data = read_encoders(serial_);
  if (!data.valid) {
    consecutive_read_failures_++;

    if (consecutive_read_failures_ <= MAX_TRANSIENT_FAILURES) {
      // Transient: use last known values (stale data is safer than no data)
      RCLCPP_WARN_THROTTLE(get_logger(), *get_clock(), 1000,
        "Read failed (%d/%d) — using last known values",
        consecutive_read_failures_, MAX_TRANSIENT_FAILURES);
      return hardware_interface::return_type::OK;  // Don't crash the loop
    }

    // Fatal: too many consecutive failures — hardware is unreachable
    RCLCPP_ERROR(get_logger(),
      "Hardware unreachable after %d consecutive failures — requesting error transition",
      consecutive_read_failures_);
    return hardware_interface::return_type::ERROR;  // Triggers on_error()
  }

  consecutive_read_failures_ = 0;  // Reset on success
  // ... update state interfaces ...
  return hardware_interface::return_type::OK;
}
```

### on_error() recovery strategy

```cpp
hardware_interface::CallbackReturn on_error(
  const rclcpp_lifecycle::State & previous_state) override
{
  RCLCPP_ERROR(get_logger(), "Hardware error from state: %s", previous_state.label().c_str());

  // 1. Safe the hardware — send zero velocity / disable torque
  send_safe_command(serial_);

  // 2. Close and reopen the connection
  serial_.close();
  std::this_thread::sleep_for(std::chrono::milliseconds(500));

  if (serial_.reopen(port_, baud_)) {
    RCLCPP_INFO(get_logger(), "Hardware reconnected — transitioning to Unconfigured");
    consecutive_read_failures_ = 0;
    return hardware_interface::CallbackReturn::SUCCESS;  // → Unconfigured (can reconfigure)
  }

  RCLCPP_FATAL(get_logger(), "Hardware reconnection failed — manual intervention required");
  return hardware_interface::CallbackReturn::ERROR;  // → Finalized (dead)
}
```

### Resource leak prevention

Hardware interfaces must cleanly release resources even on abnormal shutdown:

```cpp
hardware_interface::CallbackReturn on_deactivate(
  const rclcpp_lifecycle::State &) override
{
  // ALWAYS send safe commands before closing — prevents motors
  // from holding last command when the controller stops.
  send_zero_velocity(serial_);
  serial_.close();
  return hardware_interface::CallbackReturn::SUCCESS;
}

// Destructor as safety net — on_deactivate may not be called on crash
~MyRobotHardware() override
{
  if (serial_.is_open()) {
    try { send_zero_velocity(serial_); } catch (...) {}
    serial_.close();
  }
}
```

**Anti-pattern:** Relying solely on `on_deactivate` for cleanup. If the controller
manager crashes or `SIGKILL` is sent, `on_deactivate` is never called. The destructor
should be a safety net that also attempts to safe the hardware.

## 11. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Controller manager fails to load HW interface | Plugin not registered or not installed | Check `pluginlib_export_plugin_description_file`, rebuild, `source install/setup.bash` |
| `command_interface not found` | URDF joint name doesn't match controller config | Exact string match required — check for typos and namespaces |
| Controller reports "hardware not activated" | Lifecycle not transitioned | Use `ros2 control set_controller_state` or spawner |
| Jitter in control loop | `read()` or `write()` takes too long | Profile with `ros2 control list_hardware_interfaces`, offload I/O to thread |
| Robot jumps on activation | Initial command is 0.0, not current position | In `on_activate`, sync commands to state: `set_command(name, get_state(name))` (Jazzy) or `hw_commands_[i] = hw_positions_[i]` (Humble) |
| Emergency stop doesn't work | `write()` still sends last command | Check for `is_active()` in write, send zero-velocity on deactivate |
| Permission denied on serial port | User not in dialout group | `sudo usermod -aG dialout $USER`, re-login |
| Controller chain activation fails | Downstream controller not activated before upstream | Activate in dependency order: hardware -> downstream controller -> upstream controller |
| EtherCAT slave not reaching OP state | Incorrect PDO mapping or timing violation | Check ESI file, verify PDO sizes match slave documentation, ensure RT kernel |
| GPIO values not updating | Using wrong fully-qualified name for set_state/get_command | Use exact name from URDF: "gpio_name/interface_name" (e.g., "digital_io/estop_active") |
