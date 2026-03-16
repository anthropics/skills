# Hardware Interface (ros2_control)

## Table of contents
1. ros2_control architecture
2. Writing a hardware interface plugin
3. Controller types and selection
4. URDF integration
5. Serial and CAN communication patterns
6. Configuration and parameter loading
7. Real hardware bring-up workflow
8. Common failures and fixes

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
  // NOTE: Jazzy changed the signature from HardwareInfo to HardwareComponentInterfaceParams
  hardware_interface::CallbackReturn on_init(
    const hardware_interface::HardwareComponentInterfaceParams & params) override
  {
    if (hardware_interface::SystemInterface::on_init(params) !=
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
  // from the <ros2_control> URDF tag. Only override on_export_*_interfaces()
  // if you need custom behavior beyond what the URDF defines.

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

## 4. URDF integration

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

## 5. Serial and CAN communication patterns

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

## 6. Configuration and parameter loading

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

## 7. Real hardware bring-up workflow

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

## 8. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Controller manager fails to load HW interface | Plugin not registered or not installed | Check `pluginlib_export_plugin_description_file`, rebuild, `source install/setup.bash` |
| `command_interface not found` | URDF joint name doesn't match controller config | Exact string match required — check for typos and namespaces |
| Controller reports "hardware not activated" | Lifecycle not transitioned | Use `ros2 control set_controller_state` or spawner |
| Jitter in control loop | `read()` or `write()` takes too long | Profile with `ros2 control list_hardware_interfaces`, offload I/O to thread |
| Robot jumps on activation | Initial command is 0.0, not current position | In `on_activate`, sync commands to state: `set_command(name, get_state(name))` (Jazzy) or `hw_commands_[i] = hw_positions_[i]` (Humble) |
| Emergency stop doesn't work | `write()` still sends last command | Check for `is_active()` in write, send zero-velocity on deactivate |
| Permission denied on serial port | User not in dialout group | `sudo usermod -aG dialout $USER`, re-login |
