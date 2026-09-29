# ROS 1 → ROS 2 Migration

## Table of contents
1. Migration strategy
2. ros1_bridge setup and configuration
3. Message type mapping
4. Launch file conversion
5. API mapping (rospy → rclpy, roscpp → rclcpp)
6. tf → tf2 migration
7. Parameter server changes
8. Build system migration (catkin → ament)
9. Rosbag format migration
10. dynamic_reconfigure migration
11. Common failures and fixes

---

## 1. Migration strategy

### Incremental migration (recommended)

Migrate one package at a time while keeping the rest on ROS 1 via `ros1_bridge`.

```
Phase 1: Bridge setup
  ROS 1 nodes ←── ros1_bridge ──► ROS 2 nodes (new)

Phase 2: Package-by-package migration
  ROS 1 (shrinking) ←── ros1_bridge ──► ROS 2 (growing)

Phase 3: Bridge removal
  All ROS 2 (bridge no longer needed)
```

**Migration order (recommended):**
1. Interface packages (messages, services, actions) — create ROS 2 `*_interfaces` packages
2. Utility / library packages (no ROS dependencies) — often just CMake changes
3. Leaf nodes (subscribers, simple publishers) — least dependencies
4. Driver nodes — require hardware access testing
5. Launch files — convert last, after all nodes are migrated
6. Core nodes (planners, controllers) — most complex, migrate last

### Big-bang migration (small projects only)

Convert everything at once. Only viable for small projects (<10 packages)
with good test coverage. High risk, not recommended for production systems.

### Decision criteria

| Factor | Incremental | Big-bang |
|---|---|---|
| Project size | >10 packages | <10 packages |
| Team size | Multiple developers | Single developer |
| Downtime tolerance | Low (production) | High (research) |
| Test coverage | Any | Must be comprehensive |
| Custom messages | Many | Few |
| Timeline | Weeks/months | Days |

## 2. ros1_bridge setup and configuration

**Important:** `ros1_bridge` is available only for Humble. It was NOT ported to Jazzy or later. If migrating to Jazzy, use Humble as an intermediate step or build the bridge from source.

### Installation

```bash
# ros1_bridge requires BOTH ROS 1 and ROS 2 sourced
# Use a dedicated machine or Docker container

# Source ROS 1 first
source /opt/ros/noetic/setup.bash

# Source ROS 2 overlay
source /opt/ros/humble/setup.bash

# Install bridge
sudo apt install ros-humble-ros1-bridge
```

### Running the bridge

```bash
# Dynamic bridge — bridges all matching topics automatically
ros2 run ros1_bridge dynamic_bridge

# Static bridge — bridges only specified topics (lower overhead)
ros2 run ros1_bridge parameter_bridge

# With specific topic mappings
ros2 run ros1_bridge parameter_bridge --ros-args \
  -p topics:="[{topic: '/scan', type: 'sensor_msgs/msg/LaserScan', queue_size: 10}]"
```

### Bridge configuration (YAML)

```yaml
# bridge_config.yaml
topics:
  -
    topic: /scan
    type: sensor_msgs/msg/LaserScan
    queue_size: 10
  -
    topic: /cmd_vel
    type: geometry_msgs/msg/Twist
    queue_size: 1
  -
    topic: /odom
    type: nav_msgs/msg/Odometry
    queue_size: 10

services:
  -
    service: /set_mode
    type: std_srvs/srv/SetBool
```

### Docker-based bridge setup

```dockerfile
# Dockerfile.bridge — multi-stage: build bridge in Focal (Noetic+Humble coexist)
# NOTE: Noetic packages only exist for Ubuntu 20.04 (Focal), NOT 22.04 (Jammy).
# The recommended approach is to build ros1_bridge from source in a Focal container
# that has both Noetic and Humble installed from source or mixed repos.
FROM ros:noetic AS ros1_stage

# Use Focal-based image where both Noetic (binary) and Humble (source) coexist
FROM ubuntu:20.04 AS bridge
RUN apt-get update && apt-get install -y \
    ros-noetic-ros-base && \
    rm -rf /var/lib/apt/lists/*
# Build Humble and ros1_bridge from source in this container
# See: https://github.com/ros2/ros1_bridge for detailed build instructions

COPY bridge_entrypoint.sh /entrypoint.sh
ENTRYPOINT ["/entrypoint.sh"]
```

```bash
# bridge_entrypoint.sh
#!/bin/bash
source /opt/ros/noetic/setup.bash
source /opt/ros/humble/setup.bash
ros2 run ros1_bridge dynamic_bridge --bridge-all-topics
```

## 3. Message type mapping

### Standard message mappings (automatic)

| ROS 1 | ROS 2 | Notes |
|---|---|---|
| `std_msgs/String` | `std_msgs/msg/String` | Direct mapping |
| `sensor_msgs/LaserScan` | `sensor_msgs/msg/LaserScan` | Direct mapping |
| `geometry_msgs/Twist` | `geometry_msgs/msg/Twist` | Direct mapping |
| `nav_msgs/Odometry` | `nav_msgs/msg/Odometry` | Direct mapping |
| `tf2_msgs/TFMessage` | `tf2_msgs/msg/TFMessage` | Direct mapping |

### Custom message migration

**ROS 1:**
```
# my_robot_msgs/msg/RobotStatus.msg
Header header
uint8 mode
string description
float64 battery_voltage
```

**ROS 2:**
```
# my_robot_interfaces/msg/RobotStatus.msg
std_msgs/Header header
uint8 mode
string description
float64 battery_voltage
```

Key differences:
- `Header` → `std_msgs/Header` (must be fully qualified in ROS 2)
- Package naming: `*_msgs` → `*_interfaces` (convention, not required)
- Place in dedicated `*_interfaces` package with `rosidl_generate_interfaces`

### Custom bridge mapping for mismatched types

```yaml
# mapping_rules.yaml — for types with different names/structures
-
  ros1_package_name: 'my_robot_msgs'
  ros1_message_name: 'RobotStatus'
  ros2_package_name: 'my_robot_interfaces'
  ros2_message_name: 'RobotStatus'
  fields_1_to_2:
    header: 'header'
    mode: 'mode'
    description: 'description'
    battery_voltage: 'battery_voltage'
```

## 4. Launch file conversion

### ROS 1 XML → ROS 2 Python

**ROS 1 (XML):**
```xml
<launch>
  <arg name="robot_name" default="my_robot"/>
  <arg name="use_sim" default="false"/>

  <param name="robot_description"
         command="$(find xacro)/xacro $(find my_robot_description)/urdf/robot.urdf.xacro"/>

  <node pkg="robot_state_publisher" type="robot_state_publisher"
        name="robot_state_publisher" output="screen"/>

  <node pkg="my_robot_driver" type="driver_node" name="driver"
        ns="$(arg robot_name)" output="screen">
    <param name="serial_port" value="/dev/ttyUSB0"/>
    <param name="baud_rate" value="115200"/>
    <remap from="joint_states" to="/$(arg robot_name)/joint_states"/>
  </node>

  <group if="$(arg use_sim)">
    <include file="$(find gazebo_ros)/launch/gazebo.launch"/>
  </group>
</launch>
```

**ROS 2 (Python):**
```python
from launch import LaunchDescription
from launch.actions import DeclareLaunchArgument, GroupAction
from launch.conditions import IfCondition
from launch.substitutions import (
    LaunchConfiguration, Command, PathJoinSubstitution
)
from launch_ros.actions import Node
from launch_ros.substitutions import FindPackageShare

def generate_launch_description():
    robot_name_arg = DeclareLaunchArgument(
        'robot_name', default_value='my_robot')
    use_sim_arg = DeclareLaunchArgument(
        'use_sim', default_value='false')

    robot_description = Command([
        'xacro ',
        PathJoinSubstitution([
            FindPackageShare('my_robot_description'),
            'urdf', 'robot.urdf.xacro',
        ]),
    ])

    robot_state_publisher = Node(
        package='robot_state_publisher',
        executable='robot_state_publisher',
        parameters=[{'robot_description': robot_description}],
        output='screen',
    )

    driver = Node(
        package='my_robot_driver',
        executable='driver_node',
        name='driver',
        namespace=LaunchConfiguration('robot_name'),
        parameters=[{
            'serial_port': '/dev/ttyUSB0',
            'baud_rate': 115200,
        }],
        remappings=[
            # Note: namespace already prefixes topics, so typically just remap the base name
            ('joint_states', 'joint_states'),  # or use absolute: /my_robot/joint_states
        ],
        output='screen',
    )

    simulation = GroupAction(
        condition=IfCondition(LaunchConfiguration('use_sim')),
        actions=[
            # Include Gazebo launch
        ],
    )

    return LaunchDescription([
        robot_name_arg,
        use_sim_arg,
        robot_state_publisher,
        driver,
        simulation,
    ])
```

### Key conversion patterns

| ROS 1 | ROS 2 |
|---|---|
| `<arg name="x" default="y"/>` | `DeclareLaunchArgument('x', default_value='y')` |
| `$(arg x)` | `LaunchConfiguration('x')` |
| `$(find pkg)` | `FindPackageShare('pkg')` |
| `<param name="..." value="..."/>` | `parameters=[{'name': value}]` |
| `<remap from="a" to="b"/>` | `remappings=[('a', 'b')]` |
| `<group if="...">` | `GroupAction(condition=IfCondition(...))` |
| `<include file="..."/>` | `IncludeLaunchDescription(...)` |
| `<node ... type="...">` | `Node(... executable='...')` |
| `$(arg x)/sub` | `[LaunchConfiguration('x'), '/sub']` |

## 5. API mapping (rospy → rclpy, roscpp → rclcpp)

### Python API mapping

| rospy (ROS 1) | rclpy (ROS 2) |
|---|---|
| `rospy.init_node('name')` | `rclpy.init(); Node('name')` |
| `rospy.Publisher('topic', Msg, queue_size=10)` | `node.create_publisher(Msg, 'topic', 10)` |
| `rospy.Subscriber('topic', Msg, cb)` | `node.create_subscription(Msg, 'topic', cb, 10)` |
| `rospy.Service('srv', Type, cb)` | `node.create_service(Type, 'srv', cb)` |
| `rospy.ServiceProxy('srv', Type)` | `node.create_client(Type, 'srv')` |
| `rospy.Timer(Duration(0.1), cb)` | `node.create_timer(0.1, cb)` |
| `rospy.Rate(10); rate.sleep()` | `node.create_timer(0.1, cb)` (no rate.sleep pattern) |
| `rospy.get_param('~param', default)` | `node.declare_parameter('param', default)` |
| `rospy.loginfo('msg')` | `node.get_logger().info('msg')` |
| `rospy.spin()` | `rclpy.spin(node)` |
| `rospy.is_shutdown()` | `rclpy.ok()` |
| `rospy.Time.now()` | `node.get_clock().now()` |

### C++ API mapping

| roscpp (ROS 1) | rclcpp (ROS 2) |
|---|---|
| `ros::init(argc, argv, "name")` | `rclcpp::init(argc, argv)` |
| `ros::NodeHandle nh` | `auto node = std::make_shared<rclcpp::Node>("name")` |
| `nh.advertise<Msg>("topic", 10)` | `node->create_publisher<Msg>("topic", 10)` |
| `nh.subscribe("topic", 10, cb)` | `node->create_subscription<Msg>("topic", 10, cb)` |
| `nh.advertiseService("srv", cb)` | `node->create_service<Type>("srv", cb)` |
| `nh.serviceClient<Type>("srv")` | `node->create_client<Type>("srv")` |
| `nh.createTimer(Duration(0.1), cb)` | `node->create_wall_timer(100ms, cb)` |
| `nh.getParam("param", var)` | `node->declare_parameter("param", default)` |
| `ROS_INFO("msg")` | `RCLCPP_INFO(node->get_logger(), "msg")` |
| `ros::spin()` | `rclcpp::spin(node)` |
| `ros::ok()` | `rclcpp::ok()` |
| `ros::Time::now()` | `node->get_clock()->now()` |
| `ros::Duration(1.0)` | `rclcpp::Duration::from_seconds(1.0)` |

### Key behavioral differences

- **No global state:** ROS 2 nodes are objects, not global singletons
- **No `rospy.Rate().sleep()`:** Use timers instead (executor-friendly)
- **Parameters must be declared:** No undeclared parameter access
- **QoS is explicit:** Must choose QoS for every publisher/subscriber
- **Services are async:** Never call services synchronously in callbacks
- **No global `/rosout`:** Each node has its own logger

## 6. tf → tf2 migration

| ROS 1 (tf) | ROS 2 (tf2) |
|---|---|
| `tf::TransformListener` | `tf2_ros::TransformListener` + `tf2_ros::Buffer` |
| `tf::TransformBroadcaster` | `tf2_ros::TransformBroadcaster` |
| `tf::StampedTransform` | `geometry_msgs::msg::TransformStamped` |
| `listener.lookupTransform(target, source, time)` | `buffer.lookupTransform(target, source, time)` |
| `listener.waitForTransform(...)` | `buffer.canTransform(...)` with timeout |

```cpp
// ROS 1
tf::TransformListener listener;
tf::StampedTransform transform;
listener.waitForTransform("base_link", "laser", ros::Time(0), ros::Duration(1.0));
listener.lookupTransform("base_link", "laser", ros::Time(0), transform);

// ROS 2
auto buffer = std::make_unique<tf2_ros::Buffer>(get_clock());
auto listener = std::make_shared<tf2_ros::TransformListener>(*buffer);
auto transform = buffer->lookupTransform(
  "base_link", "laser", tf2::TimePointZero);
```

## 7. Parameter server changes

### ROS 1: Global parameter server

```python
# ROS 1 — global parameter server, any node can read/write
rospy.set_param('/robot/max_speed', 1.0)
speed = rospy.get_param('/robot/max_speed', 0.5)
```

### ROS 2: Node-local parameters

```python
# ROS 2 — parameters are node-local, must be declared
self.declare_parameter('max_speed', 0.5)
speed = self.get_parameter('max_speed').value

# To read another node's parameter:
client = self.create_client(GetParameters, '/other_node/get_parameters')
```

### Migration pattern for shared parameters

```yaml
# In ROS 1: global params loaded to parameter server
# In ROS 2: load shared params from YAML to each node that needs them
# config/shared_params.yaml
/**:
  ros__parameters:
    use_sim_time: false
    robot_type: "diff_drive"

my_node:
  ros__parameters:
    max_speed: 1.0
```

## 8. Build system migration (catkin → ament)

### CMakeLists.txt migration

**catkin (ROS 1):**
```cmake
cmake_minimum_required(VERSION 3.0)
project(my_package)
find_package(catkin REQUIRED COMPONENTS roscpp sensor_msgs)
catkin_package(INCLUDE_DIRS include LIBRARIES ${PROJECT_NAME})
include_directories(${catkin_INCLUDE_DIRS})
add_library(${PROJECT_NAME} src/my_lib.cpp)
target_link_libraries(${PROJECT_NAME} ${catkin_LIBRARIES})
add_executable(my_node src/main.cpp)
target_link_libraries(my_node ${PROJECT_NAME})
```

**ament (ROS 2):**
```cmake
cmake_minimum_required(VERSION 3.8)
project(my_package)

find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(sensor_msgs REQUIRED)

add_library(${PROJECT_NAME} src/my_lib.cpp)
target_include_directories(${PROJECT_NAME} PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include/${PROJECT_NAME}>)
ament_target_dependencies(${PROJECT_NAME} rclcpp sensor_msgs)

add_executable(my_node src/main.cpp)
target_link_libraries(my_node ${PROJECT_NAME})

install(TARGETS ${PROJECT_NAME} EXPORT export_${PROJECT_NAME}
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(TARGETS my_node DESTINATION lib/${PROJECT_NAME})
install(DIRECTORY include/ DESTINATION include/${PROJECT_NAME})

ament_export_targets(export_${PROJECT_NAME} HAS_LIBRARY_TARGET)
ament_export_dependencies(rclcpp sensor_msgs)
ament_package()
```

### package.xml migration

**format 2 (ROS 1):**
```xml
<buildtool_depend>catkin</buildtool_depend>
<build_depend>roscpp</build_depend>
<exec_depend>roscpp</exec_depend>
```

**format 3 (ROS 2):**
```xml
<buildtool_depend>ament_cmake</buildtool_depend>
<depend>rclcpp</depend>  <!-- replaces build_depend + exec_depend -->
<export><build_type>ament_cmake</build_type></export>
```

### Build command migration

| catkin (ROS 1) | colcon (ROS 2) |
|---|---|
| `catkin_make` | `colcon build` |
| `catkin build` | `colcon build` |
| `catkin build --this` | `colcon build --packages-select my_pkg` |
| `source devel/setup.bash` | `source install/setup.bash` |
| `catkin_make run_tests` | `colcon test` |

## 9. Rosbag format migration

```bash
# Convert ROS 1 bag to ROS 2 format
# Option 1: Use rosbags (pure Python, no ROS installation needed)
pip install rosbags
rosbags-convert ros1_recording.bag --dst ros2_recording/

# Option 2: Use ros1_bridge replay (requires Humble + ROS 1 sourced)
# Play ROS 1 bag → bridge → record as ROS 2 bag
```

## 10. dynamic_reconfigure migration

ROS 1's `dynamic_reconfigure` is replaced by ROS 2's native parameter system:

```python
# ROS 1: dynamic_reconfigure callback
def reconfigure_callback(config, level):
    self.kp = config['kp']
    return config

# ROS 2: parameter callback (equivalent)
def parameter_callback(self, params):
    for param in params:
        if param.name == 'kp':
            self.kp = param.value
    return SetParametersResult(successful=True)

self.add_on_set_parameters_callback(parameter_callback)
```

## 11. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| ros1_bridge crashes on startup | ROS 1 and ROS 2 env conflict | Source ROS 1 first, then ROS 2; use dedicated Docker container |
| Custom messages not bridged | Bridge doesn't know the mapping | Build bridge from source with both message packages in workspace |
| `rospy.Rate().sleep()` equivalent | No direct equivalent in ROS 2 | Use `create_timer()` callbacks instead of sleep loops |
| Global parameters not accessible | ROS 2 has no global param server | Pass shared YAML config to all nodes that need it |
| `Header` field error in custom msg | Must be `std_msgs/Header` in ROS 2 | Fully qualify the type in .msg file |
| `catkin_make` doesn't build ROS 2 | Wrong build system | Use `colcon build` for ROS 2 packages |
| Subscriber callback signature error | ROS 2 uses ConstSharedPtr, not raw pointer | Change `const Msg::ConstPtr&` to `const Msg::ConstSharedPtr` |
| Service call blocks forever | Synchronous service call in callback | Use `async_send_request` with callback instead |
