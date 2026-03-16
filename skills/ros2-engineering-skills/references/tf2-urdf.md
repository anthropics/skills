# TF2 and URDF/Xacro

## Table of contents
1. TF2 concepts
2. Static vs dynamic broadcasters
3. Transform listener patterns
4. URDF structure and joint types
5. Xacro macros and parameterization
6. robot_state_publisher
7. Debugging transforms
8. Multi-robot TF trees
9. Common failures and fixes

---

## 1. TF2 concepts

TF2 manages coordinate frame transforms across a ROS 2 system. Every sensor
reading, actuator command, and planning query depends on knowing how frames
relate to each other.

### Frame tree structure

```
map                          ← global fixed frame (SLAM/localization)
 └── odom                   ← odometry frame (continuous, drifts)
      └── base_link         ← robot body center
           ├── base_footprint  ← ground projection of base_link
           ├── laser_link   ← LiDAR sensor
           ├── camera_link  ← camera housing
           │    └── camera_optical_frame  ← optical axis (Z forward)
           ├── imu_link     ← IMU sensor
           └── arm_base_link ← manipulator base
                ├── link_1
                ├── link_2
                └── ...
```

**Key conventions (REP-105):**
- `map` → `odom`: published by localization (AMCL, EKF)
- `odom` → `base_link`: published by odometry (wheel encoders, visual odometry)
- `base_link` → sensors: published by `robot_state_publisher` from URDF
- Frame names use `snake_case`
- Optical frames follow the convention: X-right, Y-down, Z-forward

### Transform types

| Transform | Published by | Rate | TF2 type |
|---|---|---|---|
| map → odom | Localization node | 10–50 Hz | Dynamic |
| odom → base_link | Odometry node | 20–100 Hz | Dynamic |
| base_link → sensor_link | robot_state_publisher | Once (static) | Static |
| link_N → link_N+1 | robot_state_publisher | Joint state rate | Dynamic |

## 2. Static vs dynamic broadcasters

### Static broadcaster (C++)

Use for transforms that never change (sensor mounts, fixed links).

```cpp
#include <rclcpp/rclcpp.hpp>
#include <tf2_ros/static_transform_broadcaster.h>
#include <geometry_msgs/msg/transform_stamped.hpp>

class SensorMountBroadcaster : public rclcpp::Node
{
public:
  SensorMountBroadcaster() : Node("sensor_mount_tf")
  {
    tf_broadcaster_ = std::make_shared<tf2_ros::StaticTransformBroadcaster>(this);

    geometry_msgs::msg::TransformStamped t;
    t.header.stamp = this->get_clock()->now();
    t.header.frame_id = "base_link";
    t.child_frame_id = "laser_link";
    t.transform.translation.x = 0.15;
    t.transform.translation.y = 0.0;
    t.transform.translation.z = 0.3;
    // Quaternion for no rotation (identity)
    t.transform.rotation.w = 1.0;

    tf_broadcaster_->sendTransform(t);
  }

private:
  std::shared_ptr<tf2_ros::StaticTransformBroadcaster> tf_broadcaster_;
};
```

**Static transforms use `TRANSIENT_LOCAL` QoS** — late joiners receive the
transform immediately. They are published once and latched.

### Dynamic broadcaster (C++)

Use for transforms that change over time (odometry, joint states).

```cpp
#include <tf2_ros/transform_broadcaster.h>

class OdometryPublisher : public rclcpp::Node
{
public:
  OdometryPublisher() : Node("odometry_publisher")
  {
    tf_broadcaster_ = std::make_unique<tf2_ros::TransformBroadcaster>(this);
    timer_ = create_wall_timer(
      std::chrono::milliseconds(20),  // 50 Hz
      std::bind(&OdometryPublisher::publish_odom, this));
  }

private:
  void publish_odom()
  {
    geometry_msgs::msg::TransformStamped t;
    t.header.stamp = get_clock()->now();
    t.header.frame_id = "odom";
    t.child_frame_id = "base_link";
    t.transform.translation.x = current_x_;
    t.transform.translation.y = current_y_;
    t.transform.rotation = tf2::toMsg(
      tf2::Quaternion(tf2::Vector3(0, 0, 1), current_yaw_));
    tf_broadcaster_->sendTransform(t);
  }

  std::unique_ptr<tf2_ros::TransformBroadcaster> tf_broadcaster_;
  rclcpp::TimerBase::SharedPtr timer_;
  double current_x_ = 0.0, current_y_ = 0.0, current_yaw_ = 0.0;
};
```

### Static broadcaster via CLI (useful for testing)

```bash
# Publish a static transform
ros2 run tf2_ros static_transform_publisher \
  --x 0.15 --y 0 --z 0.3 --roll 0 --pitch 0 --yaw 0 \
  --frame-id base_link --child-frame-id laser_link
```

## 3. Transform listener patterns

### Looking up transforms (C++)

```cpp
#include <tf2_ros/buffer.h>
#include <tf2_ros/transform_listener.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.hpp>

class TargetTracker : public rclcpp::Node
{
public:
  TargetTracker() : Node("target_tracker")
  {
    tf_buffer_ = std::make_unique<tf2_ros::Buffer>(get_clock());
    tf_listener_ = std::make_shared<tf2_ros::TransformListener>(*tf_buffer_);

    timer_ = create_wall_timer(
      std::chrono::milliseconds(100),
      std::bind(&TargetTracker::track, this));
  }

private:
  void track()
  {
    try {
      // Look up the transform from base_link to target frame
      auto t = tf_buffer_->lookupTransform(
        "base_link", "target_frame",
        tf2::TimePointZero);  // Get the latest available

      RCLCPP_INFO(get_logger(), "Target at x=%.2f, y=%.2f, z=%.2f",
        t.transform.translation.x,
        t.transform.translation.y,
        t.transform.translation.z);
    } catch (const tf2::TransformException & ex) {
      RCLCPP_WARN_THROTTLE(get_logger(), *get_clock(), 2000,
        "Could not get transform: %s", ex.what());
    }
  }

  std::unique_ptr<tf2_ros::Buffer> tf_buffer_;
  std::shared_ptr<tf2_ros::TransformListener> tf_listener_;
  rclcpp::TimerBase::SharedPtr timer_;
};
```

### Transforming point/pose data

```cpp
#include <tf2_geometry_msgs/tf2_geometry_msgs.hpp>

// Transform a point from camera frame to base frame
geometry_msgs::msg::PointStamped point_in_camera;
point_in_camera.header.frame_id = "camera_optical_frame";
point_in_camera.header.stamp = get_clock()->now();
point_in_camera.point.x = 1.0;
point_in_camera.point.y = 0.5;
point_in_camera.point.z = 2.0;

try {
  auto point_in_base = tf_buffer_->transform(
    point_in_camera, "base_link",
    tf2::durationFromSec(0.1));  // Wait up to 100ms for the transform
  RCLCPP_INFO(get_logger(), "Point in base: (%.2f, %.2f, %.2f)",
    point_in_base.point.x, point_in_base.point.y, point_in_base.point.z);
} catch (const tf2::TransformException & ex) {
  RCLCPP_WARN(get_logger(), "Transform failed: %s", ex.what());
}
```

### Python listener

```python
import rclpy
from rclpy.node import Node
from tf2_ros import Buffer, TransformListener, TransformException
from rclpy.duration import Duration

class TargetTracker(Node):
    def __init__(self):
        super().__init__('target_tracker')
        self.tf_buffer = Buffer()
        self.tf_listener = TransformListener(self.tf_buffer, self)
        self.timer = self.create_timer(0.1, self.track)

    def track(self):
        try:
            t = self.tf_buffer.lookup_transform(
                'base_link', 'target_frame',
                rclpy.time.Time())  # Latest available
            self.get_logger().info(
                f'Target at x={t.transform.translation.x:.2f}, '
                f'y={t.transform.translation.y:.2f}')
        except TransformException as ex:
            self.get_logger().warn(f'Could not get transform: {ex}')
```

### Time-travel queries

```cpp
// Get the transform between two frames at a specific past time
auto past_time = get_clock()->now() - rclcpp::Duration::from_seconds(0.5);

auto t = tf_buffer_->lookupTransform(
  "map", "base_link",
  past_time,
  tf2::durationFromSec(0.1));  // Timeout for waiting

// Get the transform from frame A at time t1 to frame B at time t2
// (e.g., where was the robot relative to a map feature 2 seconds ago?)
auto t_advanced = tf_buffer_->lookupTransform(
  "map", rclcpp::Time(0),        // Target frame at latest time
  "base_link", past_time,        // Source frame at past time
  "map",                         // Fixed frame
  tf2::durationFromSec(0.1));
```

## 4. URDF structure and joint types

### Minimal URDF

```xml
<?xml version="1.0"?>
<robot name="my_robot">

  <!-- Base link -->
  <link name="base_link">
    <visual>
      <geometry><box size="0.5 0.3 0.1"/></geometry>
      <material name="blue"><color rgba="0 0 0.8 1"/></material>
    </visual>
    <collision>
      <geometry><box size="0.5 0.3 0.1"/></geometry>
    </collision>
    <inertial>
      <mass value="5.0"/>
      <inertia ixx="0.04" ixy="0" ixz="0"
               iyy="0.11" iyz="0" izz="0.14"/>
    </inertial>
  </link>

  <!-- Laser mount -->
  <link name="laser_link">
    <visual>
      <geometry><cylinder length="0.05" radius="0.03"/></geometry>
    </visual>
    <collision>
      <geometry><cylinder length="0.05" radius="0.03"/></geometry>
    </collision>
    <inertial>
      <mass value="0.1"/>
      <inertia ixx="0.0001" ixy="0" ixz="0"
               iyy="0.0001" iyz="0" izz="0.0001"/>
    </inertial>
  </link>

  <!-- Fixed joint (static transform) -->
  <joint name="laser_joint" type="fixed">
    <parent link="base_link"/>
    <child link="laser_link"/>
    <origin xyz="0.15 0 0.3" rpy="0 0 0"/>
  </joint>

</robot>
```

### Joint types

| Type | Motion | Example |
|---|---|---|
| `fixed` | No motion | Sensor mounts, fixed structural links |
| `revolute` | Rotation with limits | Robot arm joints, steering |
| `continuous` | Unlimited rotation | Wheels, spinning sensors |
| `prismatic` | Linear motion with limits | Linear actuators, grippers |
| `floating` | 6-DOF free motion | Drone links (rarely used) |
| `planar` | 2-DOF planar motion | XY tables (rarely used) |

### Revolute joint example

```xml
<joint name="joint_1" type="revolute">
  <parent link="base_link"/>
  <child link="link_1"/>
  <origin xyz="0 0 0.1" rpy="0 0 0"/>
  <axis xyz="0 0 1"/>           <!-- Rotation axis (Z) -->
  <limit lower="-3.14" upper="3.14"
         velocity="1.0" effort="50.0"/>
  <dynamics damping="0.1" friction="0.01"/>
</joint>
```

### Inertial properties

**Every link with mass must have correct inertials for simulation:**

```xml
<inertial>
  <origin xyz="0 0 0" rpy="0 0 0"/>  <!-- Center of mass -->
  <mass value="2.0"/>                  <!-- kg -->
  <inertia ixx="0.01" ixy="0" ixz="0"
           iyy="0.01" iyz="0"
           izz="0.01"/>                <!-- kg·m² -->
</inertial>
```

**Rules of thumb for inertia:**
- Box: `ixx = m/12 * (y² + z²)`, `iyy = m/12 * (x² + z²)`, `izz = m/12 * (x² + y²)`
- Cylinder (Z-axis): `ixx = iyy = m/12 * (3r² + h²)`, `izz = m/2 * r²`
- Sphere: `ixx = iyy = izz = 2/5 * m * r²`

## 5. Xacro macros and parameterization

### Why xacro

URDF is verbose and repetitive. Xacro adds:
- Properties (variables)
- Macros (reusable blocks)
- Math expressions
- Conditional blocks
- File inclusion

### Basic xacro file

```xml
<?xml version="1.0"?>
<robot xmlns:xacro="http://www.ros.org/wiki/xacro" name="my_robot">

  <!-- Properties (constants) -->
  <xacro:property name="base_width" value="0.3"/>
  <xacro:property name="base_length" value="0.5"/>
  <xacro:property name="base_height" value="0.1"/>
  <xacro:property name="wheel_radius" value="0.05"/>
  <xacro:property name="wheel_width" value="0.02"/>

  <!-- Math expressions -->
  <xacro:property name="base_mass" value="5.0"/>
  <xacro:property name="base_ixx"
    value="${base_mass / 12.0 * (base_width**2 + base_height**2)}"/>

  <!-- Include other xacro files -->
  <xacro:include filename="$(find my_robot_description)/urdf/materials.xacro"/>
  <xacro:include filename="$(find my_robot_description)/urdf/sensors.xacro"/>

  <!-- Conditional blocks -->
  <xacro:arg name="use_sim" default="false"/>
  <xacro:if value="$(arg use_sim)">
    <xacro:include filename="$(find my_robot_description)/urdf/gazebo.xacro"/>
  </xacro:if>

</robot>
```

### Reusable macro example (wheel)

```xml
<!-- Wheel macro — instantiate for left and right -->
<xacro:macro name="wheel" params="prefix reflect">
  <link name="${prefix}_wheel_link">
    <visual>
      <geometry>
        <cylinder length="${wheel_width}" radius="${wheel_radius}"/>
      </geometry>
      <material name="dark_grey"/>
    </visual>
    <collision>
      <geometry>
        <cylinder length="${wheel_width}" radius="${wheel_radius}"/>
      </geometry>
    </collision>
    <inertial>
      <mass value="0.5"/>
      <inertia ixx="${0.5/12.0 * (3*wheel_radius**2 + wheel_width**2)}"
               ixy="0" ixz="0"
               iyy="${0.5/12.0 * (3*wheel_radius**2 + wheel_width**2)}"
               iyz="0"
               izz="${0.5/2.0 * wheel_radius**2}"/>
    </inertial>
  </link>

  <joint name="${prefix}_wheel_joint" type="continuous">
    <parent link="base_link"/>
    <child link="${prefix}_wheel_link"/>
    <origin xyz="0 ${reflect * (base_width/2 + wheel_width/2)} 0"
            rpy="${-pi/2} 0 0"/>
    <axis xyz="0 0 1"/>
  </joint>
</xacro:macro>

<!-- Instantiate left and right wheels -->
<xacro:wheel prefix="left" reflect="1"/>
<xacro:wheel prefix="right" reflect="-1"/>
```

### Testing xacro files

```bash
# Check for syntax errors
xacro robot.urdf.xacro > /dev/null

# Generate and validate URDF
xacro robot.urdf.xacro > robot.urdf
check_urdf robot.urdf

# Visualize joint/link tree
urdf_to_graphviz robot.urdf
```

## 6. robot_state_publisher

`robot_state_publisher` takes a URDF and joint states, and publishes TF
transforms for every link in the robot.

### Launch configuration

```python
from launch_ros.actions import Node
from launch.substitutions import Command, PathJoinSubstitution
from launch_ros.substitutions import FindPackageShare

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
    parameters=[{
        'robot_description': robot_description,
        'publish_frequency': 50.0,          # Hz for TF publishing
        'ignore_timestamp': False,          # Use joint_state timestamps
        'frame_prefix': '',                 # Prefix for multi-robot
    }],
)
```

### What it publishes

- **`/tf`** — dynamic transforms for all non-fixed joints (based on `/joint_states`)
- **`/tf_static`** — static transforms for all fixed joints (published once, latched)
- **`/robot_description`** — the URDF string (TRANSIENT_LOCAL, for tools like RViz)

### joint_state_publisher for testing

For testing without real hardware:

```bash
# Interactive sliders
ros2 run joint_state_publisher_gui joint_state_publisher_gui
```

## 7. Debugging transforms

### Command-line tools

```bash
# View the TF tree as a PDF
ros2 run tf2_tools view_frames
# Generates frames.pdf showing all frames and their relationships

# Echo a specific transform
ros2 run tf2_ros tf2_echo base_link laser_link
# Shows translation and rotation at current time

# Monitor TF publishing rates
ros2 run tf2_ros tf2_monitor
# Shows all broadcasters, rates, and delays

# Check if a specific transform is available
ros2 run tf2_ros tf2_echo map base_link
# Will show errors if transform chain is broken
```

### Common debugging patterns

```bash
# List all frames
ros2 topic echo /tf --field transforms[0].header.frame_id | sort -u
ros2 topic echo /tf_static --field transforms[0].header.frame_id | sort -u

# Check transform rate and delay
ros2 run tf2_ros tf2_monitor base_link laser_link

# View in RViz — set Fixed Frame to "map" or "odom" and add TF display
```

## 8. Multi-robot TF trees

### Namespaced TF with frame_prefix

```python
# Robot 1
robot_1 = GroupAction([
    PushRosNamespace('robot_1'),
    Node(
        package='robot_state_publisher',
        executable='robot_state_publisher',
        parameters=[{
            'robot_description': robot_description,
            'frame_prefix': 'robot_1/',
        }],
        remappings=[('/joint_states', 'joint_states')],
    ),
])
```

This produces frames like `robot_1/base_link`, `robot_1/laser_link`, etc.

### Multi-robot frame tree

```
map
 ├── robot_1/odom
 │    └── robot_1/base_link
 │         ├── robot_1/laser_link
 │         └── robot_1/camera_link
 └── robot_2/odom
      └── robot_2/base_link
           ├── robot_2/laser_link
           └── robot_2/camera_link
```

**Important:** Each robot's localization node must publish
`map → robot_N/odom`, not `map → odom`. Otherwise the transforms conflict.

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| "Lookup would require extrapolation into the future" | Publisher clock skew or insufficient TF buffer | Use `tf2::TimePointZero` for latest, or increase buffer timeout |
| "Could not find a connection between X and Y" | Missing link in the TF chain | Run `ros2 run tf2_tools view_frames`, check for broken chain |
| TF tree has two separate trees | No transform connecting subtrees | Ensure localization publishes `map → odom` and odometry publishes `odom → base_link` |
| Frames appear at wrong position in RViz | Wrong URDF origin or joint axis | Check `<origin>` xyz/rpy values; test with `joint_state_publisher_gui` |
| "Multiple authority errors" for same transform | Two nodes publishing the same transform | Only one node should own each parent → child transform |
| Camera data appears rotated | Optical frame convention not followed | Add optical frame child with `rpy="-π/2 0 -π/2"` rotation |
| Transform delay causes stale data | High-latency TF publisher | Increase TF buffer duration, check publisher rate |
| `frame_prefix` not applied | Using wrong RSP version or missing parameter | Verify `frame_prefix` parameter is set in robot_state_publisher |
