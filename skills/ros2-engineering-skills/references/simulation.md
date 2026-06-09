# Simulation Integration

## Table of contents

1. [Gazebo version matrix](#1-gazebo-version-matrix)
2. [ros_gz_bridge -- topic and service bridging](#2-ros_gz_bridge----topic-and-service-bridging)
3. [gz_ros2_control -- unified hardware interface](#3-gz_ros2_control----unified-hardware-interface)
4. [Simulation time (use_sim_time)](#4-simulation-time-use_sim_time)
5. [Gazebo sensor plugins](#5-gazebo-sensor-plugins)
6. [Isaac Sim integration](#6-isaac-sim-integration)
7. [Sim-to-real transfer strategies](#7-sim-to-real-transfer-strategies)
8. [Headless simulation for CI](#8-headless-simulation-for-ci)
9. [Simulation reproducibility](#9-simulation-reproducibility)
10. [Common failures and fixes](#10-common-failures-and-fixes)

---

## 1. Gazebo version matrix

| ROS 2 Distro | Gazebo Version | Package Prefix | Notes |
|---|---|---|---|
| Humble | Fortress (LTS) | `ros-humble-ros-gz-*` (or `ros-humble-ros-ign-*` legacy) | Last release using Ignition branding |
| Jazzy | Harmonic (LTS) | `ros-jazzy-ros-gz-*` | Recommended for new projects |
| Kilted | Ionic | `ros-kilted-ros-gz-*` | Non-LTS distro |
| Rolling | Jetty / latest | `ros-rolling-ros-gz-*` | Tracks latest Gazebo |

**Critical**: Do NOT mix Gazebo versions with the wrong ROS 2 distro. The `ros_gz`
packages are built against a specific Gazebo major version. Linking against the wrong
one produces segfaults, silent message corruption, or missing symbols at runtime.

Gazebo was renamed from "Ignition" in 2022. On Humble, `ros-humble-ros-ign-*` shim
packages exist but are deprecated. On Jazzy+ only the `ros-gz-*` prefix exists.

```bash
# WRONG: Installing Gazebo Harmonic on a Humble system -- will break ros_gz
sudo apt install gz-harmonic  # DO NOT do this on Humble

# CORRECT: Let ros_gz pull in the right Gazebo version
sudo apt install ros-humble-ros-gz    # Humble
sudo apt install ros-jazzy-ros-gz     # Jazzy
```

---

## 2. ros_gz_bridge -- topic and service bridging

The `ros_gz_bridge` translates messages between ROS 2 and Gazebo transport.

### Bridging direction syntax

Format: `<topic>@<ros_type><direction><gz_type>`

| Char | Direction | Use case |
|---|---|---|
| `@` | Bidirectional | `/cmd_vel@geometry_msgs/msg/Twist@gz.msgs.Twist` |
| `[` | GZ -> ROS only | `/scan@sensor_msgs/msg/LaserScan[gz.msgs.LaserScan` |
| `]` | ROS -> GZ only | `/cmd_vel@geometry_msgs/msg/Twist]gz.msgs.Twist` |

### Launch file bridge (Python)

```python
from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    bridge = Node(
        package='ros_gz_bridge',
        executable='parameter_bridge',
        arguments=[
            '/cmd_vel@geometry_msgs/msg/Twist@gz.msgs.Twist',
            '/scan@sensor_msgs/msg/LaserScan[gz.msgs.LaserScan',
            '/camera/image@sensor_msgs/msg/Image[gz.msgs.Image',
            '/camera/camera_info@sensor_msgs/msg/CameraInfo[gz.msgs.CameraInfo',
            '/imu@sensor_msgs/msg/Imu[gz.msgs.IMU',
            '/clock@rosgraph_msgs/msg/Clock[gz.msgs.Clock',
        ],
        output='screen',
    )
    return LaunchDescription([bridge])
```

### YAML parameter bridge configuration

```yaml
# bridge_config.yaml (Jazzy / Harmonic)
- ros_topic_name: "/cmd_vel"
  gz_topic_name: "/cmd_vel"
  ros_type_name: "geometry_msgs/msg/Twist"
  gz_type_name: "gz.msgs.Twist"
  direction: BIDIRECTIONAL
- ros_topic_name: "/scan"
  gz_topic_name: "/world/default/model/robot/link/lidar_link/sensor/lidar/scan"
  ros_type_name: "sensor_msgs/msg/LaserScan"
  gz_type_name: "gz.msgs.LaserScan"
  direction: GZ_TO_ROS
- ros_topic_name: "/clock"
  gz_topic_name: "/clock"
  ros_type_name: "rosgraph_msgs/msg/Clock"
  gz_type_name: "gz.msgs.Clock"
  direction: GZ_TO_ROS
```

```python
# Launch with YAML config
import os
from ament_index_python.packages import get_package_share_directory
from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    config = os.path.join(
        get_package_share_directory('my_robot_sim'), 'config', 'bridge_config.yaml')
    return LaunchDescription([Node(
        package='ros_gz_bridge', executable='parameter_bridge',
        arguments=['--ros-args', '-p', f'config_file:={config}'],
        output='screen',
    )])
```

**Anti-pattern -- forgetting the clock bridge**: sensor timestamps use sim time but
nodes on wall clock see them as "in the future." Always bridge `/clock`.

---

## 3. gz_ros2_control -- unified hardware interface

Use the same `ros2_control` controllers in simulation and on real hardware by
swapping the `<plugin>` via xacro conditionals.

```xml
<xacro:arg name="use_sim" default="false"/>
<ros2_control name="RobotSystem" type="system">
  <hardware>
    <xacro:if value="$(arg use_sim)">
      <plugin>gz_ros2_control/GazeboSimSystem</plugin>
    </xacro:if>
    <xacro:unless value="$(arg use_sim)">
      <plugin>my_robot_driver/MyRobotHardware</plugin>
      <param name="serial_port">/dev/ttyUSB0</param>
    </xacro:unless>
  </hardware>
  <joint name="joint_1">
    <command_interface name="position">
      <param name="min">-3.14</param>
      <param name="max">3.14</param>
    </command_interface>
    <state_interface name="position"/>
    <state_interface name="velocity"/>
  </joint>
</ros2_control>
```

**Distro-specific plugin names**: Humble uses `ign_ros2_control/IgnitionSystem`.
Jazzy/Kilted use `gz_ros2_control/GazeboSimSystem`.

### Gazebo SDF plugin tag

```xml
<!-- Jazzy / Harmonic -->
<plugin filename="gz_ros2_control-system"
        name="gz_ros2_control::GazeboSimROS2ControlPlugin">
  <parameters>$(find my_robot_bringup)/config/controllers.yaml</parameters>
</plugin>

<!-- Humble / Fortress -->
<plugin filename="ign_ros2_control-system"
        name="ign_ros2_control::IgnitionROS2ControlPlugin">
  <parameters>$(find my_robot_bringup)/config/controllers.yaml</parameters>
</plugin>
```

### Dynamic xacro processing with OpaqueFunction

`LaunchConfiguration` is not resolved at import time. Use `OpaqueFunction`:

```python
from launch import LaunchDescription
from launch.actions import DeclareLaunchArgument, OpaqueFunction
from launch.substitutions import LaunchConfiguration
from launch_ros.actions import Node
import xacro, os
from ament_index_python.packages import get_package_share_directory

def launch_setup(context):
    use_sim = LaunchConfiguration('use_sim').perform(context)
    robot_desc = xacro.process_file(
        os.path.join(get_package_share_directory('my_robot_bringup'),
                     'urdf', 'robot.urdf.xacro'),
        mappings={'use_sim': use_sim}
    ).toxml()
    return [Node(
        package='robot_state_publisher', executable='robot_state_publisher',
        parameters=[{'robot_description': robot_desc,
                     'use_sim_time': use_sim == 'true'}],
    )]

def generate_launch_description():
    return LaunchDescription([
        DeclareLaunchArgument('use_sim', default_value='false'),
        OpaqueFunction(function=launch_setup),
    ])
```

**Anti-pattern**: hardcoding `gz_ros2_control/GazeboSimSystem` without a xacro
conditional. Deploying that URDF to real hardware will fail silently or crash.

---

## 4. Simulation time (`use_sim_time`)

Gazebo publishes `rosgraph_msgs/msg/Clock` on `/clock`. When a node has
`use_sim_time: true`, `this->now()` / `self.get_clock().now()` tracks `/clock`
instead of the system wall clock.

**The golden rule**: every node must agree on the time source. One node on wall time
while others use sim time produces `TF extrapolation into the future` errors.

```python
use_sim_time = LaunchConfiguration('use_sim_time', default='true')
# Pass to EVERY node:
Node(package='robot_state_publisher', executable='robot_state_publisher',
     parameters=[{'use_sim_time': use_sim_time}])
Node(package='rviz2', executable='rviz2',
     parameters=[{'use_sim_time': use_sim_time}])
```

### C++ -- sim-time-aware timers

```cpp
// WRONG: create_wall_timer ignores use_sim_time, fires during paused sim
timer_ = this->create_wall_timer(100ms, std::bind(&MyNode::cb, this));

// CORRECT: use the node's clock
timer_ = rclcpp::create_timer(
    this, this->get_clock(), rclcpp::Duration::from_seconds(0.1),
    std::bind(&MyNode::cb, this));
```

Python `create_timer()` respects `use_sim_time` automatically.

When Gazebo is paused, `/clock` stops and all sim-time nodes freeze their timers.

```bash
# Verify time consistency
ros2 param get /robot_state_publisher use_sim_time
ros2 topic echo /clock --once
```

---

## 5. Gazebo sensor plugins

### Camera

```xml
<sensor name="camera" type="camera">
  <always_on>true</always_on>
  <update_rate>30</update_rate>
  <camera>
    <horizontal_fov>1.3962634</horizontal_fov>
    <image><width>640</width><height>480</height><format>R8G8B8</format></image>
    <clip><near>0.02</near><far>300</far></clip>
  </camera>
  <topic>camera/image</topic>
</sensor>
```

Bridge: `/camera/image@sensor_msgs/msg/Image[gz.msgs.Image`

### GPU LiDAR

```xml
<sensor name="lidar" type="gpu_lidar">
  <always_on>true</always_on>
  <update_rate>10</update_rate>
  <lidar>
    <scan>
      <horizontal>
        <samples>640</samples><resolution>1</resolution>
        <min_angle>-3.14159</min_angle><max_angle>3.14159</max_angle>
      </horizontal>
    </scan>
    <range><min>0.08</min><max>10.0</max><resolution>0.01</resolution></range>
  </lidar>
  <topic>lidar/scan</topic>
</sensor>
```

Bridge: `/lidar/scan@sensor_msgs/msg/LaserScan[gz.msgs.LaserScan`

### IMU (with noise)

```xml
<sensor name="imu" type="imu">
  <always_on>true</always_on>
  <update_rate>100</update_rate>
  <imu>
    <angular_velocity>
      <x><noise type="gaussian"><mean>0</mean><stddev>0.0002</stddev></noise></x>
      <y><noise type="gaussian"><mean>0</mean><stddev>0.0002</stddev></noise></y>
      <z><noise type="gaussian"><mean>0</mean><stddev>0.0002</stddev></noise></z>
    </angular_velocity>
  </imu>
  <topic>imu</topic>
</sensor>
```

Bridge: `/imu@sensor_msgs/msg/Imu[gz.msgs.IMU`

### NavSat (GPS)

```xml
<sensor name="navsat" type="navsat">
  <always_on>true</always_on>
  <update_rate>5</update_rate>
  <topic>navsat</topic>
</sensor>
```

Bridge: `/navsat@sensor_msgs/msg/NavSatFix[gz.msgs.NavSat`

### Depth camera

```xml
<sensor name="depth_camera" type="depth_camera">
  <always_on>true</always_on>
  <update_rate>15</update_rate>
  <camera>
    <horizontal_fov>1.047</horizontal_fov>
    <image><width>640</width><height>480</height></image>
    <clip><near>0.1</near><far>10.0</far></clip>
  </camera>
  <topic>depth_camera</topic>
</sensor>
```

Bridge entries:

```
/depth_camera/depth_image@sensor_msgs/msg/Image[gz.msgs.Image
/depth_camera/points@sensor_msgs/msg/PointCloud2[gz.msgs.PointCloudPacked
```

---

## 6. Isaac Sim integration

NVIDIA Isaac Sim provides photorealistic simulation with a built-in ROS 2 bridge.

| Aspect | Gazebo | Isaac Sim |
|---|---|---|
| Physics engine | DART / Bullet | PhysX 5 |
| Rendering | OGRE2 | RTX ray tracing |
| ROS 2 bridge | External `ros_gz_bridge` | Built-in OmniGraph nodes |
| License | Apache 2.0 | NVIDIA EULA (free for individuals) |
| Headless | Native (`-s` flag) | Requires GPU |

### Action Graph for ROS 2 topics

```python
import omni.graph.core as og

keys = og.Controller.Keys
og.Controller.edit(
    {"graph_path": "/ActionGraph", "evaluator_name": "execution"},
    {
        keys.CREATE_NODES: [
            ("OnPlaybackTick", "omni.graph.action.OnPlaybackTick"),
            ("PublishClock", "omni.isaac.ros2_bridge.ROS2PublishClock"),
            ("PublishTF", "omni.isaac.ros2_bridge.ROS2PublishTransformTree"),
            ("PublishJointState", "omni.isaac.ros2_bridge.ROS2PublishJointState"),
        ],
        keys.CONNECT: [
            ("OnPlaybackTick.outputs:tick", "PublishClock.inputs:execIn"),
            ("OnPlaybackTick.outputs:tick", "PublishTF.inputs:execIn"),
            ("OnPlaybackTick.outputs:tick", "PublishJointState.inputs:execIn"),
        ],
        keys.SET_VALUES: [
            ("PublishJointState.inputs:topicName", "/joint_states"),
        ],
    },
)
```

### NVIDIA NITROS

Isaac ROS packages use NITROS to keep data on the GPU through the perception
pipeline, avoiding costly GPU-to-CPU-to-GPU transfers. NITROS-accelerated nodes
are drop-in replacements but require an NVIDIA GPU.

### When to choose each

**Isaac Sim**: photorealistic rendering, synthetic data generation, GPU-accelerated
sensors, high-fidelity contact physics, NVIDIA RTX GPU available.

**Gazebo**: lightweight, runs on any hardware, open-source, CI without GPU, broadest
ROS 2 ecosystem compatibility.

---

## 7. Sim-to-real transfer strategies

### The reality gap

| Transfers well | Requires tuning | Often fails |
|---|---|---|
| Kinematic structure | Contact dynamics | Deformable objects |
| Sensor geometry | Motor response curves | Fluid dynamics |
| High-level planning | Friction coefficients | Cable/hose routing |
| Navigation algorithms | Sensor noise profiles | Soft material grasping |

### Domain randomization

```python
import random

def randomize_physics():
    return {
        'mass': random.uniform(0.7, 1.3),         # +/- 30%
        'friction': random.uniform(0.5, 1.5),
        'damping': random.uniform(0.001, 0.01),
        'gravity_z': random.uniform(-9.91, -9.71),
    }
```

### System identification

```python
import numpy as np
from scipy.optimize import minimize

def cost_function(params):
    sim_traj = run_simulation(params, trajectory_input)
    real_traj = np.load('real_trajectory.npy')
    return np.sum((sim_traj - real_traj) ** 2)

result = minimize(cost_function, x0=[0.8, 0.005, 1.0, 0.01],
    bounds=[(0.1, 2.0), (0.001, 0.1), (0.5, 1.5), (0.0, 0.05)],
    method='L-BFGS-B')
```

### Control gap: actuator model

```python
from collections import deque
import numpy as np

class ActuatorModel:
    """Models delay, backlash, stiction, and velocity limits of real actuators.

    Real actuators exhibit:
    - Transport delay (communication + processing latency)
    - Backlash (mechanical play in gears)
    - Stiction (static friction threshold before motion begins)
    - Velocity limits (motor saturation)
    - Temperature-dependent behavior (not modeled here — use sysid for this)
    """
    def __init__(self, delay_steps=3, backlash_rad=0.005,
                 stiction_torque=0.1, vel_limit=2.0):
        self.delay_buffer = deque([0.0] * delay_steps, maxlen=delay_steps)
        self.backlash = backlash_rad
        self.stiction = stiction_torque
        self.vel_limit = vel_limit
        self.last_pos = 0.0
        self.last_dir = 0  # Track direction for backlash hysteresis

    def apply(self, cmd: float, dt: float = 0.01) -> float:
        self.delay_buffer.append(cmd)
        delayed = self.delay_buffer[0]

        # Stiction: no movement if command delta is below stiction threshold
        error = delayed - self.last_pos
        if abs(error) < self.stiction:
            return self.last_pos

        # Backlash: dead zone on direction reversal
        new_dir = 1 if error > 0 else -1
        if new_dir != self.last_dir:
            error = max(0.0, abs(error) - self.backlash) * new_dir
            self.last_dir = new_dir

        # Velocity limit
        max_step = self.vel_limit * dt
        delta = np.clip(error, -max_step, max_step)
        self.last_pos += delta
        return self.last_pos
```

### Domain randomization with Gazebo SDF parameters

Python-side randomization alone is insufficient — the most impactful parameters
(inertia, friction, damping) must be set in the physics engine via SDF.

```python
import subprocess, tempfile, os

def launch_with_randomized_physics(base_sdf: str, randomize_fn):
    """Generate a randomized SDF and launch Gazebo with it."""
    import xml.etree.ElementTree as ET
    tree = ET.parse(base_sdf)
    root = tree.getroot()
    params = randomize_fn()

    # Randomize surface friction on all collision elements
    for surface in root.iter('surface'):
        friction = surface.find('.//mu')
        if friction is not None:
            friction.text = str(params['friction'])

    # Randomize inertial properties
    for inertial in root.iter('inertial'):
        mass = inertial.find('mass')
        if mass is not None:
            mass.text = str(float(mass.text) * params['mass_scale'])

    with tempfile.NamedTemporaryFile(suffix='.sdf', delete=False, mode='wb') as f:
        tree.write(f, xml_declaration=True)
        randomized_sdf = f.name

    subprocess.run(['gz', 'sim', '-s', '-r', randomized_sdf])
    os.unlink(randomized_sdf)
```

---

## 8. Headless simulation for CI

```bash
gz sim -s -r world.sdf       # -s = server only, -r = run immediately
gz sim -s -r -v 4 world.sdf  # -v 4 = debug verbosity
```

### GitHub Actions workflow

```yaml
name: Simulation Tests
on: { pull_request: { branches: [main] } }
jobs:
  sim-test:
    runs-on: ubuntu-24.04
    container: { image: "osrf/ros:jazzy-desktop" }
    steps:
      - uses: actions/checkout@v4
      - name: Install deps
        run: apt-get update && apt-get install -y ros-jazzy-ros-gz
      - name: Test
        timeout-minutes: 10
        run: |
          source /opt/ros/jazzy/setup.bash && colcon build
          source install/setup.bash
          gz sim -s -r test_world.sdf &
          sleep 5
          ros2 launch my_robot_sim test.launch.py use_sim_time:=true &
          sleep 10
          ros2 topic echo /test_result --once --timeout 30
```

### launch_testing integration test

```python
import unittest, time, rclpy
from geometry_msgs.msg import Twist
from nav_msgs.msg import Odometry
import launch, launch_ros, launch_testing, launch_testing.actions
import pytest

@pytest.mark.launch_test
def generate_test_description():
    return launch.LaunchDescription([
        launch.actions.ExecuteProcess(
            cmd=['gz', 'sim', '-s', '-r', 'test_world.sdf'], output='screen'),
        launch_ros.actions.Node(
            package='ros_gz_bridge', executable='parameter_bridge',
            arguments=['/cmd_vel@geometry_msgs/msg/Twist@gz.msgs.Twist',
                       '/odom@nav_msgs/msg/Odometry[gz.msgs.Odometry',
                       '/clock@rosgraph_msgs/msg/Clock[gz.msgs.Clock'],
            parameters=[{'use_sim_time': True}]),
        launch_testing.actions.ReadyToTest(),
    ])

class TestSimulation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        rclpy.init()
        cls.node = rclpy.create_node('test_node')

    @classmethod
    def tearDownClass(cls):
        cls.node.destroy_node()
        rclpy.shutdown()

    def test_robot_moves(self):
        pub = self.node.create_publisher(Twist, '/cmd_vel', 10)
        received = []
        self.node.create_subscription(
            Odometry, '/odom', lambda m: received.append(m), 10)
        twist = Twist()
        twist.linear.x = 0.5
        end = time.time() + 15.0
        while time.time() < end and len(received) < 5:
            pub.publish(twist)
            rclpy.spin_once(self.node, timeout_sec=0.1)
        self.assertGreater(len(received), 0)
        self.assertGreater(received[-1].pose.pose.position.x, 0.01)
```

---

## 9. Simulation reproducibility

### The determinism problem

Gazebo simulations are **not perfectly deterministic** across runs due to:
- Thread scheduling order affecting physics solver convergence
- Floating-point operation ordering differences
- DDS discovery timing affecting when nodes start publishing

For debugging and regression testing, maximize reproducibility:

```xml
<!-- Force deterministic mode: single-threaded physics, fixed seed -->
<physics name="deterministic" type="dart">
  <real_time_factor>0</real_time_factor>   <!-- Run as fast as possible, no wall clock sync -->
  <max_step_size>0.001</max_step_size>     <!-- Fixed step size -->
</physics>
```

```bash
# Run in server mode (no GUI) with deterministic stepping
gz sim -s -r world.sdf

# For iteration-limited runs (e.g., exactly 10000 steps), use the C++ API:
#   gz::sim::Server server(serverConfig);
#   server.Run(/*blocking=*/true, /*iterations=*/10000, /*paused=*/false);
# The gz sim CLI does not have an --iterations flag.
```

> **Note:** Gazebo Sim does not provide a single global `GZ_SIM_SEED` environment
> variable. Sensor noise seeds must be configured per-sensor in SDF via the
> `<noise><seed>` element (where supported by the plugin).

**For regression tests:** Record a rosbag of the "golden" run, then compare future
runs against it. Use `ros2 bag play` with `--clock` to reproduce timing exactly.

### Physics step size vs sensor update rate

The relationship between `max_step_size` and sensor `update_rate` is critical:

| Setting | Effect |
|---|---|
| `max_step_size > 1/update_rate` | Sensor may fire 0 or 1 times per physics step — data loss |
| `max_step_size = 1/update_rate` | Exactly one sensor reading per step — ideal for determinism |
| `max_step_size << 1/update_rate` | Multiple physics steps between sensor updates — realistic but slower |

```xml
<!-- GOOD: step_size (1ms) < sensor period (10ms = 100Hz) -->
<physics name="good" type="dart">
  <max_step_size>0.001</max_step_size>
</physics>
<sensor type="imu" update_rate="100">...</sensor>

<!-- BAD: step_size (20ms) > sensor period (10ms) — sensor updates are missed -->
<physics name="bad" type="dart">
  <max_step_size>0.02</max_step_size>
</physics>
<sensor type="imu" update_rate="100">...</sensor>
```

**Anti-pattern: `real_time_factor > 10` with large `max_step_size`:**
Setting `real_time_factor=100` with `max_step_size=0.01` means each physics step
covers 10ms of sim time but the solver takes only one iteration. Contact dynamics
become unstable, objects tunnel through walls, and joints explode. Keep
`max_step_size <= 0.002` even when accelerating time.

## 10. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Gazebo segfaults on startup | Wrong Gazebo version for distro | Match versions per matrix (Section 1) |
| Bridge publishes nothing | Type mismatch or wrong `@`/`[`/`]` | Verify with `gz topic -l`; check syntax |
| Robot falls through ground | Missing `<collision>` or bad inertia | Add collision geometry; check inertia tensors |
| TF extrapolation into the future | Mixed sim/wall time | `use_sim_time: true` on ALL nodes |
| Controllers do not move robot | `gz_ros2_control` plugin missing | Add `<plugin filename="gz_ros2_control-system">` to SDF |
| No sensor data in ROS 2 | Bridge not configured for sensor topics | Add bridge entries per Section 5 |
| Simulation extremely slow | GPU not used | Install drivers; use `gpu_lidar` not `lidar` |
| Isaac Sim not publishing | OmniGraph not connected | Check Action Graph; verify ROS 2 bridge extension |
| `waiting for /clock` | Gazebo not running or paused | Start Gazebo before bridge; use `-r` flag |
| Joints stuck at zero | Controller not activated | `ros2 control switch_controllers --activate <name>` |

### Diagnostic commands

```bash
gz topic -l                             # List Gazebo topics
ros2 topic hz /scan                     # Verify bridge data flow
ros2 control list_controllers           # Show controller states
ros2 run tf2_tools view_frames          # Generate TF tree
```

### Bridge type reference

| ROS 2 Type | Correct GZ Type | Common Mistake |
|---|---|---|
| `sensor_msgs/msg/LaserScan` | `gz.msgs.LaserScan` | `gz.msgs.Lidar` |
| `sensor_msgs/msg/Image` | `gz.msgs.Image` | `gz.msgs.CameraImage` |
| `sensor_msgs/msg/Imu` | `gz.msgs.IMU` | `gz.msgs.Imu` (case) |
| `sensor_msgs/msg/PointCloud2` | `gz.msgs.PointCloudPacked` | `gz.msgs.PointCloud` |

### Physics tuning for CI

```xml
<!-- Faster-than-real-time for CI testing (Gz Sim uses DART by default) -->
<physics name="fast_physics" type="dart">
  <real_time_factor>5.0</real_time_factor>
  <max_step_size>0.001</max_step_size>
</physics>
<!-- Anti-pattern: real_time_factor=100 + step_size=0.01 causes instability -->
```
