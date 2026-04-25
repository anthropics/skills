# Multi-Robot Systems

## Table of contents
1. Communication isolation strategies
2. Namespace-based multi-robot patterns
3. Open-RMF for fleet management
4. Free Fleet adapter pattern
5. Task allocation frameworks
6. Cooperative SLAM and map merging
7. DDS discovery at scale
8. Clock synchronization (NTP/PTP)
9. Common failures and fixes

---

## 1. Communication isolation strategies

| Strategy | Isolation level | Cross-robot comms | Discovery overhead | Best for |
|---|---|---|---|---|
| ROS_DOMAIN_ID | Complete per domain | Requires bridge | None between domains | < 10 robots, simple |
| Namespace + topic filtering | Soft isolation | Direct via shared topics | Full graph visible | 10-50 robots |
| Zenoh routing | Configurable | Selective bridging | Minimal | 50+ robots, WAN |
| DDS partitions | Topic-level | Via partition matching | Reduced discovery | Mixed workloads |

### Domain ID strategy

```bash
export ROS_DOMAIN_ID=1  # Robot A
export ROS_DOMAIN_ID=2  # Robot B
```

Limitation: ROS 2 restricts domain IDs to 0-101 on Linux and 0-166 on macOS/Windows (the raw DDS maximum is 232, but ROS 2 uses additional port offsets per participant that overflow the 16-bit port range earlier). In practice, keep domain IDs below 100. For fleets > 100 robots, use namespacing or Zenoh instead of domain IDs.

### Namespace strategy (recommended for most cases)

```xml
<group>
  <push_ros_namespace namespace="robot_01"/>
  <include file="$(find-pkg-share my_robot)/launch/bringup.launch.py"/>
</group>
```

All topics/services/actions are prefixed: `/robot_01/cmd_vel`, `/robot_01/scan`, etc.

---

## 2. Namespace-based multi-robot patterns

### Launch file for N robots

```python
from launch import LaunchDescription
from launch.actions import GroupAction
from launch_ros.actions import PushRosNamespace
from launch.actions import IncludeLaunchDescription
from launch.launch_description_sources import PythonLaunchDescriptionSource
from launch.substitutions import PathJoinSubstitution
from launch_ros.substitutions import FindPackageShare

def generate_launch_description():
    robots = [
        {'name': 'robot_01', 'x': '0.0', 'y': '0.0'},
        {'name': 'robot_02', 'x': '2.0', 'y': '0.0'},
        {'name': 'robot_03', 'x': '0.0', 'y': '2.0'},
    ]
    launch_items = []
    for robot in robots:
        group = GroupAction([
            PushRosNamespace(robot['name']),
            IncludeLaunchDescription(
                PythonLaunchDescriptionSource([PathJoinSubstitution([
                    FindPackageShare('my_robot'), 'launch', 'single_robot.launch.py'
                ])]),
                launch_arguments={
                    'robot_name': robot['name'], 'x': robot['x'],
                    'y': robot['y'], 'use_sim_time': 'true',
                }.items(),
            ),
        ])
        launch_items.append(group)
    return LaunchDescription(launch_items)
```

### TF frame isolation

Each robot needs unique TF frames. Use `frame_prefix` parameter in `robot_state_publisher`:

```python
Node(
    package='robot_state_publisher',
    executable='robot_state_publisher',
    namespace=robot_name,
    parameters=[{
        'robot_description': robot_description,
        'frame_prefix': robot_name + '/',
    }],
)
```

This produces frames: `robot_01/base_link`, `robot_01/odom`, etc. Without `frame_prefix`, all robots publish identically-named frames, causing TF to oscillate between conflicting transforms.

### Nav2 with namespace

Nav2 parameters must reference namespaced frames:

```yaml
local_costmap:
  local_costmap:
    ros__parameters:
      robot_base_frame: robot_01/base_link
      global_frame: robot_01/odom
global_costmap:
  global_costmap:
    ros__parameters:
      robot_base_frame: robot_01/base_link
      global_frame: map  # Shared map frame across all robots
```

Shared topics (`/tf`, `/tf_static`, `/map`) remain global. Per-robot topics (`/cmd_vel`, `/scan`, `/amcl_pose`) are isolated via namespace.

---

## 3. Open-RMF for fleet management

Open-RMF (Robotics Middleware Framework) manages heterogeneous robot fleets in shared spaces. Architecture: RMF Core (schedule database, traffic manager, task dispatcher) connects to per-fleet Fleet Adapters, which bridge to robot-specific navigation (Nav2, proprietary, etc.).

```bash
# Jazzy
sudo apt install ros-jazzy-rmf-fleet-adapter ros-jazzy-rmf-traffic-ros2
# Humble
sudo apt install ros-humble-rmf-fleet-adapter ros-humble-rmf-traffic-ros2
```

### Fleet adapter implementation pattern

```python
from rclpy.node import Node
from rmf_fleet_msgs.msg import FleetState, RobotState, RobotMode, Location
from geometry_msgs.msg import PoseStamped, PoseWithCovarianceStamped
from nav2_msgs.action import NavigateToPose
from rclpy.action import ActionClient
import math

class Nav2FleetAdapter(Node):
    """Bridges Open-RMF and Nav2-based robots."""
    def __init__(self):
        super().__init__('nav2_fleet_adapter')
        self.declare_parameter('fleet_name', 'my_fleet')
        self.declare_parameter('robot_names', ['robot_01', 'robot_02'])
        self.fleet_name = self.get_parameter('fleet_name').value

        self.fleet_state_pub = self.create_publisher(FleetState, 'fleet_states', 10)
        self.robots = {}
        for name in self.get_parameter('robot_names').value:
            self.robots[name] = {
                'nav_client': ActionClient(self, NavigateToPose, f'/{name}/navigate_to_pose'),
                'pose': None, 'mode': RobotMode.MODE_IDLE,
            }
            # AMCL publishes PoseWithCovarianceStamped, not PoseStamped
            self.create_subscription(
                PoseWithCovarianceStamped, f'/{name}/amcl_pose',
                lambda msg, n=name: self._pose_cb(n, msg), 10)
        self.create_timer(0.5, self._publish_fleet_state)

    def _pose_cb(self, robot_name, msg):
        self.robots[robot_name]['pose'] = msg

    def _publish_fleet_state(self):
        fleet_msg = FleetState()
        fleet_msg.name = self.fleet_name
        for name, state in self.robots.items():
            robot_msg = RobotState()
            robot_msg.name = name
            robot_msg.mode.mode = state['mode']
            if state['pose']:
                loc = Location()
                loc.x = state['pose'].pose.pose.position.x
                loc.y = state['pose'].pose.pose.position.y
                q = state['pose'].pose.pose.orientation
                loc.yaw = math.atan2(2.0*(q.w*q.z + q.x*q.y), 1.0 - 2.0*(q.y*q.y + q.z*q.z))
                loc.t = self.get_clock().now().to_msg()
                loc.level_name = 'L1'
                robot_msg.location = loc
            fleet_msg.robots.append(robot_msg)
        self.fleet_state_pub.publish(fleet_msg)

    def send_robot_to(self, robot_name, x, y, yaw):
        goal = NavigateToPose.Goal()
        goal.pose.header.frame_id = 'map'
        goal.pose.pose.position.x, goal.pose.pose.position.y = x, y
        goal.pose.pose.orientation.z = math.sin(yaw / 2.0)
        goal.pose.pose.orientation.w = math.cos(yaw / 2.0)
        self.robots[robot_name]['mode'] = RobotMode.MODE_MOVING
        future = self.robots[robot_name]['nav_client'].send_goal_async(goal)
        future.add_done_callback(lambda f, n=robot_name: self._nav_done(n, f))

    def _nav_done(self, robot_name, future):
        goal_handle = future.result()
        if not goal_handle.accepted:
            self.get_logger().warn(f'{robot_name}: goal rejected')
            self.robots[robot_name]['mode'] = RobotMode.MODE_IDLE
            return
        # Wait for actual navigation completion before marking IDLE
        goal_handle.get_result_async().add_done_callback(
            lambda f, n=robot_name: self._on_nav_result(n, f))

    def _on_nav_result(self, robot_name, future):
        self.robots[robot_name]['mode'] = RobotMode.MODE_IDLE
```

---

## 4. Free Fleet adapter pattern

Free Fleet provides a simpler alternative to full Open-RMF for basic fleet coordination without traffic deconfliction. Client-server model: the server tracks all robots centrally; a client on each robot reports state and accepts navigation commands.

```bash
sudo apt install ros-humble-free-fleet ros-humble-free-fleet-client-ros2  # may need source build on Jazzy
```

### Client launch

```python
Node(
    package='free_fleet_client_ros2',
    executable='free_fleet_client_ros2',
    name='free_fleet_client',
    parameters=[{
        'fleet_name': 'my_fleet',
        'robot_name': 'robot_01',
        'navigate_to_pose_action': '/robot_01/navigate_to_pose',
        'update_frequency': 2.0,
        'robot_frame': 'robot_01/base_footprint',
        'map_frame': 'map',
    }],
)
```

---

## 5. Task allocation frameworks

| Approach | Best for | Complexity | Optimality |
|---|---|---|---|
| Round-robin | Equal robots, uniform tasks | Simple | Poor |
| Nearest-first (greedy) | Delivery/pickup tasks | Simple | Good locally |
| Hungarian algorithm | Optimal assignment, small fleets | Medium | Optimal |
| Market-based (auction) | Heterogeneous capabilities, dynamic | Medium | Near-optimal |
| Deep RL | Complex optimization, large fleets | High | Learned |

### Nearest-robot task allocator

```python
from rclpy.node import Node
from rclpy.action import ActionClient
from geometry_msgs.msg import PoseStamped, PoseWithCovarianceStamped
from nav2_msgs.action import NavigateToPose
import math

class TaskAllocator(Node):
    """Assigns waypoint goals to the nearest idle robot."""
    def __init__(self):
        super().__init__('task_allocator')
        self.declare_parameter('robot_names', ['robot_01', 'robot_02', 'robot_03'])
        self.robot_poses, self.robot_status, self.nav_clients = {}, {}, {}
        for name in self.get_parameter('robot_names').value:
            self.robot_status[name] = 'idle'
            self.create_subscription(
                PoseWithCovarianceStamped, f'/{name}/amcl_pose',
                lambda msg, n=name: self._pose_cb(n, msg), 10)
            self.nav_clients[name] = ActionClient(
                self, NavigateToPose, f'/{name}/navigate_to_pose')
        self.create_subscription(PoseStamped, 'task_queue', self._task_queue_cb, 10)

    def _pose_cb(self, robot_name, msg):
        self.robot_poses[robot_name] = PoseStamped(header=msg.header, pose=msg.pose.pose)

    def _task_queue_cb(self, msg):
        assigned = self.allocate_task(msg)
        self.get_logger().info(f'Assigned to {assigned}' if assigned else 'No idle robots')

    def allocate_task(self, target_pose):
        idle = [r for r, s in self.robot_status.items() if s == 'idle' and r in self.robot_poses]
        if not idle:
            return None
        nearest = min(idle, key=lambda r: math.hypot(
            self.robot_poses[r].pose.position.x - target_pose.pose.position.x,
            self.robot_poses[r].pose.position.y - target_pose.pose.position.y))
        goal = NavigateToPose.Goal()
        goal.pose = target_pose
        self.nav_clients[nearest].wait_for_server(timeout_sec=5.0)
        future = self.nav_clients[nearest].send_goal_async(goal)
        future.add_done_callback(lambda f, n=nearest: self._goal_response_cb(n, f))
        self.robot_status[nearest] = 'busy'
        return nearest

    def _goal_response_cb(self, robot_name, future):
        gh = future.result()
        if not gh.accepted:
            self.robot_status[robot_name] = 'idle'
            return
        gh.get_result_async().add_done_callback(
            lambda f, n=robot_name: self._mark_idle(n))

    def _mark_idle(self, robot_name):
        self.robot_status[robot_name] = 'idle'
```

---

## 6. Cooperative SLAM and map merging

### Multi-robot SLAM approaches

| Method | When to use | Complexity |
|---|---|---|
| Centralized SLAM | Reliable network, <5 robots, one powerful computer | Medium |
| Distributed SLAM + map merging | Intermittent connectivity, 5-20 robots | High |
| Pre-built shared map + AMCL per robot | Known environment, simplest approach | Low |

### Recommended production pattern

Build the map once with one robot (`slam_toolbox`), save it, then deploy AMCL on all robots with the shared map. This avoids multi-robot SLAM complexity entirely.

```bash
ros2 launch slam_toolbox online_async_launch.py   # map with one robot
ros2 run nav2_map_server map_saver_cli -f warehouse  # save map
# Deploy AMCL on each namespaced robot loading the same map file
```

### Map merging for dynamic environments

```bash
sudo apt install ros-jazzy-multirobot-map-merge  # check availability per distro
```

Key parameters for `map_merge` node: `known_init_poses` (True = provide each robot's initial pose, False = feature-based alignment, less reliable), `merging_rate` (Hz), `estimation_confidence` (0.0-1.0). Each robot runs its own SLAM instance publishing to a namespaced `/robot_XX/map` topic; the merge node subscribes to all of them.

---

## 7. DDS discovery at scale

DDS Simple Discovery Protocol (SPDP) uses multicast. With N participants, discovery traffic scales as O(N^2). With 20 robots at 20 nodes each = 400 participants, producing ~160,000 discovery pairs. At 100+ participants, discovery storms can saturate bandwidth for 30+ seconds.

### FastDDS Discovery Server

Reduces discovery from O(N^2) to O(N) by centralizing discovery.

```bash
fastdds discovery -i 0 -l 192.168.1.1 -p 11811   # start server
```

```xml
<!-- fastdds_client_profile.xml -->
<profiles xmlns="http://www.eprosima.com/XMLSchemas/fastRTPS_Profiles">
  <participant profile_name="ds_client" is_default_profile="true">
    <rtps><builtin><discovery_config>
      <discoveryProtocol>CLIENT</discoveryProtocol>
      <discoveryServersList>
        <RemoteServer prefix="44.53.00.5f.45.50.52.4f.53.49.4d.41">
          <metatrafficUnicastLocatorList>
            <locator><udpv4>
              <address>192.168.1.1</address><port>11811</port>
            </udpv4></locator>
          </metatrafficUnicastLocatorList>
        </RemoteServer>
      </discoveryServersList>
    </discovery_config></builtin></rtps>
  </participant>
</profiles>
```

```bash
export RMW_IMPLEMENTATION=rmw_fastrtps_cpp  # Humble, Jazzy
# export RMW_IMPLEMENTATION=rmw_fastdds_cpp  # Kilted, Rolling (renamed)
export FASTRTPS_DEFAULT_PROFILES_FILE=/path/to/fastdds_client_profile.xml
```

### CycloneDDS unicast peer lists

Disable multicast and list peers explicitly. Drawback: must maintain the list manually.

```xml
<CycloneDDS><Domain>
  <General><AllowMulticast>false</AllowMulticast></General>
  <Discovery>
    <Peers>
      <Peer address="192.168.1.10"/>
      <Peer address="192.168.1.11"/>
      <Peer address="192.168.1.12"/>
    </Peers>
    <ParticipantIndex>auto</ParticipantIndex>
  </Discovery>
</Domain></CycloneDDS>
```

```bash
export RMW_IMPLEMENTATION=rmw_cyclonedds_cpp
export CYCLONEDDS_URI=file:///path/to/cyclonedds.xml
```

### Zenoh (best for scale)

Router-based discovery that scales linearly. For WAN, chain routers across sites.

```bash
ros2 run rmw_zenoh_cpp rmw_zenohd          # central router
export RMW_IMPLEMENTATION=rmw_zenoh_cpp     # on each robot
```

Regardless of DDS implementation, stagger robot startup by 1-2 seconds each to reduce discovery storm peaks.

---

## 8. Clock synchronization (NTP/PTP)

Multi-robot systems sharing a TF tree or fusing sensor data REQUIRE synchronized clocks. Without clock sync, TF lookups fail with "extrapolation into the future/past" errors.

### NTP (chrony) -- accuracy ~1-10 ms

```bash
sudo apt install chrony
# /etc/chrony/chrony.conf on server: allow 192.168.1.0/24 ; local stratum 8
# /etc/chrony/chrony.conf on robots: server 192.168.1.100 iburst prefer ; makestep 1.0 3
sudo systemctl restart chrony
chronyc tracking           # "System time" offset should be < 10ms
```

### PTP (IEEE 1588) -- accuracy ~1-100 us

Required for tight cross-machine sensor fusion. Needs hardware timestamping support.

```bash
sudo apt install linuxptp
ethtool -T eth0 | grep -i ptp   # check hardware timestamping support
sudo ptp4l -i eth0 -s -m        # run as PTP slave
sudo phc2sys -s /dev/ptp0 -w -m # sync system clock to PTP hardware clock
```

### Which protocol to use

| Requirement | Protocol | Accuracy |
|---|---|---|
| Nav2 multi-robot (same area) | NTP (chrony) | 1-10 ms |
| Sensor fusion across robots | PTP (linuxptp) | 1-100 us |
| Development (same LAN) | NTP from internet | 10-50 ms |
| Air-gapped network | Local NTP server | 1-10 ms |
| Simulation | use_sim_time=true | Perfect |

---

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| TF tree has disconnected frames across robots | Missing `frame_prefix` on `robot_state_publisher` | Set `frame_prefix` parameter for each robot |
| All robots receive each other's cmd_vel | Topics not namespaced | Use `PushRosNamespace` in launch or remap topics |
| Nav2 costmap shows other robot's obstacles on wrong robot | Shared `/scan` topic without namespace | Namespace all sensor topics per robot |
| Discovery takes 30+ seconds with 50 robots | DDS multicast discovery storm | Use FastDDS Discovery Server, Zenoh, or stagger startup |
| Map merge produces artifacts | Different coordinate origins | Ensure all robots localize against the same map origin |
| Fleet adapter cannot reach robot | Wrong domain ID or namespace | Verify `ROS_DOMAIN_ID` and topic remapping in adapter config |
| Robot ignores task assignment | Wrong namespace in allocator | Use fully qualified names: `/robot_01/navigate_to_pose` |
| Clock drift causes TF errors | No clock sync between hosts | Install chrony or linuxptp; verify with `chronyc tracking` |
| Gazebo spawns robots on top of each other | Initial poses not set per robot | Pass unique `x`, `y`, `yaw` per robot in launch |
| Duplicate TF frames | No `frame_prefix` in robot_state_publisher | Add `frame_prefix: robot_name/` to each instance |
| Fleet manager reports stale poses | Client update frequency too low or network drops | Increase `update_frequency`; add heartbeat timeout monitoring |

### Debugging commands

```bash
ros2 run tf2_tools view_frames                  # TF tree (should show prefixed frames)
ros2 run tf2_ros tf2_echo map robot_01/base_link # verify specific transform
ros2 node list                                   # all discovered nodes
ros2 daemon stop && ros2 daemon start            # reset discovery cache
ros2 topic echo /fleet_states                    # monitor fleet state
```
