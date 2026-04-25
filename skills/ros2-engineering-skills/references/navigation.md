# Navigation (Nav2)

## Table of contents
1. Nav2 architecture overview
2. SLAM integration
3. Costmap configuration
4. Behavior tree navigator
5. Planner and controller plugins
6. Recovery behaviors
7. Waypoint following
8. Multi-robot navigation
9. Parameter tuning methodology
10. Common failures and fixes

---

## 1. Nav2 architecture overview

```
                    ┌─────────────────┐
                    │   BT Navigator   │ ← Behavior tree orchestrates navigation
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
     ┌──────────────┐ ┌──────────┐ ┌──────────────┐
     │    Planner    │ │Controller│ │  Recovery     │
     │    Server     │ │  Server  │ │  Server       │
     │ (global path) │ │ (cmd_vel)│ │ (stuck help)  │
     └──────┬───────┘ └────┬─────┘ └──────────────┘
            │              │
            ▼              ▼
     ┌─────────────────────────────────┐
     │         Costmap 2D              │
     │  (global + local costmaps)      │
     └────────────┬────────────────────┘
                  │
     ┌────────────▼────────────────────┐
     │   Sensor Data (LiDAR, depth)    │
     │   + TF (map → odom → base)     │
     └─────────────────────────────────┘
```

**Key lifecycle nodes (all managed):**
- `bt_navigator` — orchestrates navigation tasks via behavior trees
- `planner_server` — computes global paths
- `controller_server` — generates velocity commands to follow paths
- `behavior_server` (Jazzy+, renamed from `recoveries_server` in Humble) -- handles stuck situations (spin, back up, wait)
- `smoother_server` — smooths planned paths (optional)
- `waypoint_follower` — executes multi-waypoint missions
- `velocity_smoother` — smooths `cmd_vel` output (optional)

### Minimal Nav2 launch

```python
from launch import LaunchDescription
from launch.actions import IncludeLaunchDescription
from launch.launch_description_sources import PythonLaunchDescriptionSource
from launch.substitutions import PathJoinSubstitution
from launch_ros.substitutions import FindPackageShare

def generate_launch_description():
    nav2_launch = IncludeLaunchDescription(
        PythonLaunchDescriptionSource(
            PathJoinSubstitution([
                FindPackageShare('nav2_bringup'),
                'launch', 'navigation_launch.py',
            ])
        ),
        launch_arguments={
            'use_sim_time': 'true',
            'params_file': PathJoinSubstitution([
                FindPackageShare('my_robot_navigation'),
                'config', 'nav2_params.yaml',
            ]),
        }.items(),
    )
    return LaunchDescription([nav2_launch])
```

## 2. SLAM integration

### slam_toolbox (recommended)

```yaml
# slam_toolbox_params.yaml
slam_toolbox:
  ros__parameters:
    solver_plugin: solver_plugins::CeresSolver
    ceres_linear_solver: SPARSE_NORMAL_CHOLESKY
    ceres_preconditioner: SCHUR_JACOBI

    # Map parameters
    resolution: 0.05               # meters per pixel
    max_laser_range: 20.0           # meters

    # Update thresholds
    minimum_travel_distance: 0.5    # meters before updating map
    minimum_travel_heading: 0.5     # radians before updating map

    # Mode: mapping (online) or localization (use existing map)
    mode: mapping                   # or "localization"

    # Scan matching
    scan_topic: /scan
    use_scan_matching: true
    use_scan_barycenter: true

    # Map save
    map_file_prefix: my_map
    map_start_at_dock: true
```

### Launch with SLAM

```python
Node(
    package='slam_toolbox',
    executable='async_slam_toolbox_node',
    name='slam_toolbox',
    parameters=[slam_params_file, {'use_sim_time': True}],
),
```

### Saving and loading maps

```bash
# Save map during SLAM
ros2 run nav2_map_server map_saver_cli -f ~/maps/my_map

# Serve a saved map for localization
ros2 run nav2_map_server map_server --ros-args \
  -p yaml_filename:=~/maps/my_map.yaml \
  -p use_sim_time:=true
```

### AMCL localization (known maps)

AMCL (Adaptive Monte Carlo Localization) is the standard particle filter localization for navigating in pre-built maps:

```yaml
amcl:
  ros__parameters:
    use_sim_time: true
    alpha1: 0.2   # rotation noise from rotation
    alpha2: 0.2   # rotation noise from translation
    alpha3: 0.2   # translation noise from translation
    alpha4: 0.2   # translation noise from rotation
    base_frame_id: "base_link"
    global_frame_id: "map"
    odom_frame_id: "odom"
    max_particles: 2000
    min_particles: 500
    robot_model_type: "nav2_amcl::DifferentialMotionModel"
    scan_topic: scan
    tf_broadcast: true
    set_initial_pose: true
    initial_pose:
      x: 0.0
      y: 0.0
      yaw: 0.0
```

When to use AMCL vs SLAM:
| Scenario | Use |
|---|---|
| Known, static environment | AMCL with pre-built map |
| Unknown environment | slam_toolbox (online SLAM) |
| Semi-dynamic environment | slam_toolbox in localization mode |
| Outdoor with GPS | robot_localization EKF + NavSat |

## 3. Costmap configuration

### Global vs local costmap

| Property | Global costmap | Local costmap |
|---|---|---|
| Size | Entire map | Rolling window around robot |
| Purpose | Path planning (A* / Dijkstra) | Local obstacle avoidance |
| Update rate | Slow (1–5 Hz) | Fast (5–20 Hz) |
| Typical width | Map size | 3–6 meters |
| Resolution | 0.05 m | 0.05 m |

### Costmap layers configuration

```yaml
global_costmap:
  global_costmap:
    ros__parameters:
      update_frequency: 1.0
      publish_frequency: 1.0
      global_frame: map
      robot_base_frame: base_link
      use_sim_time: true
      robot_radius: 0.22
      resolution: 0.05
      plugins: ["static_layer", "obstacle_layer", "inflation_layer"]

      static_layer:
        plugin: "nav2_costmap_2d::StaticLayer"
        map_subscribe_transient_local: true

      obstacle_layer:
        plugin: "nav2_costmap_2d::ObstacleLayer"
        enabled: true
        observation_sources: scan
        scan:
          topic: /scan
          max_obstacle_height: 2.0
          clearing: true
          marking: true
          data_type: "LaserScan"
          raytrace_max_range: 5.0
          raytrace_min_range: 0.0
          obstacle_max_range: 4.5
          obstacle_min_range: 0.0

      inflation_layer:
        plugin: "nav2_costmap_2d::InflationLayer"
        cost_scaling_factor: 3.0     # Higher = cost drops faster (exponential decay)
        inflation_radius: 0.55       # Must be > robot_radius

# Inflation cost formula (exponential decay):
#   cost(d) = INSCRIBED_INFLATED_OBSTACLE * e^(-cost_scaling_factor * (d - inscribed_radius))
#
# where d = distance from obstacle, inscribed_radius = robot_radius
#
# Key insight: doubling cost_scaling_factor does NOT double the safe zone.
# It makes the cost DROP FASTER, meaning the robot navigates CLOSER to obstacles.
#   cost_scaling_factor=1.0 → gradual falloff, robot stays far from walls
#   cost_scaling_factor=5.0 → steep falloff, robot cuts close to obstacles
#   cost_scaling_factor=10.0 → almost binary (lethal vs free), robot hugs walls
#
# Tune inflation_radius first (sets the maximum inflation range), then
# adjust cost_scaling_factor to control how aggressively cost decays within
# that range.

local_costmap:
  local_costmap:
    ros__parameters:
      update_frequency: 5.0
      publish_frequency: 2.0
      global_frame: odom
      robot_base_frame: base_link
      rolling_window: true
      width: 3
      height: 3
      resolution: 0.05
      plugins: ["voxel_layer", "inflation_layer"]

      voxel_layer:
        plugin: "nav2_costmap_2d::VoxelLayer"
        enabled: true
        observation_sources: scan
        scan:
          topic: /scan
          max_obstacle_height: 2.0
          clearing: true
          marking: true
          data_type: "LaserScan"

      inflation_layer:
        plugin: "nav2_costmap_2d::InflationLayer"
        cost_scaling_factor: 3.0
        inflation_radius: 0.55
```

## 4. Behavior tree navigator

Nav2 uses BehaviorTree.CPP to orchestrate navigation. The default BT handles
planning, following, and recovery.

### Default navigation BT flow

```
NavigateRecovery
├── NavigateWithReplanning
│   ├── ComputePathToPose → Planner Server
│   ├── FollowPath → Controller Server
│   └── (replans on failure or rate timer)
└── RecoveryFallback
    ├── ClearCostmapExceptLastResort
    ├── Spin
    ├── Wait
    └── BackUp
```

### Custom behavior tree

```xml
<!-- my_nav_bt.xml -->
<root main_tree_to_execute="MainTree">
  <BehaviorTree ID="MainTree">
    <RecoveryNode number_of_retries="3" name="NavigateRecovery">
      <PipelineSequence name="NavigateWithReplanning">
        <RateController hz="1.0">
          <ComputePathToPose goal="{goal}" path="{path}" planner_id="GridBased"/>
        </RateController>
        <FollowPath path="{path}" controller_id="FollowPath"/>
      </PipelineSequence>
      <ReactiveFallback name="RecoveryFallback">
        <GoalUpdated/>
        <SequenceStar>
          <ClearEntireCostmap name="ClearGlobalCostmap"
            service_name="global_costmap/clear_entirely_global_costmap"/>
          <ClearEntireCostmap name="ClearLocalCostmap"
            service_name="local_costmap/clear_entirely_local_costmap"/>
          <Spin spin_dist="1.57"/>
          <Wait wait_duration="5"/>
          <BackUp backup_dist="0.30" backup_speed="0.05"/>
        </SequenceStar>
      </ReactiveFallback>
    </RecoveryNode>
  </BehaviorTree>
</root>
```

### Using custom BT in config

```yaml
bt_navigator:
  ros__parameters:
    default_bt_xml_filename: ""  # Uses built-in default
    # Or specify custom:
    # default_bt_xml_filename: /path/to/my_nav_bt.xml
    plugin_lib_names:
      - nav2_compute_path_to_pose_action_bt_node
      - nav2_follow_path_action_bt_node
      - nav2_spin_action_bt_node
      - nav2_wait_action_bt_node
      - nav2_back_up_action_bt_node
      - nav2_clear_costmap_service_bt_node
      - nav2_rate_controller_bt_node
      - nav2_pipeline_sequence_bt_node
      - nav2_recovery_node_bt_node
      - nav2_goal_updated_bt_node
```

## 5. Planner and controller plugins

### Planner plugins

| Plugin | Algorithm | Best for |
|---|---|---|
| `NavfnPlanner` | Dijkstra / A* | Simple environments, guaranteed optimal |
| `SmacPlannerHybrid` | Hybrid-A* | Non-holonomic robots (cars, Ackermann) |
| `SmacPlanner2D` | A* on 2D grid | Holonomic robots, fast planning |
| `SmacPlannerLattice` | State lattice | Complex kinematic constraints |
| `ThetaStarPlanner` | Theta* | Any-angle planning, smoother paths |

```yaml
planner_server:
  ros__parameters:
    planner_plugins: ["GridBased"]
    GridBased:
      plugin: "nav2_navfn_planner/NavfnPlanner"
      tolerance: 0.5
      use_astar: true
      allow_unknown: true
```

### Controller plugins

| Plugin | Method | Best for |
|---|---|---|
| `DWBLocalPlanner` | Dynamic Window | General purpose, differential drive |
| `RegulatedPurePursuitController` | Pure pursuit | Smooth, regulated tracking |
| `MPPIController` | Model Predictive | Complex dynamics, obstacle avoidance |
| `RotationShimController` | Wraps other controllers | Rotate in place before following path |

```yaml
controller_server:
  ros__parameters:
    controller_frequency: 20.0
    controller_plugins: ["FollowPath"]
    FollowPath:
      plugin: "dwb_core::DWBLocalPlanner"
      min_vel_x: 0.0
      min_vel_y: 0.0
      max_vel_x: 0.5
      max_vel_y: 0.0          # 0 for diff-drive
      max_vel_theta: 1.0
      min_speed_xy: 0.0
      max_speed_xy: 0.5
      acc_lim_x: 2.5
      acc_lim_y: 0.0
      acc_lim_theta: 3.2
      decel_lim_x: -2.5
      decel_lim_y: 0.0
      decel_lim_theta: -3.2
```

## 6. Recovery behaviors

```yaml
# Jazzy+: behavior_server (renamed from recoveries_server)
behavior_server:
  ros__parameters:
    behavior_plugins: ["spin", "backup", "wait"]
    spin:
      plugin: "nav2_behaviors/Spin"
    backup:
      plugin: "nav2_behaviors/BackUp"
    wait:
      plugin: "nav2_behaviors/Wait"

# Humble: recoveries_server
recoveries_server:
  ros__parameters:
    recovery_plugins: ["spin", "backup", "wait"]
    spin:
      plugin: "nav2_recoveries/Spin"
    backup:
      plugin: "nav2_recoveries/BackUp"
    wait:
      plugin: "nav2_recoveries/Wait"
```

**Custom recovery sequence:**
1. Clear costmaps (remove phantom obstacles)
2. Wait 5 seconds (let dynamic obstacles pass)
3. Spin 180° (look for alternative paths)
4. Back up 0.3 m (escape tight spaces)
5. Replan

### Dynamic obstacle handling

Nav2's costmap handles static and semi-static obstacles well, but fast-moving
obstacles (humans walking at 1.5 m/s, forklifts) require additional strategies:

| Strategy | When to use | Implementation |
|---|---|---|
| **Higher costmap update rate** | Moderate dynamics (warehouse) | `local_costmap.update_frequency: 10-20` Hz |
| **Collision monitor** | Last-line safety (see below) | Separate node, geometry-based |
| **MPPI controller** | Predictive avoidance | `MPPIController` with obstacle cost critic |
| **Costmap filters** | Known dynamic zones | `KeepoutFilter` for exclusion zones |
| **People tracking** | Dense crowds | External tracker → costmap layer via plugin |

**Limitation:** The standard `ObstacleLayer` uses a clearing/marking model that
assumes obstacles are static between scans. Fast-moving objects can leave "ghost
trails" in the costmap. For populated environments, consider:
1. Reducing `obstacle_max_range` to limit stale markings
2. Using the `VoxelLayer` with 3D clearing
3. Adding a people-tracking costmap layer

### Nav2 Collision Monitor

The collision monitor (Jazzy+) is an independent safety node that monitors sensor
data and **directly overrides `cmd_vel`** — it is NOT just a warning system. When
an obstacle enters the stop polygon, the monitor publishes zero velocity regardless
of what the controller commands. This provides a last-line-of-defense safety layer
independent of the costmap and controller.

```yaml
collision_monitor:
  ros__parameters:
    base_frame_id: "base_link"
    odom_frame_id: "odom"
    transform_tolerance: 0.5
    source_timeout: 2.0
    stop_pub_timeout: 2.0
    polygons: ["PolygonStop", "PolygonSlow"]
    PolygonStop:
      type: "polygon"
      points: [0.4, 0.3, 0.4, -0.3, -0.1, -0.3, -0.1, 0.3]
      action_type: "stop"
      max_points: 3
      visualize: true
    PolygonSlow:
      type: "circle"
      radius: 0.7
      action_type: "slowdown"
      max_points: 3
      slowdown_ratio: 0.5
    observation_sources: ["scan"]
    scan:
      source_timeout: 2.0
      type: "scan"
      topic: "/scan"
```

## 7. Waypoint following

### Sending waypoints programmatically (Python)

```python
from math import sin, cos
from nav2_simple_commander.robot_navigator import BasicNavigator
from geometry_msgs.msg import PoseStamped
import rclpy

def main():
    rclpy.init()
    navigator = BasicNavigator()

    # Wait for Nav2 to be active
    navigator.waitUntilNav2Active()

    # Define waypoints
    waypoints = []
    for (x, y, yaw) in [(1.0, 0.0, 0.0), (2.0, 1.0, 1.57), (0.0, 0.0, 3.14)]:
        pose = PoseStamped()
        pose.header.frame_id = 'map'
        pose.header.stamp = navigator.get_clock().now().to_msg()
        pose.pose.position.x = x
        pose.pose.position.y = y
        pose.pose.orientation.x = 0.0
        pose.pose.orientation.y = 0.0
        pose.pose.orientation.z = sin(yaw / 2)
        pose.pose.orientation.w = cos(yaw / 2)
        waypoints.append(pose)

    navigator.followWaypoints(waypoints)

    while not navigator.isTaskComplete():
        feedback = navigator.getFeedback()
        if feedback:
            print(f'Waypoint {feedback.current_waypoint}/{len(waypoints)}')

    result = navigator.getResult()
    print(f'Navigation result: {result}')
    rclpy.shutdown()
```

### Waypoint follower configuration

```yaml
waypoint_follower:
  ros__parameters:
    loop_rate: 20
    stop_on_failure: false
    waypoint_task_executor_plugin: "wait_at_waypoint"
    wait_at_waypoint:
      plugin: "nav2_waypoint_follower::WaitAtWaypoint"
      enabled: true
      waypoint_pause_duration: 200  # ms to pause at each waypoint
```

## 8. Multi-robot navigation

### Namespace isolation

```python
# Each robot gets its own Nav2 stack in a namespace
for robot_id in ['robot_1', 'robot_2']:
    GroupAction([
        PushRosNamespace(robot_id),
        IncludeLaunchDescription(
            PythonLaunchDescriptionSource(nav2_launch_file),
            launch_arguments={
                'namespace': robot_id,
                'use_namespace': 'true',
                'params_file': nav2_params,
            }.items(),
        ),
    ])
```

### Multi-robot considerations

- Each robot needs its own costmap (sees other robots as obstacles)
- Use `frame_prefix` in robot_state_publisher for unique TF frames
- Localization must publish `map → robot_N/odom` (not shared `odom`)
- Consider a central task allocator for waypoint assignment

### Outdoor navigation with GPS

For outdoor robots, combine GPS with Nav2 using `robot_localization` EKF:

```bash
sudo apt install ros-jazzy-robot-localization ros-jazzy-nav2-waypoint-follower
```

The key is fusing GPS (lat/lon) into the Nav2 coordinate system via `robot_localization`'s `navsat_transform_node`, which converts GPS fixes to odometry in the map frame.

For multi-robot navigation patterns including fleet management and Open-RMF integration, see `references/multi-robot.md`.

## 9. Parameter tuning methodology

### Step-by-step tuning workflow

1. **Costmap first:** Verify sensor data appears correctly in costmaps
   - `ros2 run rviz2 rviz2` — visualize global and local costmaps
   - Adjust `inflation_radius` to match robot footprint + safety margin

2. **Global planner:** Get reasonable paths
   - Start with `NavfnPlanner` (simple, reliable)
   - Tune `tolerance` based on position accuracy needs

3. **Local controller:** Tune velocity tracking
   - Start with conservative velocity limits (50% of max)
   - Increase gradually while monitoring oscillation
   - Watch for overshooting at waypoints

4. **Recovery:** Handle edge cases
   - Test in narrow passages, dead ends, dynamic obstacles
   - Tune spin distance and backup distance for your robot

### Goal tolerance and oscillation

A common production issue: the robot oscillates near the goal. This happens when
`xy_goal_tolerance` is too tight relative to the controller frequency and robot
inertia. The robot overshoots, replans, overshoots in the opposite direction, and
loops.

**Rules:**
- `xy_goal_tolerance` should be ≥ `max_vel_x / controller_frequency` (minimum
  stopping distance at max speed). E.g., 0.5 m/s at 20 Hz → tolerance ≥ 0.025 m.
- If using `RegulatedPurePursuitController`, its `regulated_linear_scaling_min_speed`
  reduces speed near goals, allowing tighter tolerances.
- Set `yaw_goal_tolerance` generously (0.1–0.3 rad) unless orientation matters.
- If the robot stops, rotates, overshoots, repeats — increase tolerances or reduce
  `max_vel_theta`.

### Key parameters to tune first

| Parameter | Effect | Start value |
|---|---|---|
| `robot_radius` | Collision boundary | Actual radius + 0.05 m |
| `inflation_radius` | Safe distance | `robot_radius` + 0.15 m |
| `max_vel_x` | Maximum speed | 50% of hardware max |
| `controller_frequency` | Path tracking update rate | 20 Hz |
| `planner_frequency` | Replanning rate | 1 Hz |

## 10. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Robot doesn't move after sending goal | Nav2 nodes not in Active state | Check lifecycle states with `ros2 lifecycle list`; use `nav2_lifecycle_manager` |
| "No valid pose received" | TF chain broken (map → odom → base_link) | Verify transforms with `ros2 run tf2_tools view_frames` |
| Robot oscillates near goal | Controller gains too aggressive | Reduce `max_vel_theta`, increase `xy_goal_tolerance` |
| Robot gets stuck at narrow passage | Inflation radius too large for gap | Reduce `inflation_radius` or use `cost_scaling_factor` to soften falloff |
| "Planning failed" | Start or goal pose inside an obstacle in costmap | Clear costmaps, check sensor data, adjust obstacle layer params |
| Costmap shows phantom obstacles | Stale sensor data or wrong TF | Check sensor topic rate, verify TF timestamps |
| Robot takes very long paths | Costmap inflation too high | Reduce `cost_scaling_factor` (higher value = cost drops faster) |
| Recovery spin doesn't complete | Insufficient space to rotate | Reduce `spin_dist`, or add `BackUp` before `Spin` in BT |
| Robot oscillates at goal | Goal tolerance too tight for speed/inertia | Increase `xy_goal_tolerance`, reduce `max_vel_theta` near goal |
| Ghost obstacles in costmap | Fast-moving people/objects leave stale marks | Reduce `obstacle_max_range`, increase `update_frequency`, use VoxelLayer |
| Collision monitor stops robot unexpectedly | Stop polygon too large for robot | Shrink `PolygonStop` points to match actual footprint + small margin |
