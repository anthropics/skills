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
- `recoveries_server` — handles stuck situations (spin, back up, wait)
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
        cost_scaling_factor: 3.0     # Higher = cost drops faster with distance
        inflation_radius: 0.55       # Must be > robot_radius

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
