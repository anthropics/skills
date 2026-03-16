---
name: ros2-engineering-skills
description: >
  Comprehensive ROS 2 engineering guide covering workspace setup, node architecture,
  communication patterns (topics/services/actions with QoS), lifecycle and component nodes,
  launch composition, tf2/URDF, ros2_control hardware interfaces, real-time constraints,
  Nav2, MoveIt 2, perception pipelines, testing, debugging, deployment, and ROS 1 migration.
  Trigger whenever the user works on ROS 2 code, packages, launch files, URDF/xacro,
  DDS configuration, ros2_control, Nav2, MoveIt 2, or any robotics middleware task
  involving rclcpp, rclpy, colcon, ament, rosbag2, ros2 CLI tools, or Gazebo/Isaac Sim
  integration. Also trigger for ROS 1 to ROS 2 migration, cross-compilation,
  Docker-based ROS 2 workflows, and CI/CD for robotics.
---

# ROS 2 Engineering Skills

A progressive-disclosure skill for ROS 2 development — from first workspace to
production fleet deployment. Each section below gives you the essential decision
framework; detailed patterns, code templates, and anti-patterns live in the
`references/` directory. Read the relevant reference file before writing code.

## How to use this skill

1. Identify what the user is building (see Decision Router below).
2. Read the matching `references/*.md` file for detailed guidance.
3. Apply the Core Engineering Principles in every piece of code you generate.
4. When multiple domains intersect (e.g. Nav2 + ros2_control), read both files.

## Decision router

| User is doing...                                  | Read                              |
|---------------------------------------------------|-----------------------------------|
| Creating a workspace, package, or build config    | `references/workspace-build.md`   |
| Writing nodes, executors, callback groups         | `references/nodes-executors.md`   |
| Topics, services, actions, custom interfaces, QoS | `references/communication.md`     |
| Lifecycle nodes, component loading, composition   | `references/lifecycle-components.md` |
| Launch files, conditional logic, event handlers   | `references/launch-system.md`     |
| tf2, URDF, xacro, robot_state_publisher           | `references/tf2-urdf.md`         |
| ros2_control, hardware interfaces, controllers    | `references/hardware-interface.md` |
| Real-time constraints, PREEMPT_RT, memory, jitter | `references/realtime.md`         |
| Nav2, SLAM, costmaps, behavior trees              | `references/navigation.md`       |
| MoveIt 2, planning scene, grasp pipelines         | `references/manipulation.md`     |
| Camera, LiDAR, PCL, cv_bridge, depth processing   | `references/perception.md`       |
| Unit tests, integration tests, launch_testing, CI | `references/testing.md`          |
| ros2 doctor, tracing, profiling, rosbag2          | `references/debugging.md`        |
| Docker, cross-compile, fleet deployment, OTA      | `references/deployment.md`       |
| Message types, units, covariance, frame conventions | `references/message-types.md`    |
| ROS 1 migration, ros1_bridge, hybrid operation    | `references/migration-ros1.md`   |

When a task spans multiple domains, read all relevant files and reconcile
conflicting recommendations by favoring safety, then determinism, then simplicity.

## Core engineering principles

These apply to every ROS 2 artifact you produce, regardless of domain.

### 1. Distro awareness

Always ask which ROS 2 distribution the user targets. Key differences:

| Feature                   | Foxy (LTS, **EOL**) | Humble (LTS)       | Jazzy (LTS)        | Rolling            |
|---------------------------|----------------------|--------------------|--------------------|--------------------|
| EOL                       | Jun 2023 (**ended**) | May 2027           | May 2029           | Rolling            |
| Ubuntu                    | 20.04               | 22.04              | 24.04              | Latest             |
| Default DDS               | Fast DDS             | CycloneDDS         | CycloneDDS         | CycloneDDS         |
| Default build type        | ament_cmake          | ament_cmake        | ament_cmake        | ament_cmake        |
| Type description support  | No                   | No                 | Yes                | Yes                |
| Service introspection     | No                   | No                 | Yes                | Yes                |
| ros2_control interface    | N/A (separate)       | 2.x                | 4.x                | Latest             |

When the user does not specify, default to the latest LTS (Jazzy).
Pin the exact distro in Dockerfile, CI, and documentation so builds are reproducible.

### 2. C++ vs Python decision

Choose the language based on the node's role, not personal preference.

**Use rclcpp (C++) when:**
- The node sits in a control loop running ≥100 Hz
- Deterministic memory allocation matters (real-time path)
- The node is a hardware driver or controller plugin
- Intra-process zero-copy communication is required

**Use rclpy (Python) when:**
- The node is orchestration, monitoring, or parameter management
- Rapid prototyping with frequent iteration
- Heavy use of ML frameworks (PyTorch, TensorFlow) that are Python-native
- The node does not sit in a latency-critical path

**Mixed stacks are normal.** A typical robot has C++ drivers/controllers and Python
orchestration/monitoring. Note: `component_container` (composition) only loads
C++ components via pluginlib. Python nodes run as separate processes, but can
share a launch file and communicate via zero-overhead intra-host DDS.

### 3. Package structure conventions

Every package should follow this layout. Consistency across a workspace reduces
onboarding time and makes CI scripts portable.

```
my_package/
├── CMakeLists.txt          # or setup.py for pure Python
├── package.xml             # format 3, with <depend> tags
├── config/
│   └── params.yaml         # default parameters
├── launch/
│   └── bringup.launch.py   # Python launch file
├── include/my_package/     # C++ public headers (if library)
├── src/                    # C++ source files
├── my_package/             # Python modules (if ament_python or mixed)
├── test/                   # gtest, pytest, launch_testing
├── urdf/                   # URDF/xacro (if applicable)
├── msg/ srv/ action/       # custom interfaces (dedicated _interfaces package preferred)
└── README.md
```

Separate interface definitions into a `*_interfaces` package so downstream
packages can depend on interfaces without pulling in implementation.

### 4. Parameter discipline

- Declare every parameter with a type, description, range, and default
  in the node constructor — never use undeclared parameters.
- Use `ParameterDescriptor` with `FloatingPointRange` or `IntegerRange`
  for numeric bounds. The parameter server rejects out-of-range values at set time.
- Group related parameters under a namespace prefix:
  `controller.kp`, `controller.ki`, `controller.kd`.
- Load defaults from a `config/params.yaml`; allow launch-time overrides.
- For dynamic reconfiguration, register a `set_parameters_callback` and
  validate new values atomically before accepting.

### 5. Error handling philosophy

- Nodes must not silently swallow errors. Log at the appropriate severity,
  then take a safe action (stop motion, request help, transition to error state).
- Prefer lifecycle node error transitions over ad-hoc boolean flags.
- When calling a service, always handle the "service not available" and
  "future timed out" cases explicitly.
- For hardware drivers, distinguish transient errors (retry with backoff)
  from fatal errors (transition to `FINALIZED` and alert the operator).

### 6. Quality of Service defaults

Start from these profiles and adjust per use case:

| Use case              | Reliability   | Durability       | History | Depth | Deadline    |
|-----------------------|---------------|------------------|---------|-------|-------------|
| Sensor stream         | BEST_EFFORT   | VOLATILE         | KEEP_LAST | 5   | —           |
| Command velocity      | RELIABLE      | VOLATILE         | KEEP_LAST | 1   | 100 ms      |
| Map (latched)         | RELIABLE      | TRANSIENT_LOCAL  | KEEP_LAST | 1   | —           |
| Diagnostics           | RELIABLE      | VOLATILE         | KEEP_LAST | 10  | —           |
| Parameter events      | RELIABLE      | VOLATILE         | KEEP_LAST | 1000| —           |
| Action feedback       | RELIABLE      | VOLATILE         | KEEP_LAST | 1   | —           |

QoS mismatches are the #1 cause of "I published but nobody receives."
Always check compatibility with `ros2 topic info -v` when debugging.

### 7. Naming conventions

| Entity      | Convention                  | Example                        |
|-------------|-----------------------------|--------------------------------|
| Package     | `snake_case`                | `arm_controller`               |
| Node        | `snake_case`                | `joint_state_broadcaster`      |
| Topic       | `/snake_case` with ns       | `/arm/joint_states`            |
| Service     | `/snake_case`               | `/arm/set_mode`                |
| Action      | `/snake_case`               | `/arm/follow_joint_trajectory` |
| Parameter   | `snake_case` with dot ns    | `controller.publish_rate`      |
| Frame       | `snake_case`                | `base_link`, `camera_optical`  |
| Interface   | `PascalCase.msg/srv/action` | `JointState.msg`               |

### 8. Thread safety and callbacks

- A `MutuallyExclusiveCallbackGroup` serializes its callbacks — safe for
  shared state without locks, but limits throughput.
- A `ReentrantCallbackGroup` allows parallel execution — you must protect
  shared state with `std::mutex` (C++) or `threading.Lock` (Python).
- Never do blocking work (file I/O, long computation, `sleep`) inside a
  timer or subscription callback on the default executor. Offload to a
  dedicated thread or use a `MultiThreadedExecutor` with a reentrant group.
- In rclcpp, prefer `std::shared_ptr<const MessageT>` in subscription
  callbacks to avoid unnecessary copies and enable zero-copy intra-process.

### 9. Lifecycle-first design

Default to lifecycle (managed) nodes for anything that owns resources:
hardware drivers, sensor pipelines, planners, controllers.

```
                 ┌──────────────┐
  create() ──►  │  Unconfigured │
                 └──────┬───────┘
            on_configure │
                 ┌──────▼───────┐
                 │   Inactive    │
                 └──────┬───────┘
            on_activate  │
                 ┌──────▼───────┐
                 │    Active     │
                 └──────┬───────┘
           on_deactivate │
                 ┌──────▼───────┐
                 │   Inactive    │
                 └──────┬───────┘
            on_cleanup   │
                 ┌──────▼───────┐
                 │  Unconfigured │
                 └──────┬───────┘
           on_shutdown   │
                 ┌──────▼───────┐
                 │   Finalized   │
                 └───────────────┘
```

This gives the system manager (launch file, orchestrator, or operator) explicit
control over when resources are allocated, when the node starts processing,
and how it shuts down. It also makes error recovery predictable.

### 10. Build and CI hygiene

- Use `colcon build --cmake-args -DCMAKE_BUILD_TYPE=RelWithDebInfo` for
  development; `Release` for deployment.
- Enable `-Wall -Wextra -Wpedantic` and treat warnings as errors in CI.
- Run `colcon test` with `--event-handlers console_cohesion+` so test
  output groups by package.
- Pin rosdep keys in `rosdep.yaml` for reproducible dependency resolution.
- Cache `/opt/ros/`, `.ccache/`, and `build/`/`install/` in CI to cut build
  times by 60–80%.

## Common anti-patterns

| Anti-pattern | Why it hurts | Fix |
|---|---|---|
| Global variables for node state | Breaks composition, untestable | Store state as class members |
| `spin()` in `main()` for multi-node processes | Starves other nodes | Use `MultiThreadedExecutor` or component composition |
| Hardcoded topic names | Breaks reuse across robots | Use relative names + namespace remapping |
| `KEEP_ALL` history with no bound | Memory grows unbounded on slow subscribers | Use `KEEP_LAST` with explicit depth |
| Using `time.sleep()` / `std::this_thread::sleep_for` | Blocks the executor thread | Use `create_wall_timer` or a dedicated thread |
| Monolithic launch file for everything | Unmanageable past 10 nodes | Compose launch files with `IncludeLaunchDescription` |
| Skipping `package.xml` dependencies | Builds locally, breaks CI and Docker | Declare every dependency explicitly |
| Publishing in constructor | Subscribers may not be ready, messages lost | Publish in `on_activate` or after a short timer |
| Ignoring QoS compatibility | Silent communication failure | Match publisher/subscriber QoS or check with `ros2 topic info -v` |
| Creating timers/subs in callbacks | Resource leak, unpredictable behavior | Create all entities in constructor or `on_configure` |
| Synchronous service call in callback | Deadlocks the executor thread | Use `async_send_request` with a callback or dedicated thread |

## Distro-specific migration notes

When upgrading between distributions, check these breaking changes first:

**Foxy → Humble:**
- Complete API overhaul. Foxy packages require significant rework.
- `ros2_control` was not bundled in Foxy — must be built separately.
- Lifecycle node API stabilized in Humble.
- Action server/client API changed significantly.

**Humble → Jazzy:**
- `ros2_control` API changed from 2.x to 4.x — `export_state_interfaces()` and
  `export_command_interfaces()` are now auto-generated by the framework. Manual
  overrides use `on_export_state_interfaces()`. See `references/hardware-interface.md`.
- Handle `get_value()` deprecated → use `get_optional<T>()` on `LoanedStateInterface` /
  `LoanedCommandInterface` (controller side). Hardware interfaces use `set_state()` /
  `get_state()` / `set_command()` / `get_command()` helpers with fully qualified names.
- All joints in `<ros2_control>` tag must exist in the URDF.
- Controller parameter loading changed — use `--param-file` with spawner.
- Default middleware changed internal config paths. Regenerate DDS profiles.
- `nav2_params.yaml` schema changes in several plugins. Validate with Nav2's
  migration guide.
- `launch_ros` actions have new parameter handling — test launch files explicitly.
- `ament_target_dependencies()` still works but is deprecated starting from Kilted
  (non-LTS, May 2025). Prefer `target_link_libraries()` with modern CMake targets
  for forward compatibility.

**ROS 1 → ROS 2:**
- See `references/migration-ros1.md` for a step-by-step strategy.

## Quick reference — ros2 CLI

```bash
# Workspace
colcon build --symlink-install --packages-select my_pkg
colcon test --packages-select my_pkg
source install/setup.bash

# Introspection
ros2 node list
ros2 topic list -t
ros2 topic info /topic_name -v          # shows QoS details
ros2 topic hz /topic_name
ros2 topic bw /topic_name
ros2 service list -t
ros2 action list -t
ros2 param list /node_name
ros2 param describe /node_name param
ros2 interface show std_msgs/msg/String

# Debugging
ros2 doctor --report
ros2 run tf2_tools view_frames
ros2 bag record -a -o my_bag
ros2 bag info my_bag
ros2 bag play my_bag --clock

# Lifecycle
ros2 lifecycle list /node_name
ros2 lifecycle set /node_name configure
ros2 lifecycle set /node_name activate
```
