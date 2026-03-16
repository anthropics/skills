# Launch System

## Table of contents
1. Python launch API fundamentals
2. Launch arguments and substitutions
3. Conditional logic
4. Event handlers
5. Composing launch files
6. GroupAction for namespacing
7. Launch for ros2_control
8. Large system organization
9. Launch testing integration
10. Common failures and fixes

---

## 1. Python launch API fundamentals

ROS 2 uses Python launch files (`*.launch.py`) as the primary launch mechanism.
XML and YAML launch formats exist but lack the full power of Python conditionals
and event handling. **Always use Python launch files for production systems.**

### Minimal launch file

```python
from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        Node(
            package='my_robot_driver',
            executable='driver_node',
            name='driver',
            namespace='robot',
            output='screen',
            parameters=[{'publish_rate': 100.0}],
            remappings=[
                ('joint_states', '/robot/joint_states'),
            ],
        ),
    ])
```

### Key launch entities

| Entity | Purpose | Example |
|---|---|---|
| `Node` | Launch a ROS 2 node | `Node(package='...', executable='...')` |
| `LifecycleNode` | Launch a lifecycle-managed node | Same as Node but exposes lifecycle events |
| `ComposableNodeContainer` | Launch a component container | Holds composable nodes |
| `ExecuteProcess` | Run any shell command | `ExecuteProcess(cmd=['ros2', 'bag', 'record'])` |
| `IncludeLaunchDescription` | Include another launch file | Compose launch files hierarchically |
| `GroupAction` | Group actions with shared namespace/conditions | Namespace isolation |
| `DeclareLaunchArgument` | Declare a user-facing argument | CLI-configurable parameters |
| `SetEnvironmentVariable` | Set env var for child processes | DDS config, locale |

## 2. Launch arguments and substitutions

### Declaring and using arguments

```python
from launch import LaunchDescription
from launch.actions import DeclareLaunchArgument
from launch.substitutions import LaunchConfiguration, PathJoinSubstitution
from launch_ros.actions import Node
from launch_ros.substitutions import FindPackageShare

def generate_launch_description():
    # Declare arguments (visible with `ros2 launch <pkg> <file> --show-args`)
    use_sim = DeclareLaunchArgument(
        'use_sim_time', default_value='false',
        description='Use simulation clock')

    robot_name = DeclareLaunchArgument(
        'robot_name', default_value='my_robot',
        description='Name prefix for all nodes and topics')

    config_file = DeclareLaunchArgument(
        'config', default_value=PathJoinSubstitution([
            FindPackageShare('my_robot_bringup'), 'config', 'params.yaml'
        ]),
        description='Path to parameter file')

    driver = Node(
        package='my_robot_driver',
        executable='driver_node',
        name=['driver_', LaunchConfiguration('robot_name')],
        namespace=LaunchConfiguration('robot_name'),
        parameters=[
            LaunchConfiguration('config'),
            {'use_sim_time': LaunchConfiguration('use_sim_time')},
        ],
        output='screen',
    )

    return LaunchDescription([use_sim, robot_name, config_file, driver])
```

```bash
# Launch with custom arguments
ros2 launch my_robot_bringup robot.launch.py use_sim_time:=true robot_name:=arm_1
```

### Common substitutions

| Substitution | Purpose | Example |
|---|---|---|
| `LaunchConfiguration('arg')` | Read a launch argument | Dynamic node config |
| `FindPackageShare('pkg')` | Get package share directory | Load config/URDF files |
| `PathJoinSubstitution([...])` | Join path segments | Build file paths |
| `Command(['cmd', 'args'])` | Run a command and use its output | `xacro` processing |
| `EnvironmentVariable('VAR')` | Read an environment variable | Robot-specific config |
| `PythonExpression(['expr'])` | Evaluate Python expression | Complex conditionals |
| `TextSubstitution(text='...')` | Static text | Fixed strings in expressions |

### URDF/xacro processing

```python
from launch.substitutions import Command, PathJoinSubstitution
from launch_ros.substitutions import FindPackageShare

robot_description = Command([
    'xacro ',
    PathJoinSubstitution([
        FindPackageShare('my_robot_description'),
        'urdf', 'robot.urdf.xacro',
    ]),
    ' use_sim:=', LaunchConfiguration('use_sim_time'),
    ' robot_name:=', LaunchConfiguration('robot_name'),
])

robot_state_publisher = Node(
    package='robot_state_publisher',
    executable='robot_state_publisher',
    parameters=[{'robot_description': robot_description}],
)
```

## 3. Conditional logic

### IfCondition / UnlessCondition

```python
from launch.actions import DeclareLaunchArgument
from launch.conditions import IfCondition, UnlessCondition
from launch.substitutions import LaunchConfiguration
from launch_ros.actions import Node

use_rviz_arg = DeclareLaunchArgument('rviz', default_value='true')

rviz_node = Node(
    package='rviz2',
    executable='rviz2',
    arguments=['-d', rviz_config_path],
    condition=IfCondition(LaunchConfiguration('rviz')),
)

headless_logger = Node(
    package='my_robot_monitor',
    executable='logger_node',
    condition=UnlessCondition(LaunchConfiguration('rviz')),
)
```

### PythonExpression for complex conditions

```python
from launch.conditions import IfCondition
from launch.substitutions import PythonExpression

# Only launch when robot_type is 'arm' and simulation is enabled
condition=IfCondition(PythonExpression([
    "'", LaunchConfiguration('robot_type'), "' == 'arm' and '",
    LaunchConfiguration('use_sim_time'), "' == 'true'"
]))
```

## 4. Event handlers

### OnProcessExit — sequenced startup

```python
from launch.actions import RegisterEventHandler, ExecuteProcess
from launch.event_handlers import OnProcessExit
from launch_ros.actions import Node

# Spawn controller after joint_state_broadcaster is loaded
spawn_jsb = Node(
    package='controller_manager',
    executable='spawner',
    arguments=['joint_state_broadcaster'],
)

spawn_arm_controller = Node(
    package='controller_manager',
    executable='spawner',
    arguments=['arm_controller'],
)

delayed_spawn = RegisterEventHandler(
    OnProcessExit(
        target_action=spawn_jsb,
        on_exit=[spawn_arm_controller],
    )
)
```

### OnProcessIO — log monitoring

```python
from launch.event_handlers import OnProcessIO

log_monitor = RegisterEventHandler(
    OnProcessIO(
        target_action=driver_node,
        on_stdout=lambda event: print(f'[DRIVER] {event.text.decode()}'),
    )
)
```

### OnShutdown — cleanup actions

```python
from launch.actions import RegisterEventHandler, LogInfo
from launch.event_handlers import OnShutdown

shutdown_handler = RegisterEventHandler(
    OnShutdown(
        on_shutdown=[LogInfo(msg='System shutting down — saving state...')],
    )
)
```

## 5. Composing launch files

### IncludeLaunchDescription

```python
from launch import LaunchDescription
from launch.actions import IncludeLaunchDescription
from launch.launch_description_sources import PythonLaunchDescriptionSource
from launch.substitutions import PathJoinSubstitution
from launch_ros.substitutions import FindPackageShare

def generate_launch_description():
    driver_launch = IncludeLaunchDescription(
        PythonLaunchDescriptionSource(
            PathJoinSubstitution([
                FindPackageShare('my_robot_driver'),
                'launch', 'driver.launch.py',
            ])
        ),
        launch_arguments={
            'serial_port': '/dev/ttyUSB0',
            'baud_rate': '115200',
        }.items(),
    )

    navigation_launch = IncludeLaunchDescription(
        PythonLaunchDescriptionSource(
            PathJoinSubstitution([
                FindPackageShare('my_robot_navigation'),
                'launch', 'navigation.launch.py',
            ])
        ),
        launch_arguments={
            'use_sim_time': LaunchConfiguration('use_sim_time'),
            'map': LaunchConfiguration('map'),
        }.items(),
    )

    return LaunchDescription([
        DeclareLaunchArgument('use_sim_time', default_value='false'),
        DeclareLaunchArgument('map', default_value=''),
        driver_launch,
        navigation_launch,
    ])
```

### Recommended hierarchy

```
my_robot_bringup/
├── launch/
│   ├── robot.launch.py          # Top-level: includes all subsystem launches
│   ├── simulation.launch.py     # Sim-specific (Gazebo + bridges)
│   └── rviz.launch.py           # Visualization
my_robot_driver/
├── launch/
│   └── driver.launch.py         # Self-contained driver launch
my_robot_navigation/
├── launch/
│   └── navigation.launch.py     # Self-contained Nav2 launch
my_robot_perception/
├── launch/
│   └── perception.launch.py     # Self-contained perception pipeline
```

## 6. GroupAction for namespacing

```python
from launch import LaunchDescription
from launch.actions import GroupAction
from launch_ros.actions import PushRosNamespace, Node

def generate_launch_description():
    robot_1 = GroupAction([
        PushRosNamespace('robot_1'),
        Node(package='my_robot_driver', executable='driver_node', name='driver'),
        Node(package='my_robot_perception', executable='lidar_node', name='lidar'),
    ])

    robot_2 = GroupAction([
        PushRosNamespace('robot_2'),
        Node(package='my_robot_driver', executable='driver_node', name='driver'),
        Node(package='my_robot_perception', executable='lidar_node', name='lidar'),
    ])

    return LaunchDescription([robot_1, robot_2])
```

This creates:
- `/robot_1/driver`, `/robot_1/lidar` with topics under `/robot_1/...`
- `/robot_2/driver`, `/robot_2/lidar` with topics under `/robot_2/...`

## 7. Launch for ros2_control

### Standard ros2_control launch pattern

```python
from launch import LaunchDescription
from launch.actions import RegisterEventHandler, DeclareLaunchArgument
from launch.event_handlers import OnProcessExit
from launch.substitutions import Command, PathJoinSubstitution, LaunchConfiguration
from launch_ros.actions import Node
from launch_ros.substitutions import FindPackageShare

def generate_launch_description():
    robot_description = Command([
        'xacro ',
        PathJoinSubstitution([
            FindPackageShare('my_robot_description'), 'urdf', 'robot.urdf.xacro',
        ]),
    ])

    controller_config = PathJoinSubstitution([
        FindPackageShare('my_robot_control'), 'config', 'controllers.yaml',
    ])

    # Robot State Publisher (publishes URDF to /robot_description)
    rsp = Node(
        package='robot_state_publisher',
        executable='robot_state_publisher',
        parameters=[{'robot_description': robot_description}],
    )

    # Controller Manager
    control_node = Node(
        package='controller_manager',
        executable='ros2_control_node',
        parameters=[
            {'robot_description': robot_description},
            controller_config,
        ],
        output='screen',
    )

    # Spawn broadcasters and controllers in order
    spawn_jsb = Node(
        package='controller_manager',
        executable='spawner',
        arguments=['joint_state_broadcaster',
                   '--controller-manager', '/controller_manager'],
    )

    spawn_controller = Node(
        package='controller_manager',
        executable='spawner',
        arguments=['arm_controller',
                   '--controller-manager', '/controller_manager',
                   '--param-file', controller_config],
    )

    # Ensure joint_state_broadcaster is up before arm_controller
    delayed_controller = RegisterEventHandler(
        OnProcessExit(
            target_action=spawn_jsb,
            on_exit=[spawn_controller],
        )
    )

    return LaunchDescription([
        rsp,
        control_node,
        spawn_jsb,
        delayed_controller,
    ])
```

## 8. Large system organization

### For systems with >50 nodes

**Problem:** A single monolithic launch file becomes unmanageable.

**Solution:** Layered launch architecture:

```
Layer 1 (Subsystem launches):
  driver.launch.py       → hardware driver nodes
  perception.launch.py   → cameras, LiDAR, detection
  navigation.launch.py   → Nav2, localization, mapping
  manipulation.launch.py → MoveIt 2, gripper control

Layer 2 (Robot launch):
  robot.launch.py        → includes all Layer 1 files
                           → passes arguments down

Layer 3 (Deployment launch):
  fleet.launch.py        → includes robot.launch.py N times with namespaces
  simulation.launch.py   → includes robot.launch.py + Gazebo
```

### Launch argument forwarding pattern

```python
# In robot.launch.py — forward all common args to subsystem launches
COMMON_ARGS = ['use_sim_time', 'robot_name', 'namespace']

def forward_args(args_dict):
    """Forward common launch arguments to included launch files."""
    return {k: LaunchConfiguration(k) for k in COMMON_ARGS if k in args_dict}
```

### TimerAction for staggered startup

```python
from launch.actions import TimerAction

# Delay perception startup by 3 seconds (wait for drivers to initialize)
delayed_perception = TimerAction(
    period=3.0,
    actions=[perception_launch],
)
```

## 9. Launch testing integration

### Basic launch test

```python
import unittest
import launch
import launch.actions
import launch_testing
import launch_testing.actions
from launch_ros.actions import Node

def generate_test_description():
    node_under_test = Node(
        package='my_robot_driver',
        executable='driver_node',
        name='driver',
        parameters=[{'use_sim_time': True}],
    )

    return (
        launch.LaunchDescription([
            node_under_test,
            launch_testing.actions.ReadyToTest(),
        ]),
        {'driver': node_under_test},
    )

class TestDriverStartup(unittest.TestCase):
    def test_node_starts(self, proc_info, driver):
        """Verify the driver node starts without crashing."""
        proc_info.assertWaitForStartup(process=driver, timeout=10)

@launch_testing.post_shutdown_test()
class TestDriverShutdown(unittest.TestCase):
    def test_clean_exit(self, proc_info):
        """Verify the node exits cleanly."""
        launch_testing.asserts.assertExitCodes(proc_info)
```

### Running launch tests

```bash
# Via colcon
colcon test --packages-select my_robot_driver

# Directly with launch_testing
ros2 launch launch_testing test/test_driver.launch.py
```

## 10. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| "Package not found" in launch | Package not installed or not sourced | `colcon build`, `source install/setup.bash` |
| Node starts but parameters are default | Parameter file path is wrong (Substitution not resolved) | Use `FindPackageShare` + `PathJoinSubstitution`, verify file exists |
| `xacro` fails during launch | Missing xacro dependency or syntax error | Test with `xacro robot.urdf.xacro` manually first |
| Launch argument not passed to included file | Argument not forwarded in `launch_arguments` | Explicitly pass `launch_arguments={...}.items()` |
| Nodes in wrong namespace | `PushRosNamespace` not wrapping correctly | Use `GroupAction` with `PushRosNamespace` as first element |
| Event handler never fires | Target action reference mismatch | Ensure the `target_action` variable is the same object, not a copy |
| Controller spawner exits with error | Controller manager not ready yet | Use `OnProcessExit` to sequence spawner after control_node startup |
| Launch file not found during `ros2 launch` | Missing `data_files` entry in setup.py (Python pkg) or `install(DIRECTORY launch ...)` in CMake | Add install directive in build config |
