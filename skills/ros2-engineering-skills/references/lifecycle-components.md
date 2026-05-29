# Lifecycle Nodes and Component Composition

## Table of contents
1. Lifecycle node state machine
2. Implementing lifecycle transitions (rclcpp)
3. Implementing lifecycle transitions (rclpy)
4. Component node registration
5. Launch-time vs runtime composition
6. Container types and selection
7. Lifecycle orchestration from launch files
8. Composition with intra-process communication
9. System-level lifecycle management
10. Common failures and fixes

---

## 1. Lifecycle node state machine

Lifecycle (managed) nodes follow the ROS 2 managed node state machine defined
in the [Managed Nodes design article](https://design.ros2.org/articles/node_lifecycle.html). Every node that owns
resources (hardware drivers, sensor pipelines, planners, controllers) should
be a lifecycle node.

```
                     ┌───────────────┐
      create() ────► │  Unconfigured  │ ◄──── on_cleanup()
                     └───────┬───────┘
                 on_configure │
                     ┌───────▼───────┐
                     │    Inactive    │ ◄──── on_deactivate()
                     └───────┬───────┘
                on_activate  │
                     ┌───────▼───────┐
                     │     Active     │
                     └───────┬───────┘
                             │
              on_shutdown can be called from Unconfigured, Inactive, or Active
                     ┌───────▼───────┐
                     │   Finalized    │
                     └───────────────┘

              on_error is triggered on any transition failure:
                     ┌───────────────┐
              ────►  │  ErrorProcessing│ ──► Unconfigured (if recovery succeeds)
                     └───────────────┘  ──► Finalized (if recovery fails)
```

**State semantics:**

| State | What the node does | Resources |
|---|---|---|
| Unconfigured | Nothing — waiting for configuration | None allocated |
| Inactive | Configured but not processing | Allocated but not active |
| Active | Fully operational, processing data | Allocated and active |
| Finalized | Terminated, cannot be restarted | Released |

**Why lifecycle matters:**
- Deterministic startup ordering (configure sensors before controllers)
- Clean error recovery (deactivate → cleanup → reconfigure)
- Resource management without shutdown/restart
- Fleet orchestration (activate/deactivate nodes across robots)

## 2. Implementing lifecycle transitions (rclcpp)

```cpp
#include <rclcpp/rclcpp.hpp>
#include <rclcpp_lifecycle/lifecycle_node.hpp>
#include <lifecycle_msgs/msg/state.hpp>
#include <sensor_msgs/msg/laser_scan.hpp>

namespace my_robot_perception
{

class LidarProcessor : public rclcpp_lifecycle::LifecycleNode
{
public:
  explicit LidarProcessor(const rclcpp::NodeOptions & options = rclcpp::NodeOptions())
  : LifecycleNode("lidar_processor", options)
  {
    // Declare parameters in constructor — always available regardless of state
    declare_parameter("min_range", 0.1);
    declare_parameter("max_range", 30.0);
    declare_parameter("filter_window", 5);
  }

  // on_configure: allocate resources, create publishers/subscribers (inactive)
  CallbackReturn on_configure(const rclcpp_lifecycle::State & /*previous_state*/) override
  {
    RCLCPP_INFO(get_logger(), "Configuring...");

    min_range_ = get_parameter("min_range").as_double();
    max_range_ = get_parameter("max_range").as_double();

    // Create lifecycle publisher — only publishes when node is ACTIVE
    scan_pub_ = create_publisher<sensor_msgs::msg::LaserScan>(
      "filtered_scan", rclcpp::SensorDataQoS());

    // Create subscription — callbacks arrive but should check state
    scan_sub_ = create_subscription<sensor_msgs::msg::LaserScan>(
      "raw_scan", rclcpp::SensorDataQoS(),
      std::bind(&LidarProcessor::scan_callback, this, std::placeholders::_1));

    // Allocate buffers
    filter_buffer_.reserve(get_parameter("filter_window").as_int());

    return CallbackReturn::SUCCESS;
  }

  // on_activate: start processing, enable outputs
  CallbackReturn on_activate(const rclcpp_lifecycle::State & /*previous_state*/) override
  {
    RCLCPP_INFO(get_logger(), "Activating...");
    // LifecyclePublisher automatically enables on activate
    // Any additional activation logic (e.g., hardware enable) goes here
    return CallbackReturn::SUCCESS;
  }

  // on_deactivate: stop processing, disable outputs
  CallbackReturn on_deactivate(const rclcpp_lifecycle::State & /*previous_state*/) override
  {
    RCLCPP_INFO(get_logger(), "Deactivating...");
    // LifecyclePublisher automatically disables on deactivate
    // Clear transient state
    filter_buffer_.clear();
    return CallbackReturn::SUCCESS;
  }

  // on_cleanup: release resources, return to Unconfigured
  CallbackReturn on_cleanup(const rclcpp_lifecycle::State & /*previous_state*/) override
  {
    RCLCPP_INFO(get_logger(), "Cleaning up...");
    scan_pub_.reset();
    scan_sub_.reset();
    filter_buffer_.clear();
    return CallbackReturn::SUCCESS;
  }

  // on_shutdown: called during shutdown from any state
  CallbackReturn on_shutdown(const rclcpp_lifecycle::State & previous_state) override
  {
    RCLCPP_INFO(get_logger(), "Shutting down from state %s", previous_state.label().c_str());
    // Release any remaining resources
    scan_pub_.reset();
    scan_sub_.reset();
    return CallbackReturn::SUCCESS;
  }

  // on_error: called when a transition fails — attempt recovery
  CallbackReturn on_error(const rclcpp_lifecycle::State & previous_state) override
  {
    RCLCPP_ERROR(get_logger(), "Error from state %s", previous_state.label().c_str());
    // Return SUCCESS to transition to Unconfigured (recovery)
    // Return FAILURE to transition to Finalized (unrecoverable)
    return CallbackReturn::SUCCESS;
  }

private:
  void scan_callback(const sensor_msgs::msg::LaserScan::ConstSharedPtr msg)
  {
    // Guard: only process when active
    if (get_current_state().id() !=
        lifecycle_msgs::msg::State::PRIMARY_STATE_ACTIVE)
    {
      return;
    }

    auto filtered = std::make_shared<sensor_msgs::msg::LaserScan>(*msg);
    for (auto & range : filtered->ranges) {
      if (range < min_range_ || range > max_range_) {
        range = std::numeric_limits<float>::quiet_NaN();
      }
    }
    scan_pub_->publish(*filtered);
  }

  rclcpp_lifecycle::LifecyclePublisher<sensor_msgs::msg::LaserScan>::SharedPtr scan_pub_;
  rclcpp::Subscription<sensor_msgs::msg::LaserScan>::SharedPtr scan_sub_;
  std::vector<float> filter_buffer_;
  double min_range_ = 0.1;
  double max_range_ = 30.0;
};

}  // namespace my_robot_perception

// Register as composable node
#include <rclcpp_components/register_node_macro.hpp>
RCLCPP_COMPONENTS_REGISTER_NODE(my_robot_perception::LidarProcessor)
```

### Key lifecycle publisher behavior

`LifecyclePublisher` is a special publisher that only delivers messages when
the node is in the `Active` state. Messages published in other states are
silently dropped. This prevents accidental output during configuration or
after deactivation.

```cpp
// This publisher only works when the node is Active
auto pub = create_publisher<Msg>("topic", qos);  // LifecyclePublisher

// Note: In a lifecycle node, ALL publishers from create_publisher() are
// LifecyclePublishers that are silenced outside Active state.
// For always-active publishing (diagnostics, heartbeats), use a separate
// rclcpp::Node dedicated to diagnostics running in the same process.
```

## 3. Implementing lifecycle transitions (rclpy)

```python
import rclpy
from rclpy.lifecycle import LifecycleNode, State, TransitionCallbackReturn
from sensor_msgs.msg import LaserScan
from rclpy.qos import QoSProfile, ReliabilityPolicy


class LidarProcessor(LifecycleNode):
    def __init__(self, **kwargs):
        super().__init__('lidar_processor', **kwargs)
        self.declare_parameter('min_range', 0.1)
        self.declare_parameter('max_range', 30.0)
        self._scan_pub = None
        self._scan_sub = None

    def on_configure(self, state: State) -> TransitionCallbackReturn:
        self.get_logger().info('Configuring...')
        self._min_range = self.get_parameter('min_range').value
        self._max_range = self.get_parameter('max_range').value

        qos = QoSProfile(depth=5, reliability=ReliabilityPolicy.BEST_EFFORT)
        self._scan_pub = self.create_lifecycle_publisher(LaserScan, 'filtered_scan', qos)
        self._scan_sub = self.create_subscription(
            LaserScan, 'raw_scan', self._scan_callback, qos)

        return TransitionCallbackReturn.SUCCESS

    def on_activate(self, state: State) -> TransitionCallbackReturn:
        self.get_logger().info('Activating...')
        return super().on_activate(state)

    def on_deactivate(self, state: State) -> TransitionCallbackReturn:
        self.get_logger().info('Deactivating...')
        return super().on_deactivate(state)

    def on_cleanup(self, state: State) -> TransitionCallbackReturn:
        self.get_logger().info('Cleaning up...')
        self.destroy_publisher(self._scan_pub)
        self.destroy_subscription(self._scan_sub)
        self._scan_pub = None
        self._scan_sub = None
        return TransitionCallbackReturn.SUCCESS

    def on_shutdown(self, state: State) -> TransitionCallbackReturn:
        self.get_logger().info(f'Shutting down from {state.label}')
        if self._scan_pub:
            self.destroy_publisher(self._scan_pub)
        if self._scan_sub:
            self.destroy_subscription(self._scan_sub)
        return TransitionCallbackReturn.SUCCESS

    def _scan_callback(self, msg: LaserScan):
        if self._scan_pub is None or not self._scan_pub.is_activated:
            return
        filtered = LaserScan()
        filtered.header = msg.header
        filtered.angle_min = msg.angle_min
        filtered.angle_max = msg.angle_max
        filtered.angle_increment = msg.angle_increment
        filtered.time_increment = msg.time_increment
        filtered.scan_time = msg.scan_time
        filtered.range_min = msg.range_min
        filtered.range_max = msg.range_max
        filtered.ranges = [
            r if self._min_range <= r <= self._max_range else float('nan')
            for r in msg.ranges
        ]
        self._scan_pub.publish(filtered)


def main(args=None):
    rclpy.init(args=args)
    node = LidarProcessor()
    try:
        rclpy.spin(node)
    except KeyboardInterrupt:
        pass
    finally:
        node.destroy_node()
        rclpy.shutdown()
```

## 4. Component node registration

Components are C++ nodes that can be loaded into a shared-memory container
process at launch or runtime, enabling zero-copy intra-process communication.

**Note:** Python nodes cannot be loaded as components via pluginlib. They must run as
separate processes. Use launch files to colocate Python and C++ nodes.

### CMakeLists.txt registration

```cmake
find_package(rclcpp_components REQUIRED)

# Build component as a shared library
add_library(lidar_processor_component SHARED
  src/lidar_processor.cpp
)
target_link_libraries(lidar_processor_component ${PROJECT_NAME}_lib)
ament_target_dependencies(lidar_processor_component
  rclcpp rclcpp_lifecycle rclcpp_components sensor_msgs)

# Register the component — this creates a .so that component_container can dlopen
rclcpp_components_register_nodes(lidar_processor_component
  "my_robot_perception::LidarProcessor")

install(TARGETS lidar_processor_component
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
)
```

### Constructor requirements

Components must accept `rclcpp::NodeOptions` as the sole constructor argument:

```cpp
explicit LidarProcessor(const rclcpp::NodeOptions & options = rclcpp::NodeOptions())
: LifecycleNode("lidar_processor", options)  // Node name hardcoded or from options
```

The container overrides the node name via `NodeOptions` at load time.

## 5. Launch-time vs runtime composition

### Launch-time composition (recommended for production)

```python
from launch import LaunchDescription
from launch_ros.actions import ComposableNodeContainer, LoadComposableNodes
from launch_ros.descriptions import ComposableNode

def generate_launch_description():
    container = ComposableNodeContainer(
        name='perception_container',
        namespace='',
        package='rclcpp_components',
        executable='component_container_mt',
        composable_node_descriptions=[
            ComposableNode(
                package='my_robot_perception',
                plugin='my_robot_perception::LidarProcessor',
                name='lidar_processor',
                parameters=[{
                    'min_range': 0.1,
                    'max_range': 25.0,
                }],
                remappings=[
                    ('raw_scan', '/lidar/scan'),
                    ('filtered_scan', '/lidar/filtered'),
                ],
                extra_arguments=[{'use_intra_process_comms': True}],
            ),
            ComposableNode(
                package='my_robot_perception',
                plugin='my_robot_perception::ObstacleDetector',
                name='obstacle_detector',
                extra_arguments=[{'use_intra_process_comms': True}],
            ),
        ],
        output='screen',
    )
    return LaunchDescription([container])
```

### Runtime composition (for dynamic systems)

```bash
# Start an empty container
ros2 run rclcpp_components component_container_mt --ros-args -r __node:=my_container

# Load a component
ros2 component load /my_container my_robot_perception \
  my_robot_perception::LidarProcessor \
  --node-name lidar_processor \
  --param min_range:=0.1

# List loaded components
ros2 component list /my_container

# Unload a component by UID
ros2 component unload /my_container 1
```

**When to use runtime composition:**
- Hot-swapping perception modules during operation
- Debugging (load one component at a time)
- Systems where components join/leave dynamically (e.g., multi-robot)

## 6. Container types and selection

| Container executable | Threading | Use case |
|---|---|---|
| `component_container` | Single-threaded executor | Simple pipelines, no concurrency needed |
| `component_container_mt` | Multi-threaded executor | Components with slow callbacks or independent data paths |
| `component_container_isolated` | Per-component executor | Maximum isolation, each component has its own executor thread(s) |

**Selection guide:**
- Default to `component_container_mt` — most flexible
- Use `component_container_isolated` when one component's slow callback
  must not block others (e.g., ML inference alongside control)
- Use `component_container` only for trivial pipelines with lightweight callbacks

### `component_container_isolated` launch example

```python
container = ComposableNodeContainer(
    name='isolated_container',
    namespace='',
    package='rclcpp_components',
    executable='component_container_isolated',
    # Each component gets its own SingleThreadedExecutor
    composable_node_descriptions=[
        ComposableNode(
            package='my_robot_perception',
            plugin='my_robot_perception::LidarProcessor',
            name='lidar_processor',
            extra_arguments=[{'use_intra_process_comms': True}],
        ),
        ComposableNode(
            package='my_robot_perception',
            plugin='my_robot_perception::MLInference',
            name='ml_inference',
            extra_arguments=[{'use_intra_process_comms': True}],
        ),
    ],
    output='screen',
)
```

## 7. Lifecycle orchestration from launch files

### Using lifecycle node manager events

```python
from launch import LaunchDescription
from launch.actions import EmitEvent, RegisterEventHandler
from launch.event_handlers import OnProcessStart
from launch_ros.actions import LifecycleNode
from launch_ros.events.lifecycle import ChangeState
import lifecycle_msgs.msg

def generate_launch_description():
    lidar_node = LifecycleNode(
        package='my_robot_perception',
        executable='lidar_processor_node',
        name='lidar_processor',
        namespace='',
        output='screen',
    )

    # Automatically configure when the process starts
    configure_event = RegisterEventHandler(
        OnProcessStart(
            target_action=lidar_node,
            on_start=[
                EmitEvent(event=ChangeState(
                    lifecycle_node_matcher=lambda node: True,
                    transition_id=lifecycle_msgs.msg.Transition.TRANSITION_CONFIGURE,
                )),
            ],
        )
    )

    return LaunchDescription([lidar_node, configure_event])
```

### Ordered startup with dependencies

```python
from launch.actions import RegisterEventHandler, EmitEvent
from launch.event_handlers import OnProcessStart
from launch_ros.events.lifecycle import ChangeState
from launch_ros.event_handlers import OnStateTransition
import lifecycle_msgs.msg

# 1. Configure driver first
# 2. When driver is Inactive, configure processor
# 3. When both are Inactive, activate driver
# 4. When driver is Active, activate processor

activate_processor = RegisterEventHandler(
    OnStateTransition(
        target_lifecycle_node=driver_node,
        goal_state='active',
        entities=[
            EmitEvent(event=ChangeState(
                lifecycle_node_matcher=lambda node: node.node_name == 'lidar_processor',
                transition_id=lifecycle_msgs.msg.Transition.TRANSITION_ACTIVATE,
            )),
        ],
    )
)
```

### Programmatic lifecycle management

For complex orchestration beyond what launch files can express:

```cpp
#include <rclcpp/rclcpp.hpp>
#include <lifecycle_msgs/srv/change_state.hpp>
#include <lifecycle_msgs/srv/get_state.hpp>

class LifecycleOrchestrator : public rclcpp::Node
{
public:
  LifecycleOrchestrator() : Node("orchestrator")
  {
    // Create clients for each managed node
    driver_state_client_ = create_client<lifecycle_msgs::srv::ChangeState>(
      "/driver/change_state");
    processor_state_client_ = create_client<lifecycle_msgs::srv::ChangeState>(
      "/lidar_processor/change_state");
  }

  void bring_up_system()
  {
    // Configure nodes in dependency order
    change_state(driver_state_client_,
                 lifecycle_msgs::msg::Transition::TRANSITION_CONFIGURE);
    change_state(processor_state_client_,
                 lifecycle_msgs::msg::Transition::TRANSITION_CONFIGURE);

    // Activate in dependency order
    change_state(driver_state_client_,
                 lifecycle_msgs::msg::Transition::TRANSITION_ACTIVATE);
    change_state(processor_state_client_,
                 lifecycle_msgs::msg::Transition::TRANSITION_ACTIVATE);
  }

private:
  void change_state(
    rclcpp::Client<lifecycle_msgs::srv::ChangeState>::SharedPtr client,
    uint8_t transition)
  {
    auto request = std::make_shared<lifecycle_msgs::srv::ChangeState::Request>();
    request->transition.id = transition;

    if (!client->wait_for_service(std::chrono::seconds(5))) {
      RCLCPP_ERROR(get_logger(), "Lifecycle service not available");
      return;
    }

    auto future = client->async_send_request(request);
    // WARNING: spin_until_future_complete(shared_from_this(), future) will deadlock if
    // this function is called from within an executor callback. The executor cannot deliver
    // the service response while the calling callback occupies it. Only call from main()
    // or a dedicated thread. For lifecycle transitions from within callbacks, use async
    // patterns:
    //
    //   auto future = client->async_send_request(request,
    //     [this](rclcpp::Client<lifecycle_msgs::srv::ChangeState>::SharedFuture result) {
    //       auto response = result.get();
    //       if (response->success) {
    //         RCLCPP_INFO(get_logger(), "Transition succeeded");
    //       }
    //     });
    //
    if (rclcpp::spin_until_future_complete(shared_from_this(), future,
        std::chrono::seconds(10)) != rclcpp::FutureReturnCode::SUCCESS)
    {
      RCLCPP_ERROR(get_logger(), "Failed to change state");
    }
  }

  rclcpp::Client<lifecycle_msgs::srv::ChangeState>::SharedPtr driver_state_client_;
  rclcpp::Client<lifecycle_msgs::srv::ChangeState>::SharedPtr processor_state_client_;
};
```

## 8. Composition with intra-process communication

When nodes run in the same process with intra-process enabled, messages bypass
DDS entirely — zero serialization, zero copy. This works for any nodes sharing
a process (composable components in a container, or nodes manually instantiated
in the same `main()`). Composition is the most common approach, but not the
only one.

### Enabling intra-process in launch

```python
ComposableNode(
    package='my_pkg',
    plugin='my_pkg::MyComponent',
    name='my_node',
    extra_arguments=[{'use_intra_process_comms': True}],
)
```

### Publisher side — must use unique_ptr

```cpp
// Zero-copy publish — transfer ownership to subscriber
auto msg = std::make_unique<sensor_msgs::msg::Image>();
msg->header.stamp = now();
// ... fill data ...
pub_->publish(std::move(msg));
```

### Subscriber side — receives ConstSharedPtr

```cpp
void callback(const sensor_msgs::msg::Image::ConstSharedPtr msg)
{
  // msg points to the same memory that was published — no copy
  process(msg);
}
```

### Requirements for zero-copy

1. Both publisher and subscriber in the same process (e.g., same `ComposableNodeContainer` or same `main()`)
2. Both have `use_intra_process_comms: true`
3. Publisher uses `std::unique_ptr` with `publish(std::move(msg))`
4. QoS uses `KEEP_LAST` (not `KEEP_ALL`)
5. Only one subscriber reads the message (otherwise a copy is made for each)

### Performance impact

| Scenario | Latency | Throughput | CPU |
|---|---|---|---|
| Inter-process (DDS) | ~100–500 µs | Limited by serialization | High |
| Intra-process (zero-copy) | ~1–10 µs | Memory bandwidth | Minimal |

## 9. System-level lifecycle management

### Bond-based health monitoring

Use `bond` to detect when a lifecycle node dies unexpectedly:

```cpp
#include <bondcpp/bond.hpp>

// In the lifecycle node's on_activate:
bond_ = std::make_unique<bond::Bond>("bond_topic", get_name(),
  shared_from_this());
bond_->start();

// In on_deactivate:
if (bond_) { bond_->breakBond(); bond_.reset(); }
```

The orchestrator monitors the bond and can restart or reconfigure nodes that
fail unexpectedly.

### State monitoring via CLI

```bash
# Check current state
ros2 lifecycle get /lidar_processor

# List available transitions
ros2 lifecycle list /lidar_processor

# Trigger transitions
ros2 lifecycle set /lidar_processor configure
ros2 lifecycle set /lidar_processor activate
ros2 lifecycle set /lidar_processor deactivate
ros2 lifecycle set /lidar_processor cleanup
ros2 lifecycle set /lidar_processor shutdown
```

## 10. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Component not found during load | Plugin not registered or shared library not installed | Verify `rclcpp_components_register_nodes()` in CMakeLists.txt, rebuild, source setup.bash |
| LifecyclePublisher not publishing | Node not in Active state | Transition to Active before publishing; check with `ros2 lifecycle get` |
| `on_configure` fails | Resource allocation error (port busy, memory) | Log the specific error, ensure cleanup releases resources on retry |
| Transition hangs indefinitely | Blocking call in transition callback | Keep transitions fast; offload heavy init to a thread if needed |
| Components crash container | Unhandled exception in one component | Catch all exceptions in component callbacks; consider `component_container_isolated` |
| Intra-process not working | Missing `use_intra_process_comms` in extra_arguments | Add to launch description; verify both sides are in the same container |
| Node restarts but won't reconfigure | Previous cleanup didn't release resources | Ensure `on_cleanup` and `on_shutdown` release all resources (reset shared_ptrs) |
| State transition rejected | Invalid transition from current state | Check state machine diagram; you cannot go from Unconfigured directly to Active |
