# Nodes and Executors

## Table of contents
1. Node anatomy — rclcpp and rclpy
2. Executor models
3. Callback groups
4. Intra-process communication
5. Custom executors
6. Node composition in a single process
7. Patterns by use case
8. Performance considerations
9. Common failures and fixes

---

## 1. Node anatomy

### rclcpp node (C++)

```cpp
#include <rclcpp/rclcpp.hpp>
#include <sensor_msgs/msg/joint_state.hpp>

class JointPublisher : public rclcpp::Node
{
public:
  JointPublisher()
  : Node("joint_publisher")
  {
    // Declare parameters with descriptors
    auto rate_desc = rcl_interfaces::msg::ParameterDescriptor{};
    rate_desc.description = "Publishing rate in Hz";
    rate_desc.floating_point_range.resize(1);
    rate_desc.floating_point_range[0].from_value = 1.0;
    rate_desc.floating_point_range[0].to_value = 1000.0;
    this->declare_parameter("publish_rate", 50.0, rate_desc);

    double rate = this->get_parameter("publish_rate").as_double();

    // Create publisher with appropriate QoS
    pub_ = this->create_publisher<sensor_msgs::msg::JointState>(
      "joint_states", rclcpp::SensorDataQoS());

    // Timer drives the publish loop — never use sleep() in a callback
    timer_ = this->create_wall_timer(
      std::chrono::duration<double>(1.0 / rate),
      std::bind(&JointPublisher::publish_state, this));
  }

private:
  void publish_state()
  {
    auto msg = sensor_msgs::msg::JointState();
    msg.header.stamp = this->get_clock()->now();
    msg.name = {"joint_1", "joint_2"};
    msg.position = {pos_1_, pos_2_};
    pub_->publish(msg);
  }

  rclcpp::Publisher<sensor_msgs::msg::JointState>::SharedPtr pub_;
  rclcpp::TimerBase::SharedPtr timer_;
  double pos_1_ = 0.0, pos_2_ = 0.0;
};

int main(int argc, char ** argv)
{
  rclcpp::init(argc, argv);
  rclcpp::spin(std::make_shared<JointPublisher>());
  rclcpp::shutdown();
  return 0;
}
```

### rclpy node (Python)

```python
import rclpy
from rclpy.node import Node
from rclpy.qos import QoSProfile, ReliabilityPolicy, HistoryPolicy
from sensor_msgs.msg import JointState


class JointPublisher(Node):
    def __init__(self):
        super().__init__('joint_publisher')

        self.declare_parameter('publish_rate', 50.0)
        rate = self.get_parameter('publish_rate').value

        qos = QoSProfile(
            reliability=ReliabilityPolicy.BEST_EFFORT,
            history=HistoryPolicy.KEEP_LAST,
            depth=5,
        )
        self.pub = self.create_publisher(JointState, 'joint_states', qos)
        self.timer = self.create_timer(1.0 / rate, self.publish_state)

    def publish_state(self):
        msg = JointState()
        msg.header.stamp = self.get_clock().now().to_msg()
        msg.name = ['joint_1', 'joint_2']
        msg.position = [0.0, 0.0]
        self.pub.publish(msg)


def main(args=None):
    rclpy.init(args=args)
    node = JointPublisher()
    try:
        rclpy.spin(node)
    except KeyboardInterrupt:
        pass
    finally:
        node.destroy_node()
        rclpy.shutdown()
```

**Key differences:**
- rclcpp uses `SharedPtr` everywhere — understand ownership semantics
- rclpy GIL limits true parallelism — offload CPU work to C++ or `concurrent.futures`
- Both: always declare parameters in constructor, never use undeclared params

## 2. Executor models

### SingleThreadedExecutor (default)

```cpp
rclcpp::spin(node);
// Equivalent to:
rclcpp::executors::SingleThreadedExecutor executor;
executor.add_node(node);
executor.spin();
```

All callbacks run on one thread, serialized. Simple and safe, but a slow callback
blocks everything. This is fine for nodes with lightweight, fast callbacks.

### MultiThreadedExecutor

```cpp
rclcpp::executors::MultiThreadedExecutor executor;
executor.add_node(node_a);
executor.add_node(node_b);
executor.spin();  // Uses std::thread::hardware_concurrency() threads
```

Callbacks can run in parallel. You **must** pair this with callback groups to
control which callbacks may overlap (see section 3).

### StaticSingleThreadedExecutor

```cpp
rclcpp::executors::StaticSingleThreadedExecutor executor;
executor.add_node(node);
executor.spin();
```

Like `SingleThreadedExecutor` but pre-computes the callback schedule at startup.
Lower overhead per spin iteration — use for nodes with a fixed set of subscriptions
and timers (no dynamic creation/destruction at runtime).

### EventsExecutor (Jazzy+)

```cpp
rclcpp::experimental::executors::EventsExecutor executor;
executor.add_node(node);
executor.spin();
```

Event-driven instead of polling-based. Lower CPU usage when idle, faster wake-up
on incoming data. Preferred for systems with many nodes and intermittent traffic.

### Choosing an executor

| Scenario | Executor | Why |
|---|---|---|
| Simple node, few callbacks | `SingleThreadedExecutor` | Simplest, no thread-safety concerns |
| Fixed callback set, low overhead | `StaticSingleThreadedExecutor` | Reduced per-spin cost |
| Multiple nodes or slow callbacks | `MultiThreadedExecutor` | Prevents one slow callback from blocking others |
| Many nodes, intermittent data | `EventsExecutor` | Lower CPU when idle |
| Custom scheduling requirements | Custom executor | Full control over callback ordering and priority |

## 3. Callback groups

Callback groups control which callbacks may execute concurrently in a
`MultiThreadedExecutor`.

### MutuallyExclusiveCallbackGroup

```cpp
auto group = this->create_callback_group(
  rclcpp::CallbackGroupType::MutuallyExclusive);

rclcpp::SubscriptionOptions opts;
opts.callback_group = group;

sub_ = this->create_subscription<Msg>("topic", 10, callback, opts);
timer_ = this->create_wall_timer(100ms, timer_cb,  group);
// sub_ callback and timer_cb will NEVER run at the same time
```

Use when callbacks share state and you want serialization without manual locking.

### ReentrantCallbackGroup

```cpp
auto group = this->create_callback_group(
  rclcpp::CallbackGroupType::Reentrant);
// Callbacks in this group CAN run simultaneously — protect shared state
```

Use when callbacks are independent or when you need maximum throughput and can
handle your own synchronization.

### The default group trap

If you do not assign a callback group, all callbacks go into the node's default
`MutuallyExclusiveCallbackGroup`. This means with a `MultiThreadedExecutor`,
callbacks on the **same node** still serialize. To actually get parallelism,
explicitly assign a `Reentrant` group.

### Recommended pattern: separate groups by data access

```cpp
// Group 1: sensor callbacks (reentrant — they read different sensors)
auto sensor_group = create_callback_group(rclcpp::CallbackGroupType::Reentrant);

// Group 2: state machine callbacks (mutually exclusive — shared state)
auto state_group = create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

// Assign explicitly
rclcpp::SubscriptionOptions sensor_opts;
sensor_opts.callback_group = sensor_group;
lidar_sub_ = create_subscription<LaserScan>("/scan", 10, lidar_cb, sensor_opts);
imu_sub_ = create_subscription<Imu>("/imu", 10, imu_cb, sensor_opts);

rclcpp::SubscriptionOptions state_opts;
state_opts.callback_group = state_group;
cmd_sub_ = create_subscription<Twist>("/cmd_vel", 10, cmd_cb, state_opts);
```

## 4. Intra-process communication

When multiple nodes run in the same process (via composition), you can
eliminate serialization overhead entirely.

```cpp
rclcpp::NodeOptions options;
options.use_intra_process_comms(true);

auto node = std::make_shared<MyNode>(options);
```

**Requirements:**
- Publisher and subscriber must be in the same process
- Use `std::unique_ptr<MessageT>` when publishing (transfers ownership)
- Both must use compatible QoS (typically `KEEP_LAST`, depth 1)

```cpp
// Publisher side — must publish unique_ptr for zero-copy
auto msg = std::make_unique<sensor_msgs::msg::Image>();
// ... fill msg ...
pub_->publish(std::move(msg));

// Subscriber side — receives shared_ptr, zero copy from same process
void callback(const sensor_msgs::msg::Image::ConstSharedPtr msg) {
  // msg points to the same memory — no copy occurred
}
```

**When intra-process shines:**
- Image pipelines (camera → detector → tracker in one process)
- Sensor fusion (IMU + encoder → odometry in one process)
- Any high-bandwidth data path within one process

**Limitations:**
- Does not work across processes (falls back to DDS)
- All nodes must be loaded as components
- `KEEP_ALL` history breaks zero-copy optimization

## 5. Custom executors

For advanced scheduling requirements (e.g., priority-based, deadline-aware),
subclass `rclcpp::Executor`:

```cpp
class PriorityExecutor : public rclcpp::Executor
{
public:
  void spin() override
  {
    while (rclcpp::ok()) {
      // Get all ready callbacks
      // Sort by priority (e.g., control > perception > logging)
      // Execute in priority order
    }
  }
};
```

This is rarely needed but powerful for real-time systems where certain callbacks
must preempt others.

## 6. Node composition in a single process

### Launch-time composition (recommended)

```python
from launch_ros.actions import ComposableNodeContainer
from launch_ros.descriptions import ComposableNode

container = ComposableNodeContainer(
    name='my_container',
    namespace='',
    package='rclcpp_components',
    executable='component_container_mt',  # _mt = MultiThreadedExecutor
    composable_node_descriptions=[
        ComposableNode(
            package='my_robot_driver',
            plugin='my_robot_driver::DriverComponent',
            name='driver',
            parameters=[{'publish_rate': 100.0}],
        ),
        ComposableNode(
            package='my_robot_perception',
            plugin='my_robot_perception::DetectorComponent',
            name='detector',
        ),
    ],
)
```

### Runtime composition (dynamic loading)

```bash
# Start empty container
ros2 run rclcpp_components component_container

# Load a component
ros2 component load /ComponentManager my_robot_driver my_robot_driver::DriverComponent
```

### Container types

| Container | Threads | Use case |
|---|---|---|
| `component_container` | Single | Simple, all callbacks serial |
| `component_container_mt` | Multi | Independent components need parallelism |
| `component_container_isolated` | Multi + isolation | Each component gets its own executor |

## 7. Patterns by use case

### Sensor driver node

```cpp
class SensorDriver : public rclcpp_lifecycle::LifecycleNode
{
  // on_configure: open serial port, allocate buffers
  // on_activate: start timer to poll sensor, begin publishing
  // on_deactivate: stop timer, stop publishing
  // on_cleanup: close serial port, free buffers
  // on_error: attempt recovery, log diagnostics
};
```

### Periodic controller node

```cpp
class Controller : public rclcpp::Node
{
  // Timer at control frequency (e.g., 500 Hz)
  // Subscription for sensor input
  // Publisher for actuator commands
  // MutuallyExclusive group for timer + subscription
  // Reentrant group for diagnostic publisher (non-critical)
};
```

### Event-driven processor

```cpp
class ImageProcessor : public rclcpp::Node
{
  // Subscription for images (drives processing)
  // No timer — work is triggered by incoming messages
  // Service for configuration changes
  // Action for long-running tasks (e.g., calibration)
};
```

## 8. Performance considerations

- **Avoid `shared_ptr` cycles:** Node → Subscription → Callback → Node.
  Use `weak_ptr` or capture `this` as raw pointer with guaranteed lifetime.
- **Pre-allocate messages** in real-time paths. Do not allocate in callbacks.
- **Use `StaticSingleThreadedExecutor`** when the callback set is fixed.
- **Measure with `ros2 topic delay`** and **tracing** before optimizing.
- **Python GIL:** For CPU-bound Python nodes, use `ProcessPoolExecutor` for
  parallel computation, or rewrite the hot path in C++ as a component.

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Callbacks stop firing | Blocking call in callback | Offload to thread, use async service calls |
| Segfault on shutdown | Accessing destroyed node in callback | Use `weak_from_this()`, check validity |
| Memory growing over time | Unbounded queue + slow subscriber | Use `KEEP_LAST` with depth, or process faster |
| Callbacks run serially despite MultiThreadedExecutor | All in default MutuallyExclusive group | Assign Reentrant callback group explicitly |
| Timer drifts under load | Wall timer + heavy callbacks | Use a dedicated callback group or reduce callback work |
| Intra-process not working | Missing `use_intra_process_comms(true)` or not in same container | Enable in NodeOptions, load into same ComposableNodeContainer |
