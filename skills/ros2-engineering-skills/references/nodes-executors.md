# Nodes and Executors

## Table of contents
1. Node anatomy — rclcpp and rclpy
2. Executor models
3. Callback groups
   - When ReentrantCallbackGroup is mandatory
   - Python callback groups (rclpy)
4. Intra-process communication
5. Custom executors
   - Two-executor pattern with `add_callback_group`
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

**rclpy GIL note:** In rclpy, `MultiThreadedExecutor` uses multiple threads, but
Python's GIL prevents true parallelism for CPU-bound callbacks.
`ReentrantCallbackGroup` in rclpy is still essential for I/O-bound work (service
calls, network I/O, file I/O) -- it prevents one blocking I/O callback from starving
others. For CPU-bound parallelism, offload to `concurrent.futures.ProcessPoolExecutor`
or rewrite the hot path as a C++ component.

```python
import concurrent.futures
from rclpy.node import Node
from sensor_msgs.msg import Image

class HeavyProcessingNode(Node):
    def __init__(self):
        super().__init__('heavy_node')
        # Process pool for CPU-bound work — bypasses the GIL
        self._pool = concurrent.futures.ProcessPoolExecutor(max_workers=4)
        self.sub = self.create_subscription(
            Image, '/camera/image_raw', self.image_cb, 10)

    def image_cb(self, msg):
        # Submit CPU-bound work to a separate process
        future = self._pool.submit(run_detection, msg.data)
        future.add_done_callback(self._on_detection_done)

    def _on_detection_done(self, future):
        result = future.result()
        self.get_logger().info(f'Detection complete: {result}')
```

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

**Performance trade-off:** Unlike `SingleThreadedExecutor`, which re-scans all entities
on every spin iteration, `StaticSingleThreadedExecutor` builds its entity list once
and only updates it when topology changes (node/subscription added or removed). This
reduces per-iteration overhead but means entity discovery is slightly delayed compared
to the regular executor. For nodes whose subscription set is truly fixed at startup,
this executor offers the lowest overhead.

### EventsExecutor (Jazzy+)

Event-driven instead of polling-based. Lower CPU usage when idle, faster wake-up
on incoming data. Preferred for systems with many nodes and intermittent traffic.

In Rolling and Kilted, `EventsExecutor` graduated from the experimental namespace
to `rclcpp::executors::EventsExecutor`. For Jazzy, use the experimental namespace.
In Kilted, `EventsExecutor` was also ported to rclpy as `rclpy.executors.EventsExecutor`.

**Benchmark note:** Per the iRobot 2023 paper, `EventsExecutor` achieves approximately
90% reduction in wake-up latency compared to polling-based `SingleThreadedExecutor`
under idle-to-active transition.

**Trade-off warning:** `EventsExecutor` excels at idle-to-active wake-up but can exhibit
**higher p99 latency variance** under sustained high-throughput scenarios compared to
`SingleThreadedExecutor`. In tight control loops (>500 Hz) where worst-case jitter matters
more than average latency, benchmark both executors on your target hardware before
committing. For mixed workloads (some idle nodes, some high-frequency), the two-executor
pattern (section 5) lets you use `SingleThreadedExecutor` on the RT path and
`EventsExecutor` on the non-RT path.

```cpp
// Jazzy — experimental namespace
rclcpp::experimental::executors::EventsExecutor executor;
executor.add_node(node);
executor.spin();
```

```cpp
// Kilted / Rolling — graduated namespace
rclcpp::executors::EventsExecutor executor;
executor.add_node(node);
executor.spin();
```

```python
# Kilted+ — rclpy EventsExecutor
import rclpy
from rclpy.executors import EventsExecutor

rclpy.init()
node = MyNode()
executor = EventsExecutor()
executor.add_node(node)
try:
    executor.spin()
finally:
    executor.shutdown()
    node.destroy_node()
    rclpy.shutdown()
```

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

### When ReentrantCallbackGroup is mandatory

There are scenarios where `MutuallyExclusiveCallbackGroup` fundamentally cannot
work and `ReentrantCallbackGroup` is the only correct choice:

**a) Action server with concurrent goals**

`rclcpp_action::create_server` registers goal, cancel, and accepted/execute
callbacks. When a goal is executing (publishing feedback in a loop), the executor
must still be able to process new goal requests and cancel requests. If these
callbacks are in a `MutuallyExclusiveCallbackGroup`, new goal and cancel requests
are blocked until the current goal finishes -- defeating the purpose of actions.

```cpp
class MultiGoalActionServer : public rclcpp::Node
{
public:
  MultiGoalActionServer()
  : Node("multi_goal_server")
  {
    // ReentrantCallbackGroup is required so the executor can accept
    // new goals and cancellations while a goal is actively executing.
    action_group_ = create_callback_group(
      rclcpp::CallbackGroupType::Reentrant);

    action_server_ = rclcpp_action::create_server<MyAction>(
      this,
      "my_action",
      std::bind(&MultiGoalActionServer::handle_goal, this, _1, _2),
      std::bind(&MultiGoalActionServer::handle_cancel, this, _1),
      std::bind(&MultiGoalActionServer::handle_accepted, this, _1),
      rcl_action_server_get_default_options(),
      action_group_);
  }

private:
  rclcpp_action::GoalResponse handle_goal(
    const rclcpp_action::GoalUUID &,
    std::shared_ptr<const MyAction::Goal>)
  {
    return rclcpp_action::GoalResponse::ACCEPT_AND_EXECUTE;
  }

  rclcpp_action::CancelResponse handle_cancel(
    const std::shared_ptr<rclcpp_action::ServerGoalHandle<MyAction>>)
  {
    return rclcpp_action::CancelResponse::ACCEPT;
  }

  void handle_accepted(
    const std::shared_ptr<rclcpp_action::ServerGoalHandle<MyAction>> goal_handle)
  {
    // Join any previously running execution thread before starting a new one.
    // NEVER use .detach() — detached threads risk accessing destroyed resources
    // after the node shuts down, causing segfaults or undefined behavior.
    if (execution_thread_.joinable()) {
      execution_thread_.join();
    }
    execution_thread_ = std::thread([this, goal_handle]() { execute(goal_handle); });
  }

  void execute(
    const std::shared_ptr<rclcpp_action::ServerGoalHandle<MyAction>> goal_handle)
  {
    auto feedback = std::make_shared<MyAction::Feedback>();
    for (int i = 0; i < 100 && rclcpp::ok(); ++i) {
      if (goal_handle->is_canceling()) {
        goal_handle->canceled(std::make_shared<MyAction::Result>());
        return;
      }
      feedback->progress = static_cast<float>(i) / 100.0f;
      goal_handle->publish_feedback(feedback);
      std::this_thread::sleep_for(100ms);
    }
    goal_handle->succeed(std::make_shared<MyAction::Result>());
  }

  ~MultiGoalActionServer() {
    if (execution_thread_.joinable()) {
      execution_thread_.join();
    }
  }

  rclcpp::CallbackGroup::SharedPtr action_group_;
  rclcpp_action::Server<MyAction>::SharedPtr action_server_;
  std::thread execution_thread_;
};
```

**b) Parallel high-frequency sensor processing**

When a node subscribes to 4 cameras at 30 Hz each (120 callbacks/sec) and each
callback takes 20 ms, a `MutuallyExclusiveCallbackGroup` can only handle
50 callbacks/sec (1000 ms / 20 ms), causing drops. `ReentrantCallbackGroup` with
`MultiThreadedExecutor` allows all 4 to process in parallel.

```cpp
class MultiCameraNode : public rclcpp::Node
{
public:
  MultiCameraNode() : Node("multi_camera")
  {
    // Reentrant group: 4 camera callbacks can run in parallel
    cam_group_ = create_callback_group(
      rclcpp::CallbackGroupType::Reentrant);

    rclcpp::SubscriptionOptions opts;
    opts.callback_group = cam_group_;

    for (int i = 0; i < 4; ++i) {
      auto topic = "/camera_" + std::to_string(i) + "/image_raw";
      cam_subs_.push_back(
        create_subscription<sensor_msgs::msg::Image>(
          topic, rclcpp::SensorDataQoS(),
          [this, i](sensor_msgs::msg::Image::ConstSharedPtr msg) {
            process_image(i, msg);  // Takes ~20ms each
          },
          opts));
    }
  }

private:
  void process_image(int cam_id,
                     sensor_msgs::msg::Image::ConstSharedPtr msg)
  {
    // Each camera callback runs independently in its own thread.
    // No shared state mutation here -- safe without locking.
    auto result = run_detector(msg);
    RCLCPP_DEBUG(get_logger(), "Camera %d: detected %zu objects",
                 cam_id, result.size());
  }

  rclcpp::CallbackGroup::SharedPtr cam_group_;
  std::vector<rclcpp::Subscription<sensor_msgs::msg::Image>::SharedPtr> cam_subs_;
};

// Must use MultiThreadedExecutor to benefit from ReentrantCallbackGroup
int main(int argc, char ** argv)
{
  rclcpp::init(argc, argv);
  rclcpp::executors::MultiThreadedExecutor executor;
  executor.add_node(std::make_shared<MultiCameraNode>());
  executor.spin();
  rclcpp::shutdown();
  return 0;
}
```

**c) Timer + slow subscription overlap**

A 100 Hz control loop timer must not be blocked by a slow data-processing
subscription callback. If both share a `MutuallyExclusiveCallbackGroup`, the
timer misses deadlines whenever the subscription is processing. Put the timer in
one group and the subscription in another, or use `ReentrantCallbackGroup` if
they do not share state.

```cpp
class ControlNode : public rclcpp::Node
{
public:
  ControlNode() : Node("control_node")
  {
    // Option A: Reentrant group — timer and subscription run independently
    auto group = create_callback_group(
      rclcpp::CallbackGroupType::Reentrant);

    timer_ = create_wall_timer(
      10ms,  // 100 Hz control loop
      std::bind(&ControlNode::control_loop, this),
      group);

    rclcpp::SubscriptionOptions opts;
    opts.callback_group = group;
    map_sub_ = create_subscription<nav_msgs::msg::OccupancyGrid>(
      "/map", rclcpp::QoS(1).transient_local(),
      std::bind(&ControlNode::map_callback, this, std::placeholders::_1),
      opts);
  }

private:
  void control_loop()
  {
    // Fast path: read latest sensor data, compute command, publish.
    // Must never be blocked by map_callback.
  }

  void map_callback(nav_msgs::msg::OccupancyGrid::ConstSharedPtr msg)
  {
    // Slow path: processing a large occupancy grid (~50ms).
    // Runs in parallel with control_loop thanks to Reentrant group.
  }

  rclcpp::TimerBase::SharedPtr timer_;
  rclcpp::Subscription<nav_msgs::msg::OccupancyGrid>::SharedPtr map_sub_;
};
```

### Critical pattern: calling a service from a callback

If you call a service from within a subscription or timer callback, the service
client **must** be on a different callback group than the caller. Otherwise the
executor deadlocks — the callback is waiting for the service response, but the
executor cannot process the response because the callback group is occupied.

```cpp
// WRONG — deadlocks in ANY of these conditions:
//   1. SingleThreadedExecutor (only one thread — cannot deliver response while blocked)
//   2. MultiThreadedExecutor when client and caller share a MutuallyExclusive group
//      (group lock prevents response delivery)
// Even with MultiThreadedExecutor + separate groups, spin_until_future_complete
// creates a nested spin that can cause subtle reentrancy bugs. Avoid entirely.
void timer_callback() {
  auto future = client_->async_send_request(request);
  auto result = rclcpp::spin_until_future_complete(shared_from_this(), future);
  // This blocks the executor, which cannot deliver the response → deadlock
}

// CORRECT — use a separate callback group + async handling
class MyNode : public rclcpp::Node {
public:
  MyNode() : Node("my_node") {
    // Timer in default group
    timer_ = create_wall_timer(1s, std::bind(&MyNode::timer_callback, this));

    // Service client in a SEPARATE callback group
    client_group_ = create_callback_group(
      rclcpp::CallbackGroupType::MutuallyExclusive);
    client_ = create_client<MySrv>("my_service",
      rmw_qos_profile_services_default, client_group_);
  }

private:
  void timer_callback() {
    auto request = std::make_shared<MySrv::Request>();
    // Use async with a response callback — does NOT block the executor
    client_->async_send_request(request,
      [this](rclcpp::Client<MySrv>::SharedFuture future) {
        auto response = future.get();
        RCLCPP_INFO(get_logger(), "Got response: %s", response->message.c_str());
      });
  }

  rclcpp::CallbackGroup::SharedPtr client_group_;
  rclcpp::Client<MySrv>::SharedPtr client_;
  rclcpp::TimerBase::SharedPtr timer_;
};
```

**Rule:** When using `MultiThreadedExecutor`, always put service clients in a
separate `MutuallyExclusiveCallbackGroup` from the callbacks that invoke them.
With `SingleThreadedExecutor`, never use `spin_until_future_complete` inside a
callback — always use the async callback pattern shown above.

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

// Group 3: service clients (separate from callers to avoid deadlock)
auto client_group = create_callback_group(rclcpp::CallbackGroupType::MutuallyExclusive);

// Assign explicitly
rclcpp::SubscriptionOptions sensor_opts;
sensor_opts.callback_group = sensor_group;
lidar_sub_ = create_subscription<LaserScan>("/scan", 10, lidar_cb, sensor_opts);
imu_sub_ = create_subscription<Imu>("/imu", 10, imu_cb, sensor_opts);

rclcpp::SubscriptionOptions state_opts;
state_opts.callback_group = state_group;
cmd_sub_ = create_subscription<Twist>("/cmd_vel", 10, cmd_cb, state_opts);

// Service client on its own group — safe to call from sensor or state callbacks
mode_client_ = create_client<SetMode>("/set_mode",
  rmw_qos_profile_services_default, client_group);
```

### Python callback groups (rclpy)

rclpy provides the same callback group semantics as rclcpp. The API differs
slightly: groups are passed directly to subscription/timer/client constructors
via the `callback_group` parameter.

```python
import rclpy
from rclpy.callback_groups import (
    MutuallyExclusiveCallbackGroup,
    ReentrantCallbackGroup,
)
from rclpy.executors import MultiThreadedExecutor
from rclpy.node import Node
from sensor_msgs.msg import LaserScan, Imu
from geometry_msgs.msg import Twist
from example_interfaces.srv import SetBool


class MultiGroupNode(Node):
    def __init__(self):
        super().__init__('multi_group_node')

        # Group 1: sensor callbacks (reentrant — independent data streams)
        self.sensor_group = ReentrantCallbackGroup()

        # Group 2: state callbacks (mutually exclusive — shared state)
        self.state_group = MutuallyExclusiveCallbackGroup()

        # Group 3: service clients (separate group to avoid deadlock)
        self.client_group = MutuallyExclusiveCallbackGroup()

        # Subscriptions assigned to groups
        self.lidar_sub = self.create_subscription(
            LaserScan, '/scan', self.lidar_cb, 10,
            callback_group=self.sensor_group)
        self.imu_sub = self.create_subscription(
            Imu, '/imu', self.imu_cb, 10,
            callback_group=self.sensor_group)

        self.cmd_sub = self.create_subscription(
            Twist, '/cmd_vel', self.cmd_cb, 10,
            callback_group=self.state_group)

        # Timer in the state group — serialized with cmd_cb
        self.timer = self.create_timer(
            0.1, self.control_loop,
            callback_group=self.state_group)

        # Service client on its own group
        self.mode_client = self.create_client(
            SetBool, '/set_mode',
            callback_group=self.client_group)

    def lidar_cb(self, msg):
        self.get_logger().debug(f'Scan: {len(msg.ranges)} ranges')

    def imu_cb(self, msg):
        self.get_logger().debug('IMU received')

    def cmd_cb(self, msg):
        self.latest_cmd = msg  # Shared state, safe — state_group is MutuallyExclusive

    def control_loop(self):
        # Also in state_group, so never runs concurrently with cmd_cb
        pass


def main(args=None):
    rclpy.init(args=args)
    node = MultiGroupNode()
    executor = MultiThreadedExecutor()
    executor.add_node(node)
    try:
        executor.spin()
    finally:
        executor.shutdown()
        node.destroy_node()
        rclpy.shutdown()
```

### Python async service call pattern (rclpy)

In rclpy, calling a service from within a callback requires `call_async()`.
Never use the synchronous `call()` inside a callback -- it blocks the executor
thread and deadlocks.

```python
# WRONG — blocks the executor thread, causes deadlock
def timer_callback(self):
    request = SetBool.Request()
    request.data = True
    response = self.client.call(request)  # Deadlock!

# CORRECT — use call_async with await in an async callback
import asyncio
from rclpy.callback_groups import MutuallyExclusiveCallbackGroup

class AsyncServiceCallerNode(Node):
    def __init__(self):
        super().__init__('async_caller')

        self.client_group = MutuallyExclusiveCallbackGroup()
        self.client = self.create_client(
            SetBool, '/set_mode',
            callback_group=self.client_group)

        # Timer in the default group (separate from client_group)
        self.timer = self.create_timer(1.0, self.timer_callback)

    async def timer_callback(self):
        """Async callback — the executor can process other work while awaiting."""
        if not self.client.service_is_ready():
            self.get_logger().warn('Service not ready')
            return

        request = SetBool.Request()
        request.data = True
        response = await self.client.call_async(request)
        self.get_logger().info(f'Service response: {response.success}')
```

**Key rules for rclpy service calls from callbacks:**
- Always use `call_async()`, never `call()`, inside a callback
- Make the callback `async def` and `await` the future
- Put the service client in a separate `MutuallyExclusiveCallbackGroup`
- Use `MultiThreadedExecutor` to allow the client group to process the response

## 4. Intra-process communication

When multiple nodes run in the same process, you can eliminate serialization
overhead entirely. This works for **any** nodes sharing a process — whether
loaded as composable components, manually instantiated in the same `main()`,
or even publishers and subscribers within the same node. Composition via
`ComposableNodeContainer` is the most common way to colocate nodes, but it
is not the only way.

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
- Every participating node must enable `use_intra_process_comms(true)` in its `NodeOptions`
- `KEEP_ALL` history breaks zero-copy optimization

## 5. Custom executors and alternatives

For advanced scheduling requirements (e.g., priority-based, deadline-aware),
subclass `rclcpp::Executor`. Alternatively, if you want to avoid executors
entirely, ROS 2 provides the `WaitSet` API.

### 5.1 The WaitSet Alternative (Executor-less spin)

An executor is essentially a while loop around a WaitSet. For ultimate control
over scheduling (especially in hard real-time systems where you want zero
hidden allocations or unpredictable callback queues), you can bypass executors
entirely and use `rclcpp::WaitSet`.

```cpp
#include <rclcpp/rclcpp.hpp>

int main(int argc, char ** argv)
{
  rclcpp::init(argc, argv);
  auto node = std::make_shared<rclcpp::Node>("waitset_node");

  // create_subscription requires a callback, but it won't be invoked when
  // using a WaitSet — messages are retrieved manually via take().
  auto sub = node->create_subscription<std_msgs::msg::String>(
    "topic", 10, [](std_msgs::msg::String::UniquePtr) {});

  auto timer = node->create_wall_timer(std::chrono::seconds(1), nullptr);

  // 1. Create a WaitSet that can hold 1 subscription and 1 timer.
  // Note: Only SubscriptionEntry and WaitableEntry are type aliases on WaitSet.
  // The other slots take shared_ptr vectors directly.
  rclcpp::WaitSet wait_set(
    std::vector<rclcpp::WaitSet::SubscriptionEntry>{{sub}},
    std::vector<std::shared_ptr<rclcpp::GuardCondition>>{},
    std::vector<std::shared_ptr<rclcpp::TimerBase>>{timer},
    std::vector<std::shared_ptr<rclcpp::ClientBase>>{},
    std::vector<std::shared_ptr<rclcpp::ServiceBase>>{},
    std::vector<rclcpp::WaitSet::WaitableEntry>{}
  );

  while (rclcpp::ok()) {
    // 2. Wait up to 100ms for something to be ready
    auto wait_result = wait_set.wait(std::chrono::milliseconds(100));

    if (wait_result.kind() == rclcpp::WaitResultKind::Ready) {
      // 3. Check what woke us up and handle it manually
      if (wait_result.get_wait_set().get_rcl_wait_set().timers[0]) {
        // Timer fired
        timer->execute_callback();
      }

      if (wait_result.get_wait_set().get_rcl_wait_set().subscriptions[0]) {
        // Subscription received data
        std_msgs::msg::String msg;
        rclcpp::MessageInfo msg_info;
        if (sub->take(msg, msg_info)) {
          RCLCPP_INFO(node->get_logger(), "Got: %s", msg.data.c_str());
        }
      }
    }
  }

  rclcpp::shutdown();
  return 0;
}
```

WaitSets are powerful because you decide *exactly* the order in which to check
and process entities. If the timer is more important than the subscription, you
check the timer first and process it before taking the message.

> **Note:** The `rclcpp::Executor` protected API varies across distros and is not
> fully stable. The following shows the architectural pattern — adapt method names
> to your target distro. For production, consider the `EventsExecutor` (Kilted+)
> as a higher-performance alternative.

```cpp
#include <rclcpp/rclcpp.hpp>
#include <map>
#include <algorithm>

class PriorityExecutor : public rclcpp::Executor
{
public:
  /// Register a callback group with a priority level (lower number = higher priority).
  void add_callback_group_with_priority(
    rclcpp::CallbackGroup::SharedPtr group,
    rclcpp::node_interfaces::NodeBaseInterface::SharedPtr node_base,
    int priority)
  {
    priority_map_[group.get()] = priority;
    add_callback_group(group, node_base);
  }

  void spin() override
  {
    while (rclcpp::ok()) {
      // Block until at least one callback is ready, with a timeout
      // to allow checking rclcpp::ok() periodically.
      auto any_exec = get_next_ready_executable();
      if (any_exec.has_value()) {
        execute_any_executable(any_exec.value());
      }
    }
  }

private:
  std::optional<rclcpp::AnyExecutable> get_next_ready_executable()
  {
    // Wait for work with a timeout so we can re-check rclcpp::ok()
    std::chrono::nanoseconds timeout(100'000'000);  // 100ms

    // Collect all ready executables by iterating callback groups
    std::vector<std::pair<int, rclcpp::AnyExecutable>> ready_list;

    for (auto & weak_group : get_all_callback_groups()) {
      auto group = weak_group.lock();
      if (!group) {
        continue;
      }
      rclcpp::AnyExecutable any_exec;
      if (get_next_executable(any_exec, timeout)) {
        int prio = 999;
        auto it = priority_map_.find(any_exec.callback_group.get());
        if (it != priority_map_.end()) {
          prio = it->second;
        }
        ready_list.push_back({prio, std::move(any_exec)});
      }
    }

    if (ready_list.empty()) {
      // Fall back to standard wait-for-ready with timeout
      rclcpp::AnyExecutable any_exec;
      if (get_next_executable(any_exec, timeout)) {
        return any_exec;
      }
      return std::nullopt;
    }

    // Sort by priority: lowest number first
    std::sort(ready_list.begin(), ready_list.end(),
      [](const auto & a, const auto & b) { return a.first < b.first; });

    return std::move(ready_list.front().second);
  }

  std::map<rclcpp::CallbackGroup *, int> priority_map_;
};

// Usage
int main(int argc, char ** argv)
{
  rclcpp::init(argc, argv);
  auto node = std::make_shared<rclcpp::Node>("priority_demo");

  auto control_group = node->create_callback_group(
    rclcpp::CallbackGroupType::MutuallyExclusive);
  auto logging_group = node->create_callback_group(
    rclcpp::CallbackGroupType::MutuallyExclusive);

  PriorityExecutor executor;
  // Priority 0 = highest, processes first
  executor.add_callback_group_with_priority(
    control_group, node->get_node_base_interface(), 0);
  // Priority 10 = lower, processes only when higher-priority groups are idle
  executor.add_callback_group_with_priority(
    logging_group, node->get_node_base_interface(), 10);

  executor.spin();
  rclcpp::shutdown();
  return 0;
}
```

This is rarely needed but powerful for real-time systems where certain callbacks
must preempt others. For most applications, splitting callback groups across
separate executors (see below) is simpler and achieves a similar effect.

### Two-executor pattern with `add_callback_group`

Instead of a custom executor, you can split a single node's callback groups
across two standard executors, each running on its own thread. This is the
recommended way to isolate real-time callbacks from non-real-time work.

```cpp
#include <rclcpp/rclcpp.hpp>
#include <std_msgs/msg/float64.hpp>
#include <example_interfaces/srv/set_bool.hpp>
#include <thread>

class DualExecutorNode : public rclcpp::Node
{
public:
  DualExecutorNode() : Node("dual_executor_node")
  {
    // RT group: fast control loop
    rt_group_ = create_callback_group(
      rclcpp::CallbackGroupType::MutuallyExclusive);
    // Background group: slow service calls, logging
    bg_group_ = create_callback_group(
      rclcpp::CallbackGroupType::Reentrant);

    // 500 Hz control timer in the RT group
    control_timer_ = create_wall_timer(
      std::chrono::microseconds(2000),
      std::bind(&DualExecutorNode::control_loop, this),
      rt_group_);

    // Publisher for actuator commands (used from the RT callback)
    cmd_pub_ = create_publisher<std_msgs::msg::Float64>(
      "actuator_cmd", rclcpp::SystemDefaultsQoS());

    // Service client in the background group — safe to call from bg callbacks
    param_client_ = create_client<example_interfaces::srv::SetBool>(
      "/configure_sensor",
      rmw_qos_profile_services_default,
      bg_group_);

    // Slow subscription in the background group
    rclcpp::SubscriptionOptions bg_opts;
    bg_opts.callback_group = bg_group_;
    config_sub_ = create_subscription<std_msgs::msg::Float64>(
      "config_update", 10,
      std::bind(&DualExecutorNode::config_callback, this,
                std::placeholders::_1),
      bg_opts);
  }

  rclcpp::CallbackGroup::SharedPtr rt_group_;
  rclcpp::CallbackGroup::SharedPtr bg_group_;

private:
  void control_loop()
  {
    auto msg = std_msgs::msg::Float64();
    msg.data = compute_command();
    cmd_pub_->publish(msg);
  }

  void config_callback(std_msgs::msg::Float64::ConstSharedPtr msg)
  {
    // Slow processing -- does not affect control_loop timing
    RCLCPP_INFO(get_logger(), "Config update: %f", msg->data);
  }

  double compute_command() { return 0.0; }

  rclcpp::TimerBase::SharedPtr control_timer_;
  rclcpp::Publisher<std_msgs::msg::Float64>::SharedPtr cmd_pub_;
  rclcpp::Client<example_interfaces::srv::SetBool>::SharedPtr param_client_;
  rclcpp::Subscription<std_msgs::msg::Float64>::SharedPtr config_sub_;
};

int main(int argc, char ** argv)
{
  rclcpp::init(argc, argv);
  auto node = std::make_shared<DualExecutorNode>();

  // RT executor: only processes control_timer_ (rt_group_)
  rclcpp::executors::SingleThreadedExecutor rt_executor;
  rt_executor.add_callback_group(
    node->rt_group_, node->get_node_base_interface());

  // Background executor: processes config_sub_ and param_client_ (bg_group_)
  rclcpp::executors::MultiThreadedExecutor bg_executor;
  bg_executor.add_callback_group(
    node->bg_group_, node->get_node_base_interface());

  // Each executor spins on its own thread
  std::thread rt_thread([&]() { rt_executor.spin(); });
  std::thread bg_thread([&]() { bg_executor.spin(); });

  rt_thread.join();
  bg_thread.join();

  rclcpp::shutdown();
  return 0;
}
```

**When to use this pattern:**
- A node has both hard-real-time callbacks (control loops) and soft/non-RT
  callbacks (logging, service calls, parameter updates)
- You want to set different thread priorities (e.g., `SCHED_FIFO` on the RT
  thread) without affecting non-RT callbacks
- You need to prevent a slow subscription from ever blocking a fast timer

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

### 7.1 Sensor driver node (Lifecycle)

```cpp
class SensorDriver : public rclcpp_lifecycle::LifecycleNode
{
  // on_configure: open serial port, allocate buffers
  // on_activate: start timer to poll sensor, begin publishing
  // on_deactivate: stop timer, stop publishing
  // on_cleanup: close serial port, free buffers
  // on_error: attempt recovery (e.g., re-init USB), log diagnostics
};
```

### 7.2 Lifecycle error recovery patterns

When a lifecycle node hits a fatal hardware error (e.g. USB disconnect), it should
transition itself to the `ErrorProcessing` state, attempt recovery, and either
recover back to `Unconfigured` or drop to `Finalized`.

```cpp
class RobustDriver : public rclcpp_lifecycle::LifecycleNode
{
public:
  RobustDriver() : LifecycleNode("robust_driver") {}

  // Normal read loop called by timer
  void read_hardware()
  {
    if (!device_.read()) {
      RCLCPP_ERROR(get_logger(), "Hardware failure! Requesting deactivation.");
      // 1. Deactivate timer
      timer_->cancel();

      // 2. Request deactivation via lifecycle service.
      // The lifecycle state machine will call on_deactivate(). To reach on_error(),
      // return CallbackReturn::ERROR from on_deactivate — the framework then
      // automatically invokes on_error(). You cannot directly trigger the error
      // transition; it is an internal transition driven by callback return values.
      this->trigger_transition(
        lifecycle_msgs::msg::Transition::TRANSITION_DEACTIVATE);
    }
  }

  // 3. The framework calls on_error
  CallbackReturn on_error(const rclcpp_lifecycle::State &) override
  {
    RCLCPP_INFO(get_logger(), "Attempting hardware reset...");
    device_.close();
    std::this_thread::sleep_for(std::chrono::seconds(2));

    if (device_.init()) {
      RCLCPP_INFO(get_logger(), "Recovery successful. Returning to Unconfigured.");
      return CallbackReturn::SUCCESS; // Transitions to Unconfigured
    }

    RCLCPP_FATAL(get_logger(), "Recovery failed. Hardware is dead.");
    return CallbackReturn::FAILURE; // Transitions to Finalized
  }
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
- **MultiThreadedExecutor starvation (EmSoft 2024):** A 2024 research paper
  ("Thread Carefully: Preventing Starvation in the ROS 2 Multi-Threaded
  Executor") identified a priority-inversion pattern where high-frequency timers
  can starve lower-priority subscription callbacks. The executor's ready-set
  evaluation favors timers that are perpetually ready, leaving subscriptions
  unable to acquire execution slots. Mitigation: assign subscriptions and timers
  to separate callback groups on separate executors via `add_callback_group()`
  (see the two-executor pattern in section 5), or use `EventsExecutor` which
  dispatches based on actual events and is not susceptible to this starvation
  pattern.

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Callbacks stop firing | Blocking call in callback | Offload to thread, use async service calls |
| Segfault on shutdown | Accessing destroyed node in callback | Use `weak_from_this()`, check validity |
| Memory growing over time | Unbounded queue + slow subscriber | Use `KEEP_LAST` with depth, or process faster |
| Callbacks run serially despite MultiThreadedExecutor | All in default MutuallyExclusive group | Assign Reentrant callback group explicitly |
| Timer drifts under load | Wall timer + heavy callbacks | Use a dedicated callback group or reduce callback work |
| Intra-process not working | Missing `use_intra_process_comms(true)` or nodes not in same process | Enable in NodeOptions for all participating nodes; ensure they run in the same process (composition, same main(), etc.) |
| Service call deadlocks executor | Service client in same callback group as caller | Put service client in a separate MutuallyExclusiveCallbackGroup; use async_send_request with callback |
