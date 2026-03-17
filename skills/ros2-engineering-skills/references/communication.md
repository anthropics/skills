# Communication Patterns

## Table of contents
1. Choosing the right pattern
2. Topics
3. Services
4. Actions
5. Custom interfaces
6. Type adapters (REP-2007)
7. Content-filtered topics (Jazzy+)
8. Service introspection (Jazzy+)
9. QoS deep dive
10. DDS configuration
11. Serialization and bandwidth
12. Common failures and fixes

---

## 1. Choosing the right pattern

| Criteria | Topic | Service | Action |
|---|---|---|---|
| Directionality | One-to-many broadcast | One-to-one request/response | One-to-one with feedback |
| Blocking | Non-blocking publish | Blocking (client waits) | Non-blocking (async) |
| Duration | Continuous stream | Quick computation (< 1s) | Long-running task (seconds+) |
| Cancelable | No | No | Yes |
| Feedback | No | No | Yes (periodic updates) |
| Typical use | Sensor data, state, commands | Parameter queries, mode set | Navigation, trajectory exec |

**Decision rule:**
- Data flows continuously → Topic
- Client needs a result from a specific request → Service
- Task takes time and client wants progress/cancellation → Action

## 2. Topics

### Publisher (C++)

```cpp
// Reliable, keep last 1 — for command topics
auto pub = create_publisher<geometry_msgs::msg::Twist>(
  "cmd_vel", rclcpp::QoS(1).reliable());

// Best effort, keep last 5 — for high-frequency sensor data
auto pub = create_publisher<sensor_msgs::msg::LaserScan>(
  "scan", rclcpp::SensorDataQoS());
```

### Subscriber with message filter

```cpp
#include <message_filters/subscriber.h>
#include <message_filters/time_synchronizer.h>

message_filters::Subscriber<Image> image_sub(this, "camera/image");
message_filters::Subscriber<CameraInfo> info_sub(this, "camera/info");

auto sync = std::make_shared<message_filters::TimeSynchronizer<Image, CameraInfo>>(
  image_sub, info_sub, 10);
sync->registerCallback(&MyNode::synced_callback, this);
```

### Latched topic equivalent (transient local)

```cpp
auto qos = rclcpp::QoS(1)
  .reliable()
  .transient_local();  // Late subscribers get the last published message

auto pub = create_publisher<nav_msgs::msg::OccupancyGrid>("map", qos);
```

## 3. Services

### Server (C++)

```cpp
auto srv = create_service<my_robot_interfaces::srv::SetMode>(
  "set_mode",
  [this](const std::shared_ptr<SetMode::Request> req,
         std::shared_ptr<SetMode::Response> res)
  {
    if (req->mode == "idle" || req->mode == "active") {
      current_mode_ = req->mode;
      res->success = true;
      res->message = "Mode set to " + req->mode;
    } else {
      res->success = false;
      res->message = "Unknown mode: " + req->mode;
    }
  });
```

### Client — async (preferred)

```cpp
auto client = create_client<SetMode>("set_mode");

// Wait for service with timeout
if (!client->wait_for_service(std::chrono::seconds(5))) {
  RCLCPP_ERROR(get_logger(), "Service not available");
  return;
}

auto request = std::make_shared<SetMode::Request>();
request->mode = "active";

auto future = client->async_send_request(request,
  [this](rclcpp::Client<SetMode>::SharedFuture result) {
    auto response = result.get();
    RCLCPP_INFO(get_logger(), "Result: %s", response->message.c_str());
  });
```

**Never call services synchronously from a callback** — it deadlocks the executor.
Always use `async_send_request` with a callback or a separate thread.

## 4. Actions

### Server (C++)

```cpp
#include <rclcpp_action/rclcpp_action.hpp>

using MoveToPosition = my_robot_interfaces::action::MoveToPosition;
using GoalHandle = rclcpp_action::ServerGoalHandle<MoveToPosition>;

auto server = rclcpp_action::create_server<MoveToPosition>(
  this, "move_to_position",
  // Goal callback — accept or reject
  [this](const rclcpp_action::GoalUUID &, std::shared_ptr<const MoveToPosition::Goal> goal)
  {
    if (goal->target_position.z < 0) {
      return rclcpp_action::GoalResponse::REJECT;
    }
    return rclcpp_action::GoalResponse::ACCEPT_AND_EXECUTE;
  },
  // Cancel callback
  [this](const std::shared_ptr<GoalHandle>)
  {
    return rclcpp_action::CancelResponse::ACCEPT;
  },
  // Accepted callback — called when goal is accepted.
  // Store the execution thread as a member to ensure clean shutdown.
  // NEVER use .detach() — it risks accessing destroyed resources after
  // the node shuts down.
  [this](const std::shared_ptr<GoalHandle> goal_handle)
  {
    // Join any previously running execution thread before starting a new one
    if (execution_thread_.joinable()) {
      execution_thread_.join();
    }
    execution_thread_ = std::thread{[this, goal_handle]() {
      auto feedback = std::make_shared<MoveToPosition::Feedback>();
      auto result = std::make_shared<MoveToPosition::Result>();

      try {
        while (rclcpp::ok() && !at_target()) {
          if (goal_handle->is_canceling()) {
            result->success = false;
            goal_handle->canceled(result);
            return;
          }
          feedback->progress = compute_progress();
          goal_handle->publish_feedback(feedback);
          std::this_thread::sleep_for(std::chrono::milliseconds(100));
        }
        result->success = true;
        goal_handle->succeed(result);
      } catch (const std::exception & e) {
        RCLCPP_ERROR(get_logger(), "Action execution failed: %s", e.what());
        result->success = false;
        goal_handle->abort(result);
      }
    }};
  });

// Class member and destructor pattern:
// std::thread execution_thread_;
//
// ~MyActionServer() {
//   if (execution_thread_.joinable()) {
//     execution_thread_.join();
//   }
// }
//
// For lifecycle nodes, join in on_deactivate():
// CallbackReturn on_deactivate(const rclcpp_lifecycle::State &) override {
//   if (execution_thread_.joinable()) {
//     execution_thread_.join();
//   }
//   return CallbackReturn::SUCCESS;
// }
```

### Client (C++)

```cpp
auto client = rclcpp_action::create_client<MoveToPosition>(this, "move_to_position");

auto goal = MoveToPosition::Goal();
goal.target_position.x = 1.0;

auto send_goal_options = rclcpp_action::Client<MoveToPosition>::SendGoalOptions();
send_goal_options.feedback_callback =
  [this](auto, const auto & feedback) {
    RCLCPP_INFO(get_logger(), "Progress: %.1f%%", feedback->progress);
  };
send_goal_options.result_callback =
  [this](const auto & result) {
    switch (result.code) {
      case rclcpp_action::ResultCode::SUCCEEDED:
        RCLCPP_INFO(get_logger(), "Reached target");
        break;
      case rclcpp_action::ResultCode::ABORTED:
        RCLCPP_ERROR(get_logger(), "Goal aborted");
        break;
      case rclcpp_action::ResultCode::CANCELED:
        RCLCPP_WARN(get_logger(), "Goal canceled");
        break;
      default:
        RCLCPP_ERROR(get_logger(), "Unknown result code");
        break;
    }
  };

client->async_send_goal(goal, send_goal_options);
```

## 5. Custom interfaces

### Message definition (.msg)

```
# my_robot_interfaces/msg/RobotStatus.msg
std_msgs/Header header
string robot_id
uint8 mode                    # 0=IDLE, 1=ACTIVE, 2=ERROR
float64 battery_voltage
float64 cpu_temperature
geometry_msgs/Pose current_pose
bool emergency_stop_active
```

### Service definition (.srv)

```
# my_robot_interfaces/srv/SetMode.srv
string mode
bool force
---
bool success
string message
```

### Action definition (.action)

```
# my_robot_interfaces/action/MoveToPosition.action
# Goal
geometry_msgs/Point target_position
float64 max_velocity
---
# Result
bool success
float64 total_distance
float64 total_time
---
# Feedback
float64 progress
geometry_msgs/Point current_position
float64 distance_remaining
```

**Interface design rules:**
- Use existing `std_msgs`, `geometry_msgs`, `sensor_msgs` types when possible
- Add a `Header` field to any message that represents a measurement in time
- Use fixed-size arrays when the length is known; variable arrays otherwise
- Use enums via `uint8` constants with named values in comments
- Put interfaces in a dedicated `*_interfaces` package

## 6. Type adapters (REP-2007)

Type adapters (introduced in REP-2007, available in rclcpp Humble+) allow nodes to
work natively with custom C++ types (e.g., `cv::Mat`, `Eigen::Matrix3d`) while ROS
handles serialization to standard message types automatically. The middleware never
sees the custom type -- it only serializes the ROS message. This eliminates manual
conversion boilerplate and enables zero-copy intra-process transfer of custom types.

**Note:** Type adapters are a C++ (rclcpp) feature only. They are not available in rclpy.

### TypeAdapter specialization

```cpp
#include <rclcpp/type_adapter.hpp>

template<>
struct rclcpp::TypeAdapter<cv::Mat, sensor_msgs::msg::Image>
{
  using is_specialized = std::true_type;
  using custom_type = cv::Mat;
  using ros_message_type = sensor_msgs::msg::Image;

  static void convert_to_ros_message(
    const custom_type & source,
    ros_message_type & destination)
  {
    // Convert cv::Mat to sensor_msgs::msg::Image
    destination.header.stamp = rclcpp::Clock().now();
    destination.height = source.rows;
    destination.width = source.cols;
    destination.encoding = "bgr8";
    destination.is_bigendian = false;
    destination.step = static_cast<uint32_t>(source.step);
    destination.data.assign(source.data,
                            source.data + source.total() * source.elemSize());
  }

  static void convert_to_custom(
    const ros_message_type & source,
    custom_type & destination)
  {
    // Convert sensor_msgs::msg::Image to cv::Mat
    int cv_type = CV_8UC3;  // Assumes bgr8 encoding
    destination = cv::Mat(source.height, source.width, cv_type,
                          const_cast<uint8_t *>(source.data.data()),
                          source.step).clone();
  }
};

RCLCPP_USING_CUSTOM_TYPE_AS_ROS_MESSAGE_TYPE(cv::Mat, sensor_msgs::msg::Image);
```

### Using the adapted type in a node

```cpp
// The macro defines AdaptedType that can be used directly with create_publisher
// and create_subscription. On the wire, sensor_msgs::msg::Image is sent.
// In callbacks, you receive cv::Mat directly.

using AdaptedImageType = rclcpp::TypeAdapter<cv::Mat, sensor_msgs::msg::Image>;

class ImageProcessingNode : public rclcpp::Node
{
public:
  ImageProcessingNode() : Node("image_processor")
  {
    pub_ = create_publisher<AdaptedImageType>("output_image", 10);
    sub_ = create_subscription<AdaptedImageType>(
      "input_image", 10,
      [this](const cv::Mat & mat) {
        // Receive cv::Mat directly -- no cv_bridge needed
        cv::Mat processed;
        cv::GaussianBlur(mat, processed, cv::Size(5, 5), 0);
        pub_->publish(processed);
      });
  }

private:
  rclcpp::Publisher<AdaptedImageType>::SharedPtr pub_;
  rclcpp::Subscription<AdaptedImageType>::SharedPtr sub_;
};
```

**Performance note:** When combined with intra-process communication
(`rclcpp::NodeOptions().use_intra_process_comms(true)`), type adapters enable true
zero-copy `cv::Mat` transfer between nodes in the same process, completely bypassing
serialization and `cv_bridge` overhead.

**Industry reference:** NVIDIA NITROS (used in Isaac ROS) builds on type adapters to
negotiate GPU tensor <-> ROS message conversion, keeping data on the GPU between
NITROS-accelerated nodes and only converting to CPU ROS messages at the boundary.

## 7. Content-filtered topics (Jazzy+)

Content-filtered topics allow subscribers to receive only messages matching a
filter expression, evaluated at the DDS layer before delivery. This reduces CPU
overhead and network bandwidth for subscribers that only need a subset of messages.

### Basic API

```cpp
auto options = rclcpp::SubscriptionOptions();
// SQL-like filter expression with positional parameters
// Filter on top-level fields of the message type only
options.content_filter_options.filter_expression = "temperature > %0";
options.content_filter_options.expression_parameters = {"80.0"};

auto sub = create_subscription<sensor_msgs::msg::Temperature>(
  "diagnostics/temperature", rclcpp::SensorDataQoS(),
  [this](const sensor_msgs::msg::Temperature::SharedPtr msg) {
    // Only called when temperature > 80.0 — filtering happens at DDS layer
    RCLCPP_WARN(get_logger(), "High engine temperature: %.1f", msg->temperature);
  },
  options);
```

**Limitation:** Content filters operate on top-level message fields only. You cannot
filter on nested fields (e.g., `status[].level` inside `DiagnosticArray`). For nested
filtering, subscribe normally and filter in your callback.

### Practical example: filtering by string field

```cpp
auto options = rclcpp::SubscriptionOptions();
// Only receive messages from a specific frame
options.content_filter_options.filter_expression = "header.frame_id = %0";
options.content_filter_options.expression_parameters = {"'base_link'"};

auto sub = create_subscription<sensor_msgs::msg::Imu>(
  "/imu", rclcpp::SensorDataQoS(),
  [this](const sensor_msgs::msg::Imu::SharedPtr msg) {
    RCLCPP_INFO(get_logger(), "Received filtered IMU from %s",
                msg->header.frame_id.c_str());
  },
  options);
```

### Checking content filter support at runtime

```cpp
auto sub = create_subscription<MyMsg>("topic", 10, callback, options);
if (!sub->is_cft_enabled()) {
  RCLCPP_WARN(get_logger(),
    "Content filter not supported by this DDS vendor — "
    "falling back to application-level filtering");
}
```

**DDS vendor support:**

| Vendor | Content filter support |
|---|---|
| FastDDS | Full support |
| CycloneDDS | Limited support (basic expressions only) |
| Connext DDS | Full support |
| Zenoh (rmw_zenoh) | Not currently supported |

## 8. Service introspection (Jazzy+)

Service introspection allows monitoring service request/response pairs without
modifying the server or client code. This is useful for debugging, logging,
compliance auditing, and building service-level observability tools.

### Command-line usage

```bash
# Enable service introspection on a running node
ros2 param set /my_node service_introspection.set_mode "contents"

# Echo service request/response pairs in real time
ros2 service echo /my_service

# Available modes:
#   "off"       — no introspection (default)
#   "metadata"  — publish only metadata (timestamps, client/server IDs)
#   "contents"  — publish full request/response contents
```

### Programmatic configuration

```cpp
#include <rclcpp/rclcpp.hpp>

class IntrospectableServer : public rclcpp::Node
{
public:
  IntrospectableServer() : Node("introspectable_server")
  {
    auto srv = create_service<example_interfaces::srv::AddTwoInts>(
      "add_two_ints",
      [this](const std::shared_ptr<example_interfaces::srv::AddTwoInts::Request> req,
             std::shared_ptr<example_interfaces::srv::AddTwoInts::Response> res) {
        res->sum = req->a + req->b;
      });

    // Enable service introspection programmatically
    srv->configure_introspection(
      get_clock(),
      rclcpp::SystemDefaultsQoS(),
      rcl_service_introspection_contents);  // or rcl_service_introspection_metadata
  }
};
```

### Use cases

- **Debugging:** Observe exact request/response payloads without inserting logging into
  service code.
- **Compliance auditing:** Record all service interactions for regulatory or safety review.
- **Performance monitoring:** Measure service latency by comparing request and response
  timestamps.
- **Testing:** Verify service behavior by capturing interactions during integration tests.

## 9. QoS deep dive

### QoS compatibility matrix

Publisher and subscriber must have compatible QoS settings or the connection
silently fails.

| Publisher | Subscriber | Compatible? |
|---|---|---|
| RELIABLE | RELIABLE | Yes |
| RELIABLE | BEST_EFFORT | Yes |
| BEST_EFFORT | RELIABLE | **No** — subscriber demands reliability publisher cannot guarantee |
| BEST_EFFORT | BEST_EFFORT | Yes |
| TRANSIENT_LOCAL | TRANSIENT_LOCAL | Yes |
| TRANSIENT_LOCAL | VOLATILE | Yes |
| VOLATILE | TRANSIENT_LOCAL | **No** — subscriber expects history publisher does not retain |

### QoS profiles for common scenarios

```cpp
// Sensor data — tolerate drops, minimize latency
auto sensor_qos = rclcpp::SensorDataQoS();
// Equivalent to: best_effort, volatile, keep_last(5)

// Reliable commands — every message must arrive
auto cmd_qos = rclcpp::QoS(1).reliable();

// Map-like data — late joiners get the last map
auto map_qos = rclcpp::QoS(1).reliable().transient_local();

// Diagnostics — moderate buffer, reliable
auto diag_qos = rclcpp::QoS(10).reliable();

// Custom profile with deadline
auto custom_qos = rclcpp::QoS(1)
  .reliable()
  .deadline(std::chrono::milliseconds(100));  // Warn if no message in 100ms
```

### DEADLINE policy

The DEADLINE policy triggers an event when no message arrives within the specified
duration. Use it for safety-critical topics where stale data must be detected.

```cpp
// Publisher declares it will publish at least every 100ms
auto pub_qos = rclcpp::QoS(1).reliable()
  .deadline(std::chrono::milliseconds(100));
auto pub = create_publisher<sensor_msgs::msg::Imu>("imu", pub_qos);

// Subscriber expects a message at least every 100ms
// If no message arrives within 100ms, a RequestedDeadlineMissed event fires
auto sub_qos = rclcpp::QoS(1).reliable()
  .deadline(std::chrono::milliseconds(100));
auto sub = create_subscription<sensor_msgs::msg::Imu>(
  "imu", sub_qos, callback);
```

### LIFESPAN policy

The LIFESPAN policy discards messages that are older than the specified duration
before delivery. This prevents consumers from processing stale data.

```cpp
auto qos = rclcpp::QoS(1).reliable()
  .lifespan(std::chrono::seconds(5));
// Messages older than 5 seconds are discarded before delivery
// Useful for map updates, status messages, or any data with a validity window
auto pub = create_publisher<nav_msgs::msg::OccupancyGrid>("local_costmap", qos);
```

### LIVELINESS policy

The LIVELINESS policy detects when a publisher has silently failed (e.g., node
crash, network partition). The subscriber receives a `LivelinessChanged` event.

```cpp
// Publisher must explicitly assert liveliness every 2 seconds
auto pub_qos = rclcpp::QoS(1).reliable()
  .liveliness(rclcpp::LivelinessPolicy::ManualByTopic)
  .liveliness_lease_duration(std::chrono::seconds(2));
auto pub = create_publisher<std_msgs::msg::Bool>("heartbeat", pub_qos);

// Publisher must call assert_liveliness() periodically
// (typically in a timer callback)
pub->assert_liveliness();

// Subscriber detects publisher failure via LivelinessChanged event
auto sub_qos = rclcpp::QoS(1).reliable()
  .liveliness(rclcpp::LivelinessPolicy::ManualByTopic)
  .liveliness_lease_duration(std::chrono::seconds(2));
```

**When to use each liveliness mode:**

| Mode | Behavior | Use case |
|---|---|---|
| `Automatic` (default) | DDS middleware asserts liveliness based on any activity | General purpose — detects process crash |
| `ManualByTopic` | Publisher must explicitly call `assert_liveliness()` periodically | Safety-critical — detects software hang (node alive but stuck) |
| `ManualByParticipant` | Any write on any topic counts as alive | Less granular than ManualByTopic |

**Rule:** Use `ManualByTopic` for safety-critical heartbeats where you need to detect
not just process death but also software deadlocks or frozen threads. Use `Automatic`
for general "is this publisher still alive?" checks.

### QoS event callbacks

Register callbacks to react to QoS events programmatically instead of checking logs.

```cpp
rclcpp::SubscriptionOptions sub_opts;

sub_opts.event_callbacks.deadline_callback =
  [this](rclcpp::QOSDeadlineRequestedInfo & event) {
    RCLCPP_WARN(get_logger(), "Deadline missed: total=%d, delta=%d",
                event.total_count, event.total_count_change);
    // Trigger fallback behavior, e.g., use last known value or enter safe mode
  };

sub_opts.event_callbacks.liveliness_callback =
  [this](rclcpp::QOSLivelinessChangedInfo & event) {
    RCLCPP_WARN(get_logger(), "Liveliness changed: alive=%d, not_alive=%d",
                event.alive_count, event.not_alive_count);
    if (event.alive_count == 0) {
      RCLCPP_ERROR(get_logger(), "All publishers lost — entering safe mode");
    }
  };

sub_opts.event_callbacks.incompatible_qos_callback =
  [this](rclcpp::QOSRequestedIncompatibleQoSInfo & event) {
    RCLCPP_ERROR(get_logger(), "Incompatible QoS detected on policy: %d",
                 event.last_policy_kind);
  };

auto sub = create_subscription<sensor_msgs::msg::Imu>(
  "imu",
  rclcpp::QoS(1).reliable().deadline(std::chrono::milliseconds(100)),
  imu_callback,
  sub_opts);
```

### Debugging QoS issues

```bash
# Show full QoS settings for all publishers and subscribers on a topic
ros2 topic info /cmd_vel -v

# Check for incompatible QoS events (logged to /rosout)
ros2 topic echo /rosout --qos-reliability reliable --field msg | grep -i "incompatible"
```

## 10. DDS configuration

### CycloneDDS tuning (default vendor)

```xml
<!-- cyclonedds.xml -->
<?xml version="1.0" encoding="UTF-8"?>
<CycloneDDS xmlns="https://cdds.io/config">
  <Domain>
    <General>
      <Interfaces>
        <NetworkInterface name="eth0"/>
      </Interfaces>
      <AllowMulticast>true</AllowMulticast>
      <MaxMessageSize>65500B</MaxMessageSize>
    </General>
    <Internal>
      <SocketReceiveBufferSize min="10MB"/>
    </Internal>
    <Tracing>
      <OutputFile>/tmp/cdds.log</OutputFile>
      <Verbosity>warning</Verbosity>
    </Tracing>
  </Domain>
</CycloneDDS>
```

```bash
export CYCLONEDDS_URI=file://$(pwd)/cyclonedds.xml
```

### Multi-machine communication

```bash
# Same DDS domain (default 0) on same network — automatic discovery
export ROS_DOMAIN_ID=42  # Isolate from other ROS 2 systems on the network

# For networks without multicast (e.g., WiFi issues):
# Use CycloneDDS unicast peer list
```

```xml
<Discovery>
  <Peers>
    <Peer address="192.168.1.100"/>
    <Peer address="192.168.1.101"/>
  </Peers>
  <ParticipantIndex>auto</ParticipantIndex>
</Discovery>
```

### Zenoh as an alternative middleware

Zenoh (`rmw_zenoh_cpp`) is an emerging ROS 2 middleware option — experimental in Jazzy,
Tier 1 in Kilted (May 2025) with production-ready binaries. It offers lower wire
overhead and better performance in challenging network conditions compared to DDS.

```bash
# Install (available as binary in Jazzy+)
sudo apt install ros-jazzy-rmw-zenoh-cpp

# Use Zenoh instead of CycloneDDS
export RMW_IMPLEMENTATION=rmw_zenoh_cpp
```

**Router modes:**

- **Standalone router:** Required for multi-machine setups. Start before launching nodes:
  ```bash
  ros2 run rmw_zenoh_cpp rmw_zenohd
  ```
- **Peer-to-peer:** For small deployments (e.g., single robot), nodes can discover
  each other directly without a router using multicast scouting.
- **Client mode:** For constrained devices (e.g., microcontrollers, edge devices),
  connect to a router without participating in mesh routing:
  ```bash
  export ZENOH_ROUTER_CONFIG_URI=file://$(pwd)/zenoh_client_config.json5
  ```

**Shared memory:** Zenoh supports shared memory transport via the Zenoh SHM plugin,
enabling zero-copy communication for nodes on the same host without iceoryx.

### DDS vendor comparison

| Aspect | CycloneDDS | FastDDS | Connext DDS | Zenoh |
|---|---|---|---|---|
| License | Eclipse Public 2.0 | Apache 2.0 | Commercial | Eclipse Public 2.0 |
| ROS 2 default | Humble+ | Foxy (was default) | Tier 2 | Tier 1 (Kilted+) |
| Shared memory | iceoryx plugin (Jazzy+) | Built-in DataSharing | Built-in | SHM plugin |
| Latency (loopback, 1KB) | ~30-60 us | ~40-80 us | ~20-40 us | ~20-40 us |
| Discovery | SPDP/SEDP (multicast) | SPDP/SEDP (multicast) | SPDP/SEDP + Discovery Server | Zenoh router/scouting |
| Configuration | XML file | XML profile | XML + QoS file | JSON5 config |
| Best for | General purpose, most tested | Large data + SHM | Safety-critical, certified | Constrained networks, WiFi, WAN |

**Large message warning:** The latency numbers above are for small (~1 KB) messages.
For `PointCloud2` (~1.5 MB) or `Image` (~900 KB), expect **50–100x worse latency**
due to serialization, UDP fragmentation, and reassembly. For high-bandwidth data on
latency-sensitive paths, use intra-process zero-copy or shared memory transport.

### Linux kernel tuning for DDS

Large ROS 2 messages (PointCloud2, Image) require OS-level tuning for reliable
DDS transport. Without these settings, publishing large messages may silently fail
or cause extreme latency on congested networks.

```bash
# Required for large message transfer (PointCloud2, images)
sudo sysctl -w net.core.rmem_max=67108864        # 64 MB receive buffer
sudo sysctl -w net.core.rmem_default=67108864
sudo sysctl -w net.core.wmem_max=67108864         # 64 MB send buffer
sudo sysctl -w net.core.wmem_default=67108864

# Prevent UDP fragment timeout issues with large DDS messages
sudo sysctl -w net.ipv4.ipfrag_time=3             # Default 30s is too long
sudo sysctl -w net.ipv4.ipfrag_high_thresh=134217728  # 128 MB fragment buffer
```

Make these persistent by creating `/etc/sysctl.d/10-ros2-dds.conf`:

```bash
# /etc/sysctl.d/10-ros2-dds.conf
net.core.rmem_max=67108864
net.core.rmem_default=67108864
net.core.wmem_max=67108864
net.core.wmem_default=67108864
net.ipv4.ipfrag_time=3
net.ipv4.ipfrag_high_thresh=134217728
```

### Shared memory transport (CycloneDDS + iceoryx)

For nodes on the same host, shared memory transport eliminates serialization and
network stack overhead entirely. CycloneDDS supports iceoryx as a shared memory
backend starting in Jazzy.

```xml
<!-- cyclonedds_shm.xml — Jazzy+ with iceoryx plugin -->
<CycloneDDS xmlns="https://cdds.io/config">
  <Domain>
    <SharedMemory>
      <Enable>true</Enable>
      <LogLevel>warning</LogLevel>
    </SharedMemory>
  </Domain>
</CycloneDDS>
```

```bash
# Start iceoryx RouDi daemon first (must run before any ROS 2 nodes)
iox-roudi &

export CYCLONEDDS_URI=file://$(pwd)/cyclonedds_shm.xml
# Now launch ROS 2 nodes — they will use shared memory for same-host communication
ros2 launch my_robot bringup.launch.py
```

### Per-topic DDS configuration (FastDDS)

FastDDS supports per-topic QoS profiles via XML configuration. CycloneDDS does not
support topic-level QoS overrides in its XML config — set QoS programmatically in code instead.

```xml
<!-- FastDDS: Override QoS for specific topics via XML profile -->
<?xml version="1.0" encoding="UTF-8"?>
<dds xmlns="http://www.eprosima.com/XMLSchemas/fastRTPS_Profiles">
  <profiles>
    <data_writer profile_name="rt_writer" is_default_profile="false">
      <topic><name>rt/*</name></topic>
      <qos>
        <reliability><kind>BEST_EFFORT_RELIABILITY_QOS</kind></reliability>
      </qos>
    </data_writer>
    <data_writer profile_name="map_writer" is_default_profile="false">
      <topic><name>rt/map</name></topic>
      <qos>
        <reliability><kind>RELIABLE_RELIABILITY_QOS</kind></reliability>
        <durability><kind>TRANSIENT_LOCAL_DURABILITY_QOS</kind></durability>
      </qos>
    </data_writer>
  </profiles>
</dds>
```

### Localhost-only communication (for development)

```bash
# Jazzy+ (preferred):
export ROS_AUTOMATIC_DISCOVERY_RANGE=LOCALHOST

# Humble (or Jazzy backward-compatible):
export ROS_LOCALHOST_ONLY=1  # Deprecated in Jazzy+, still functional

# Or in CycloneDDS (all distros):
# <General><AllowMulticast>false</AllowMulticast></General>
# and only list 127.0.0.1 in Peers
```

## 11. Serialization and bandwidth

### Message size estimation

Rule of thumb for planning bandwidth:

| Message type | Typical size | At 30 Hz |
|---|---|---|
| `Twist` | ~56 bytes | ~1.7 KB/s |
| `JointState` (6 DOF) | ~200 bytes | ~6 KB/s |
| `LaserScan` (720 points) | ~6 KB | ~180 KB/s |
| `PointCloud2` (64k points) | ~1.5 MB | ~45 MB/s |
| `Image` (640x480 RGB) | ~900 KB | ~27 MB/s |
| `CompressedImage` (JPEG) | ~50 KB | ~1.5 MB/s |

For high-bandwidth data (images, point clouds):
- Use `image_transport` with compression
- Use intra-process communication within the same process
- Consider shared memory transport (Jazzy+)
- **Message pre-allocation for high-throughput:** In tight loops (>100 Hz), avoid
  creating new message objects per publish cycle. Pre-allocate the message once and
  reuse it, only updating the fields that change:
  ```cpp
  // Pre-allocate once in constructor
  auto msg = std::make_unique<sensor_msgs::msg::PointCloud2>();
  msg->data.reserve(MAX_POINTS * POINT_STEP);  // Reserve max capacity

  // In publish loop — reuse the same allocation
  msg->header.stamp = now();
  msg->data.resize(actual_points * POINT_STEP);  // No realloc if <= reserved
  pub_->publish(std::move(msg));
  msg = std::make_unique<sensor_msgs::msg::PointCloud2>();  // Reallocate for next cycle
  // For true zero-allocation, use intra-process with a message pool pattern
  ```
- **Agnocast (2025 research):** A publish-subscribe framework enabling true zero-copy
  for variable-size messages (`PointCloud2`, `Image`) without serialization. Unlike
  standard intra-process which requires `unique_ptr` ownership transfer, Agnocast uses
  shared memory with reference counting, allowing multiple subscribers to access the
  same memory region. Still experimental -- watch the Autoware integration.

## 12. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Publisher sends, subscriber receives nothing | QoS mismatch | Check with `ros2 topic info -v`, align reliability/durability |
| Subscriber gets messages but with huge delay | Large message + RELIABLE + small buffer | Increase depth or switch to BEST_EFFORT for sensor data |
| Service call hangs forever | Synchronous call in executor callback | Use `async_send_request`, never synchronous in callbacks |
| Action feedback not arriving | Client not spinning | Ensure client node is being spun (e.g., in MultiThreadedExecutor) |
| "Failed to find type support" at runtime | Interface package not sourced | `source install/setup.bash` and verify with `ros2 interface show` |
| Messages arrive out of order | BEST_EFFORT over lossy network | Use RELIABLE for ordering guarantees, or handle reordering in logic |
| High CPU from subscriber | Callback slower than publish rate | Increase subscriber queue depth, add `KEEP_LAST` with small depth |
| QoS deadline missed events not firing | Deadline policy not supported by DDS vendor for this topic type | Use CycloneDDS or FastDDS; verify with `ros2 topic info -v` |
| Content filter has no effect | DDS vendor does not support content filtering | Check vendor docs; CycloneDDS has limited support, FastDDS has full support |
| Shared memory transport not working | iceoryx RouDi daemon not running or CYCLONEDDS_URI not set | Start `iox-roudi` first, export CYCLONEDDS_URI, ensure same user/permissions |
