# Communication Patterns

## Table of contents
1. Choosing the right pattern
2. Topics
3. Services
4. Actions
5. Custom interfaces
6. QoS deep dive
7. DDS configuration
8. Serialization and bandwidth
9. Common failures and fixes

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
  // Spawn a thread for long-running execution to avoid blocking the executor.
  [this](const std::shared_ptr<GoalHandle> goal_handle)
  {
    std::thread{[this, goal_handle]() {
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
    }}.detach();
  });
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

## 6. QoS deep dive

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

### Debugging QoS issues

```bash
# Show full QoS settings for all publishers and subscribers on a topic
ros2 topic info /cmd_vel -v

# Check for incompatible QoS events (logged to /rosout)
ros2 topic echo /rosout --qos-reliability reliable --field msg | grep -i "incompatible"
```

## 7. DDS configuration

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
Tier 1 in Kilted (May 2025). It offers lower wire overhead and better performance
in challenging network conditions compared to DDS.

```bash
# Install (available as binary in Jazzy+)
sudo apt install ros-jazzy-rmw-zenoh-cpp

# Use Zenoh instead of CycloneDDS
export RMW_IMPLEMENTATION=rmw_zenoh_cpp
```

**Note:** Zenoh requires a Zenoh router for discovery (multicast is disabled by
default). Start the router before launching nodes:
```bash
ros2 run rmw_zenoh_cpp rmw_zenohd
```

### Localhost-only communication (for development)

```bash
export ROS_LOCALHOST_ONLY=1
# Or in CycloneDDS:
# <General><AllowMulticast>false</AllowMulticast></General>
# and only list 127.0.0.1 in Peers
```

## 8. Serialization and bandwidth

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

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Publisher sends, subscriber receives nothing | QoS mismatch | Check with `ros2 topic info -v`, align reliability/durability |
| Subscriber gets messages but with huge delay | Large message + RELIABLE + small buffer | Increase depth or switch to BEST_EFFORT for sensor data |
| Service call hangs forever | Synchronous call in executor callback | Use `async_send_request`, never synchronous in callbacks |
| Action feedback not arriving | Client not spinning | Ensure client node is being spun (e.g., in MultiThreadedExecutor) |
| "Failed to find type support" at runtime | Interface package not sourced | `source install/setup.bash` and verify with `ros2 interface show` |
| Messages arrive out of order | BEST_EFFORT over lossy network | Use RELIABLE for ordering guarantees, or handle reordering in logic |
| High CPU from subscriber | Callback slower than publish rate | Increase subscriber queue depth, add `KEEP_LAST` with small depth |
