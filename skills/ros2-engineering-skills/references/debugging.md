# Debugging and Diagnostics

## Table of contents
1. ros2 doctor and system diagnostics
2. rqt tools
3. Tracing with ros2_tracing (LTTng)
4. Performance profiling
5. rosbag2 recording and playback
6. GDB debugging for C++ nodes
7. Network and DDS debugging
8. Common crash patterns and post-mortem analysis
9. Common failures and fixes

---

## 1. ros2 doctor and system diagnostics

### Quick health check

```bash
# Full system report
ros2 doctor --report

# Summary only (fast)
ros2 doctor

# Include network analysis
ros2 doctor --report --include-network
```

`ros2 wtf` is an alias for `ros2 doctor` -- both commands are equivalent.

### What ros2 doctor checks
- ROS 2 distribution and middleware configuration
- Network interfaces and multicast capability
- DDS discovery health
- Topic/service/action availability
- Node connectivity

### Topic introspection

```bash
# List all topics with types
ros2 topic list -t

# Detailed QoS info for a topic
ros2 topic info /cmd_vel -v

# Message rate
ros2 topic hz /joint_states

# Bandwidth usage
ros2 topic bw /camera/image_raw

# Latency (requires header with timestamp)
ros2 topic delay /joint_states

# Echo messages (raw)
ros2 topic echo /cmd_vel

# Echo specific field
ros2 topic echo /joint_states --field position

# Echo once (don't stream)
ros2 topic echo /joint_states --once
```

### Node introspection

```bash
# List all nodes
ros2 node list

# Node details (publishers, subscribers, services, parameters)
ros2 node info /my_node

# List parameters
ros2 param list /my_node

# Get parameter value
ros2 param get /my_node publish_rate

# Describe parameter (type, range, description)
ros2 param describe /my_node publish_rate
```

### diagnostics framework

For production systems, use the `diagnostic_updater` to report component health:

```cpp
#include <diagnostic_updater/diagnostic_updater.hpp>

class SensorDriver : public rclcpp::Node
{
public:
  SensorDriver() : Node("sensor_driver"), diag_updater_(this)
  {
    diag_updater_.setHardwareID("lidar_unit_01");
    diag_updater_.add("Connection", this, &SensorDriver::check_connection);
    diag_updater_.add("Data Rate", this, &SensorDriver::check_data_rate);
  }

private:
  void check_connection(diagnostic_updater::DiagnosticStatusWrapper & stat)
  {
    if (is_connected_) {
      stat.summary(diagnostic_msgs::msg::DiagnosticStatus::OK, "Connected");
    } else {
      stat.summary(diagnostic_msgs::msg::DiagnosticStatus::ERROR, "Disconnected");
    }
    stat.add("Port", port_);
    stat.add("Reconnect attempts", reconnect_count_);
  }

  void check_data_rate(diagnostic_updater::DiagnosticStatusWrapper & stat)
  {
    if (current_rate_ > 25.0) {
      stat.summary(diagnostic_msgs::msg::DiagnosticStatus::OK,
                   "Rate nominal");
    } else if (current_rate_ > 10.0) {
      stat.summary(diagnostic_msgs::msg::DiagnosticStatus::WARN,
                   "Rate degraded");
    } else {
      stat.summary(diagnostic_msgs::msg::DiagnosticStatus::ERROR,
                   "Rate critical");
    }
    stat.add("Current rate (Hz)", current_rate_);
  }

  diagnostic_updater::Updater diag_updater_;
  bool is_connected_ = false;
  double current_rate_ = 0.0;
  std::string port_;
  int reconnect_count_ = 0;
};
```

View diagnostics:
```bash
ros2 topic echo /diagnostics
ros2 run rqt_robot_monitor rqt_robot_monitor
```

## 2. rqt tools

### Essential rqt plugins

```bash
# Node graph — see all nodes and their connections
ros2 run rqt_graph rqt_graph

# Console — view /rosout messages with filtering
ros2 run rqt_console rqt_console

# Dynamic reconfigure — edit parameters at runtime
ros2 run rqt_reconfigure rqt_reconfigure

# Topic monitor — stream topic data
ros2 run rqt_topic rqt_topic

# Service caller — call services interactively
ros2 run rqt_service_caller rqt_service_caller

# Image viewer
ros2 run rqt_image_view rqt_image_view

# Plot numeric values
ros2 run rqt_plot rqt_plot /joint_states/position[0] /joint_states/position[1]
```

### rqt_graph tips
- Use "Nodes/Topics (all)" to see the full picture
- Hide `/rosout` and `/parameter_events` to reduce clutter
- Refresh after launching new nodes

## 3. Tracing with ros2_tracing (LTTng)

Low-overhead tracing for analyzing callback latency, scheduling, and DDS behavior.

### Setup

```bash
# Install
sudo apt install ros-jazzy-ros2trace ros-jazzy-tracetools-analysis
sudo apt install lttng-tools babeltrace2

# Add user to tracing group
sudo usermod -aG tracing $USER
```

### Recording a trace

```bash
# Start tracing
# Start tracing (all ROS 2 tracepoints enabled by default)
ros2 trace start my_trace

# Run your system
ros2 launch my_robot_bringup robot.launch.py

# Stop tracing (Iron+; on Humble, use Ctrl+C on the interactive `ros2 trace`)
ros2 trace stop my_trace

# Traces are stored in ~/.ros/tracing/my_trace/
```

### Analyzing traces

```python
# Using tracetools_analysis (API is illustrative — verify against
# your distro's tracetools_analysis source; the internal data model
# may use different attribute names across versions)
from tracetools_analysis.loading import load_file
from tracetools_analysis.processor.ros2 import Ros2Handler

events = load_file('~/.ros/tracing/my_trace/')
handler = Ros2Handler.process(events)

# Get callback durations
for callback in handler.data.callback_instances:
    duration_ns = callback.duration
    print(f'Callback: {callback.callback_object}, Duration: {duration_ns/1e6:.3f} ms')
```

### Key tracepoints

| Tracepoint | What it tells you |
|---|---|
| `ros2:callback_start` / `callback_end` | Callback execution time |
| `ros2:rclcpp_publish` | When a message was published |
| `ros2:rclcpp_subscription_callback_added` | Subscription registration |
| `ros2:rcl_timer_init` | Timer creation with period |

## 4. Performance profiling

### CPU profiling with perf

```bash
# Record CPU profile for a running node
perf record -g -p $(pgrep -f driver_node) -- sleep 10

# Generate flamegraph
perf script | stackcollapse-perf.pl | flamegraph.pl > flamegraph.svg
```

### Memory profiling with valgrind

```bash
# Check for memory leaks
valgrind --leak-check=full --show-leak-kinds=all \
  ros2 run my_robot_driver driver_node

# Heap profiling
valgrind --tool=massif \
  ros2 run my_robot_driver driver_node
ms_print massif.out.<pid>
```

### Callback latency measurement

```cpp
// Add to any node for lightweight latency monitoring
class LatencyMonitor
{
public:
  void tick()
  {
    auto now = std::chrono::steady_clock::now();
    if (last_.time_since_epoch().count() > 0) {
      auto dt = std::chrono::duration_cast<std::chrono::microseconds>(
        now - last_).count();
      count_++;
      total_us_ += dt;
      max_us_ = std::max(max_us_, dt);
      min_us_ = std::min(min_us_, dt);
    }
    last_ = now;
  }

  void report(rclcpp::Logger logger)
  {
    if (count_ > 0) {
      RCLCPP_INFO(logger,
        "Latency stats: avg=%.1f µs, min=%ld µs, max=%ld µs, count=%ld",
        static_cast<double>(total_us_) / count_, min_us_, max_us_, count_);
    }
  }

private:
  std::chrono::steady_clock::time_point last_;
  long count_ = 0;
  long total_us_ = 0;
  long max_us_ = 0;
  long min_us_ = std::numeric_limits<long>::max();
};
```

### TF buffer memory growth

The default `tf2_ros::Buffer` stores transform history with a 10-second window. If transforms are published at high frequency (e.g., 100 Hz for 50 frames), the buffer can grow significantly. Control with `cache_time`:

```cpp
// Limit TF buffer to 5 seconds of history (default is 10s)
auto tf_buffer = std::make_shared<tf2_ros::Buffer>(
  this->get_clock(),
  tf2::Duration(std::chrono::seconds(5)));
```

```python
# Python equivalent
from tf2_ros import Buffer
tf_buffer = Buffer(cache_time=rclpy.duration.Duration(seconds=5))
```

### rclpy reference cycle debugging

Python nodes that create circular references between callbacks and node state can cause memory leaks that the garbage collector delays collecting:

```python
import gc
import sys
gc.set_debug(gc.DEBUG_SAVEALL)  # Track uncollectable objects

# After a period of operation:
gc.collect()
for obj in gc.garbage:
    print(type(obj), sys.getrefcount(obj))
```

Common rclpy leak: storing `self` references in lambda callbacks that are stored as node members, creating `Node -> callback -> Node` cycles. Use `weakref` or explicit cleanup in `destroy_node()`.

## 5. rosbag2 recording and playback

### Recording

```bash
# Record all topics
ros2 bag record -a -o my_bag

# Record specific topics
ros2 bag record -o sensor_data \
  /joint_states /scan /imu/data /tf /tf_static

# Record with compression
ros2 bag record -o compressed_bag \
  --compression-mode message \
  --compression-format zstd \
  /camera/image_raw /scan

# Record with max size and duration
ros2 bag record -o bounded_bag \
  --max-bag-size 1000000000 \
  --max-bag-duration 300 \
  /scan
```

### Playback

```bash
# Basic playback
ros2 bag play my_bag

# Play with simulated time (required for use_sim_time nodes)
ros2 bag play my_bag --clock

# Play at half speed
ros2 bag play my_bag --rate 0.5

# Play specific topics only
ros2 bag play my_bag --topics /scan /tf

# Loop playback
ros2 bag play my_bag --loop

# Start from specific timestamp
ros2 bag play my_bag --start-offset 10.5
```

### Bag inspection

```bash
# Bag metadata
ros2 bag info my_bag

# Output:
# Files:             my_bag_0.db3
# Bag size:          150.2 MiB
# Duration:          30.5s
# Messages:          15234
# Topic information:
#   /scan          5000 msgs  : sensor_msgs/msg/LaserScan
#   /joint_states  15000 msgs : sensor_msgs/msg/JointState
#   /tf            5000 msgs  : tf2_msgs/msg/TFMessage
```

### Programmatic bag processing (Python)

```python
from rosbag2_py import SequentialReader, StorageOptions, ConverterOptions
from rclpy.serialization import deserialize_message
from sensor_msgs.msg import LaserScan

reader = SequentialReader()
storage_options = StorageOptions(
    uri='my_bag',
    storage_id='mcap')  # MCAP is the default format since Jazzy; use 'sqlite3' for Humble compatibility
converter_options = ConverterOptions(
    input_serialization_format='cdr',
    output_serialization_format='cdr')
reader.open(storage_options, converter_options)

while reader.has_next():
    topic, data, timestamp = reader.read_next()
    if topic == '/scan':
        msg = deserialize_message(data, LaserScan)
        print(f't={timestamp/1e9:.3f}s, ranges={len(msg.ranges)} points')
```

### MCAP format features (Iron+)

MCAP became the default bag format in Iron (and continues in Jazzy/Kilted/Rolling), replacing SQLite3. It offers faster writes, better compression, and indexed random access.

```bash
# Record with MCAP (default in Jazzy+)
ros2 bag record -a -o my_bag

# Record with compression (recommended for production)
ros2 bag record -a -o my_bag --compression-mode file --compression-format zstd

# Inspect MCAP file
ros2 bag info my_bag

# Convert SQLite3 bag to MCAP (requires a YAML config file)
# 1. Create convert_config.yaml:
#    output_bags:
#      - uri: new_bag
#        storage_id: mcap
#        all: true
# 2. Run:
ros2 bag convert -i old_bag -o convert_config.yaml
```

Compression comparison:
| Format | Speed | Ratio | Best for |
|---|---|---|---|
| zstd | Fast write, fast read | ~3-5x | Production recording (default choice) |
| lz4 | Very fast write | ~2-3x | Real-time recording with CPU constraints |
| None | Fastest | 1x | Short recordings, maximum write throughput |

### Foxglove Studio

Foxglove Studio is a modern alternative to rqt for visualization and debugging. It can:
- Open MCAP files directly for offline analysis
- Connect to live ROS 2 systems via Foxglove WebSocket bridge
- Render 3D scenes, plots, images, and diagnostics in a web-based UI
- Share dashboards across teams

```bash
# Install Foxglove bridge for live connection
sudo apt install ros-jazzy-foxglove-bridge
ros2 launch foxglove_bridge foxglove_bridge_launch.xml
# Open https://app.foxglove.dev and connect to ws://localhost:8765
```

## 6. GDB debugging for C++ nodes

### Launch with GDB

```bash
# Attach GDB to a running node
ros2 run --prefix 'gdb -ex run --args' my_robot_driver driver_node

# Or use launch file prefix
Node(
    package='my_robot_driver',
    executable='driver_node',
    prefix=['gdb', '-ex', 'run', '--args'],
    output='screen',
)
```

### Core dump analysis

```bash
# Enable core dumps
ulimit -c unlimited
echo '/tmp/core.%e.%p' | sudo tee /proc/sys/kernel/core_pattern

# After crash, analyze with GDB
gdb /path/to/driver_node /tmp/core.driver_node.12345

# In GDB:
(gdb) bt          # backtrace
(gdb) bt full     # backtrace with variables
(gdb) thread apply all bt  # all thread backtraces
```

### AddressSanitizer (ASan) for memory bugs

```cmake
# Add to CMakeLists.txt for debug builds
if(CMAKE_BUILD_TYPE MATCHES "Debug")
  add_compile_options(-fsanitize=address -fno-omit-frame-pointer)
  add_link_options(-fsanitize=address)
endif()
```

```bash
colcon build --packages-select my_robot_driver \
  --cmake-args -DCMAKE_BUILD_TYPE=Debug
```

## 7. Network and DDS debugging

### Discovery issues

```bash
# Check if nodes can discover each other
ros2 daemon stop && ros2 daemon start

# Verify DDS domain
echo $ROS_DOMAIN_ID

# Check multicast connectivity
ros2 multicast receive &
ros2 multicast send

# CycloneDDS debug logging
export CYCLONEDDS_URI='<CycloneDDS><Domain><Tracing><Verbosity>finest</Verbosity><OutputFile>/tmp/cdds.log</OutputFile></Tracing></Domain></CycloneDDS>'
```

### Common network problems

```bash
# Firewall blocking DDS
sudo ufw allow 7400:7500/udp   # DDS discovery range
sudo ufw allow 7400:7500/tcp

# Check if multicast is enabled on interface
ip maddr show

# Force specific network interface
export CYCLONEDDS_URI='<CycloneDDS><Domain><General><Interfaces><NetworkInterface name="eth0"/></Interfaces></General></Domain></CycloneDDS>'
```

### Localhost-only debugging

```bash
# Isolate from other ROS 2 systems
# Jazzy+ (preferred):
export ROS_AUTOMATIC_DISCOVERY_RANGE=LOCALHOST
# Humble (or Jazzy backward-compatible):
# export ROS_LOCALHOST_ONLY=1  # Deprecated in Jazzy+
export ROS_DOMAIN_ID=42
```

## 8. Common crash patterns and post-mortem analysis

### Segfault in callback (use-after-free)

```
Symptom: Segfault when subscription callback fires after node destruction
Cause: Lambda captures `this` but node is destroyed
Fix: Use weak_from_this() or ensure proper shutdown ordering
```

```cpp
// BAD — captures raw `this`, crashes if node is destroyed
auto sub = create_subscription<Msg>("topic", 10,
  [this](const Msg::SharedPtr msg) { process(msg); });

// GOOD — use weak_ptr to detect destroyed node
auto weak_node = weak_from_this();
auto sub = create_subscription<Msg>("topic", 10,
  [weak_node](const Msg::SharedPtr msg) {
    if (auto node = weak_node.lock()) {
      // Safe — node still exists
    }
  });
```

### Deadlock from synchronous service call

```
Symptom: Node hangs, callbacks stop firing
Cause: Synchronous service call in executor callback
Fix: Use async_send_request with callback
```

### Memory leak from uncleared subscriptions

```
Symptom: Memory grows steadily, node eventually OOM-killed
Cause: Creating subscriptions in callbacks without destroying old ones
Fix: Create all subscriptions in constructor/on_configure, never in callbacks
```

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| "No executable found" for `ros2 run` | Package not built or not sourced | `colcon build`, `source install/setup.bash` |
| Node shows in `ros2 node list` but no topics | Node created but not spinning | Verify `rclcpp::spin()` or executor is running |
| Messages arrive with wrong timestamp | Clock skew between machines | Use NTP/PTP synchronization, or `use_sim_time` with `/clock` |
| `ros2 topic echo` shows nothing | QoS mismatch (echo defaults to RELIABLE) | Use `ros2 topic echo --qos-reliability best_effort` for sensor topics |
| GDB shows `<optimized out>` for variables | Release build | Build with `-DCMAKE_BUILD_TYPE=Debug` or `RelWithDebInfo` |
| Bag playback too fast | Missing `--clock` flag | Add `--clock` and set `use_sim_time: true` on nodes |
| rqt_graph shows disconnected nodes | Nodes on different DDS domains | Verify `ROS_DOMAIN_ID` is the same on all machines |
| valgrind reports leaks in rclcpp | Known ROS 2 library allocations (not true leaks) | Suppress ROS 2 internal allocations, focus on your code |
