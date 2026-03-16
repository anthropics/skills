# Real-Time Constraints

## Table of contents
1. Why real-time matters in robotics
2. PREEMPT_RT kernel setup
3. Thread priority and scheduling
4. Memory allocation strategies
5. Callback group strategies for RT paths
6. Avoiding priority inversion
7. DDS tuning for real-time
8. ros2_control real-time considerations
9. Measuring jitter and latency
10. Common failures and fixes

---

## 1. Why real-time matters in robotics

Real-time does not mean "fast" — it means **deterministic**. A control loop
that runs at 1 kHz with ±50 µs jitter is real-time. A loop that runs at 10
kHz but occasionally stalls for 5 ms is not.

**Where real-time matters:**
- Motor control loops (100–1000 Hz, <100 µs jitter)
- Force/torque feedback (500+ Hz, <50 µs jitter)
- Safety-critical monitoring (e.g., collision detection)
- High-frequency sensor fusion (IMU at 1 kHz)

**Where real-time does NOT matter:**
- Navigation planning (runs at 1–10 Hz, tolerates 50 ms delay)
- Perception pipelines (30 Hz, tolerates 100 ms delay)
- Telemetry and logging
- Parameter configuration

**Rule:** Only apply real-time techniques to the critical path. Over-constraining
the entire system adds complexity without benefit.

## 2. PREEMPT_RT kernel setup

### Installing the RT kernel

```bash
# Ubuntu 22.04 (Humble) / 24.04 (Jazzy)
sudo apt install linux-image-rt-amd64     # Debian-based
# Or install the Ubuntu Pro real-time kernel:
sudo pro attach
sudo pro enable realtime-kernel

# Verify RT kernel is running
uname -a  # Should show "PREEMPT_RT" in kernel version

# Check RT capabilities
cat /sys/kernel/realtime  # Should print "1"
```

### System configuration for RT

```bash
# /etc/security/limits.d/99-realtime.conf
# Allow the robotics user to set RT priorities and lock memory
@realtime   soft    rtprio     99
@realtime   soft    memlock    unlimited
@realtime   hard    rtprio     99
@realtime   hard    memlock    unlimited

# Add user to the realtime group
sudo groupadd -f realtime
sudo usermod -aG realtime $USER
```

### CPU isolation (dedicated cores for RT)

```bash
# /etc/default/grub — isolate CPUs 2 and 3 for RT
GRUB_CMDLINE_LINUX="isolcpus=2,3 nohz_full=2,3 rcu_nocbs=2,3"
sudo update-grub && sudo reboot

# Verify isolation
cat /sys/devices/system/cpu/isolated  # Should show "2-3"
```

## 3. Thread priority and scheduling

### Setting RT scheduling in C++

```cpp
#include <pthread.h>
#include <sched.h>

void set_thread_rt_priority(int priority)
{
  struct sched_param param{};
  param.sched_priority = priority;  // 1 (lowest) to 99 (highest)

  int ret = pthread_setschedparam(pthread_self(), SCHED_FIFO, &param);
  if (ret != 0) {
    // Common failure: insufficient privileges
    // Ensure /etc/security/limits.d/ is configured and user is in realtime group
    std::cerr << "Failed to set RT priority: " << strerror(ret) << std::endl;
  }
}
```

### Priority assignment guidelines

| Component | Priority (SCHED_FIFO) | Rationale |
|---|---|---|
| Safety monitor | 90 | Must never be preempted by control |
| Hardware read/write | 80 | Sensor data and actuator commands |
| Control loop | 70 | Main control computation |
| Sensor fusion | 50 | Pre-processing for control |
| DDS communication | 40 | Network I/O |
| Logging | 10 | Non-critical, runs when idle |

**Never use priority 99** — it can starve kernel threads and watchdogs.

### CPU affinity

```cpp
#include <pthread.h>

void pin_thread_to_cpu(int cpu_id)
{
  cpu_set_t cpuset;
  CPU_ZERO(&cpuset);
  CPU_SET(cpu_id, &cpuset);
  pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
}

// Example: Pin the control thread to isolated CPU 2
pin_thread_to_cpu(2);
set_thread_rt_priority(70);
```

## 4. Memory allocation strategies

### The problem

Dynamic memory allocation (`new`, `malloc`, `std::vector::push_back`) can
trigger page faults and kernel calls with unbounded latency. In a 1 kHz
control loop, a single 100 µs allocation spike breaks determinism.

### Pre-allocation pattern

```cpp
class RTController : public rclcpp::Node
{
public:
  RTController() : Node("rt_controller")
  {
    // Pre-allocate everything in the constructor (non-RT context)
    joint_positions_.resize(NUM_JOINTS, 0.0);
    joint_velocities_.resize(NUM_JOINTS, 0.0);
    joint_commands_.resize(NUM_JOINTS, 0.0);

    // Pre-allocate message
    cmd_msg_ = std::make_unique<trajectory_msgs::msg::JointTrajectoryPoint>();
    cmd_msg_->positions.resize(NUM_JOINTS);
    cmd_msg_->velocities.resize(NUM_JOINTS);

    // Lock memory pages to prevent page faults
    if (mlockall(MCL_CURRENT | MCL_FUTURE) != 0) {
      RCLCPP_WARN(get_logger(), "mlockall failed — RT performance may be degraded");
    }
  }

  ~RTController() override
  {
    munlockall();
  }

private:
  static constexpr size_t NUM_JOINTS = 6;
  std::vector<double> joint_positions_;
  std::vector<double> joint_velocities_;
  std::vector<double> joint_commands_;
  std::unique_ptr<trajectory_msgs::msg::JointTrajectoryPoint> cmd_msg_;
};
```

### Lock-free data structures for RT-safe communication

```cpp
#include <atomic>
#include <array>

// RT-safe double buffer for passing data between RT and non-RT threads
template<typename T>
class RealtimeBuffer
{
public:
  void writeFromNonRT(const T & data)
  {
    *non_rt_data_ = data;
    new_data_available_.store(true, std::memory_order_release);
  }

  T readFromRT()
  {
    if (new_data_available_.load(std::memory_order_acquire)) {
      rt_data_ = *non_rt_data_;
      new_data_available_.store(false, std::memory_order_release);
    }
    return rt_data_;
  }

private:
  std::unique_ptr<T> non_rt_data_ = std::make_unique<T>();
  T rt_data_{};
  std::atomic<bool> new_data_available_{false};
};
```

### What to avoid in the RT path

| Operation | Latency risk | Alternative |
|---|---|---|
| `new` / `delete` / `malloc` / `free` | 10–1000 µs | Pre-allocate, use pool allocators |
| `std::vector::push_back` (may reallocate) | 10–500 µs | Pre-allocate with `reserve()`, use fixed arrays |
| `std::string` construction | 5–100 µs | Use `std::string_view` or pre-allocated strings |
| `std::shared_ptr` creation | 5–50 µs | Use raw pointers or pre-existing shared_ptrs |
| File I/O / logging | 100–10000 µs | Log to a lock-free queue, flush from non-RT thread |
| `std::mutex::lock` | Unbounded (priority inversion) | Use `rt_mutex` or lock-free algorithms |
| System calls (`read`, `write`) | 1–10000 µs | Use non-blocking I/O, poll from non-RT thread |

## 5. Callback group strategies for RT paths

### Separating RT and non-RT callbacks

```cpp
class RTControlNode : public rclcpp::Node
{
public:
  RTControlNode() : Node("rt_control")
  {
    // High-priority group for control loop — MutuallyExclusive to prevent
    // concurrent access to control state
    rt_group_ = create_callback_group(
      rclcpp::CallbackGroupType::MutuallyExclusive);

    // Low-priority group for diagnostics, parameters, etc.
    non_rt_group_ = create_callback_group(
      rclcpp::CallbackGroupType::Reentrant);

    // Control timer at 500 Hz — in RT group
    rclcpp::SubscriptionOptions rt_opts;
    rt_opts.callback_group = rt_group_;
    joint_state_sub_ = create_subscription<JointState>(
      "joint_states", rclcpp::SensorDataQoS(),
      std::bind(&RTControlNode::control_callback, this, std::placeholders::_1),
      rt_opts);

    // Diagnostics at 1 Hz — in non-RT group
    rclcpp::SubscriptionOptions non_rt_opts;
    non_rt_opts.callback_group = non_rt_group_;
    diag_timer_ = create_wall_timer(
      std::chrono::seconds(1),
      std::bind(&RTControlNode::publish_diagnostics, this),
      non_rt_group_);
  }

private:
  void control_callback(const JointState::ConstSharedPtr msg)
  {
    // This runs in the RT thread — no allocations, no blocking
    update_control(msg);
    send_commands();
  }

  void publish_diagnostics()
  {
    // This runs in the non-RT thread — can allocate, log, etc.
  }

  rclcpp::CallbackGroup::SharedPtr rt_group_;
  rclcpp::CallbackGroup::SharedPtr non_rt_group_;
  rclcpp::Subscription<JointState>::SharedPtr joint_state_sub_;
  rclcpp::TimerBase::SharedPtr diag_timer_;
};
```

### Custom RT executor

```cpp
class RTExecutor
{
public:
  void run(rclcpp::Node::SharedPtr node,
           rclcpp::CallbackGroup::SharedPtr rt_group,
           int rt_priority, int cpu_id)
  {
    // Create a separate single-threaded executor for the RT group
    rclcpp::executors::SingleThreadedExecutor rt_executor;
    rt_executor.add_callback_group(rt_group, node->get_node_base_interface());

    // Run on dedicated thread with RT priority
    rt_thread_ = std::thread([&rt_executor, rt_priority, cpu_id]() {
      set_thread_rt_priority(rt_priority);
      pin_thread_to_cpu(cpu_id);
      rt_executor.spin();
    });
  }

private:
  std::thread rt_thread_;
};
```

## 6. Avoiding priority inversion

Priority inversion occurs when a high-priority RT thread blocks waiting for a
lock held by a low-priority non-RT thread, which in turn is preempted by a
medium-priority thread.

### Use priority-inheritance mutexes

```cpp
#include <pthread.h>
#include <mutex>

// Create a mutex with priority inheritance protocol
pthread_mutex_t create_pi_mutex()
{
  pthread_mutex_t mutex;
  pthread_mutexattr_t attr;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_setprotocol(&attr, PTHREAD_PRIO_INHERIT);
  pthread_mutex_init(&mutex, &attr);
  pthread_mutexattr_destroy(&attr);
  return mutex;
}
```

### Prefer lock-free designs

In the RT path, avoid mutexes entirely where possible:
- Use `std::atomic` for simple shared state
- Use lock-free queues for producer/consumer patterns
- Use double-buffering (RT reads buffer A, non-RT writes buffer B, swap atomically)

## 7. DDS tuning for real-time

### CycloneDDS for low latency

```xml
<!-- cyclonedds_rt.xml -->
<CycloneDDS xmlns="https://cdds.io/config">
  <Domain>
    <General>
      <Interfaces>
        <NetworkInterface name="eth0"/>
      </Interfaces>
    </General>
    <Internal>
      <!-- Pre-allocate receive buffers -->
      <SocketReceiveBufferSize min="4MB"/>
      <!-- Reduce discovery overhead -->
      <LeaseDuration>20s</LeaseDuration>
    </Internal>
    <Scheduling>
      <!-- Set DDS thread priorities (below control loop) -->
      <Class>Realtime</Class>
      <Priority>40</Priority>
    </Scheduling>
  </Domain>
</CycloneDDS>
```

### Minimize DDS overhead

- Use `BEST_EFFORT` QoS for sensor data (no ACK overhead)
- Use intra-process communication for co-located nodes
- Limit discovery scope with `ROS_DOMAIN_ID` and `ROS_LOCALHOST_ONLY`
- Use shared memory transport (Jazzy+) to bypass the network stack entirely

## 8. ros2_control real-time considerations

The `controller_manager` in ros2_control runs `read()` → `update()` → `write()`
in a tight loop at the configured `update_rate`. This loop must be deterministic.

### RT-safe read/write

```cpp
// In your hardware interface — RT-critical path
hardware_interface::return_type MyHardware::read(
  const rclcpp::Time &, const rclcpp::Duration &)
{
  // NO allocations, NO logging (except throttled), NO blocking calls
  // Read directly from pre-allocated buffers
  auto data = serial_buffer_.load(std::memory_order_acquire);
  for (size_t i = 0; i < num_joints_; ++i) {
    set_state(joint_names_[i] + "/position", data.positions[i]);
    set_state(joint_names_[i] + "/velocity", data.velocities[i]);
  }
  return hardware_interface::return_type::OK;
}
```

### Offloading serial I/O from the RT thread

```cpp
// Non-RT thread reads serial, stores in atomic buffer
void io_thread_func()
{
  while (running_) {
    auto frame = serial_.read_frame(std::chrono::milliseconds(5));
    if (frame) {
      SensorData data = parse_frame(*frame);
      serial_buffer_.store(data, std::memory_order_release);
    }
  }
}

// RT thread (read()) just loads from the atomic buffer — never blocks
```

### Controller manager RT settings

```yaml
controller_manager:
  ros__parameters:
    update_rate: 500        # Hz
    # On PREEMPT_RT kernel with isolated CPUs:
    # The controller_manager thread can be pinned to a specific CPU
    # via launch file or systemd service configuration
```

## 9. Measuring jitter and latency

### cyclictest (baseline kernel latency)

```bash
# Install
sudo apt install rt-tests

# Run cyclictest on isolated CPU core
sudo cyclictest -t1 -p 80 -n -i 1000 -l 10000 -a 2
# -t1: 1 thread
# -p 80: priority 80
# -n: use nanosleep
# -i 1000: interval 1000µs (1kHz)
# -l 10000: 10000 loops
# -a 2: pin to CPU 2

# Target: max latency < 50µs on PREEMPT_RT
# Standard kernel: max latency 100–10000µs
```

### Measuring ros2_control loop jitter

```cpp
// Add timing instrumentation to your hardware interface
hardware_interface::return_type MyHardware::read(
  const rclcpp::Time & time, const rclcpp::Duration & period)
{
  auto now = std::chrono::steady_clock::now();
  if (last_read_time_.time_since_epoch().count() > 0) {
    auto dt = std::chrono::duration_cast<std::chrono::microseconds>(
      now - last_read_time_).count();
    auto expected = 1000000.0 / update_rate_;
    auto jitter = std::abs(dt - expected);
    max_jitter_us_ = std::max(max_jitter_us_, jitter);
  }
  last_read_time_ = now;
  // ... actual read logic ...
}
```

### ros2_tracing for latency analysis

```bash
# Enable tracing (requires ros2_tracing package)
ros2 trace start my_trace -e ros2:*

# Run your system
ros2 launch my_robot_bringup robot.launch.py

# Stop tracing
ros2 trace stop my_trace

# Analyze with ros2_tracing tools or LTTng
```

## 10. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Occasional 1–10 ms latency spikes | Page faults from dynamic allocation | Use `mlockall()`, pre-allocate all buffers |
| Periodic jitter every 1 second | CPU frequency scaling | Set governor to `performance`: `cpupower frequency-set -g performance` |
| RT thread starved by non-RT work | Not using isolated CPUs | Isolate CPUs with `isolcpus` kernel parameter |
| "Operation not permitted" on `sched_setscheduler` | Missing RT privileges | Configure `/etc/security/limits.d/`, add user to `realtime` group |
| Control loop overshoots under load | Priority inversion on mutex | Use `PTHREAD_PRIO_INHERIT`, or replace mutex with lock-free design |
| DDS adds unpredictable latency | Network stack interference | Use intra-process or shared memory transport for local communication |
| Logging causes jitter | `RCLCPP_INFO` allocates strings | Use `RCLCPP_INFO_THROTTLE` or log from non-RT thread via lock-free queue |
| USB serial drops frames | USB polling interval too high | Set `usbcore.autosuspend=-1`, use low-latency serial settings |
