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
10. Hardware-level RT pitfalls (CPU freq, clock sources, NUMA, IRQ affinity)
11. Common failures and fixes

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
sudo apt install linux-image-rt-generic
# On Ubuntu Pro, use `sudo pro enable realtime-kernel` instead.

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
# x86/amd64 (GRUB bootloader):
# /etc/default/grub — isolate CPUs 2 and 3 for RT
GRUB_CMDLINE_LINUX="isolcpus=2,3 nohz_full=2,3 rcu_nocbs=2,3"
sudo update-grub && sudo reboot

# NVIDIA Jetson (U-Boot/extlinux):
# Edit /boot/extlinux/extlinux.conf, add to APPEND line:
# isolcpus=2,3 nohz_full=2,3 rcu_nocbs=2,3

# Raspberry Pi (config.txt + cmdline.txt):
# Edit /boot/firmware/cmdline.txt, append:
# isolcpus=2,3 nohz_full=2,3 rcu_nocbs=2,3

# Verify isolation (all platforms)
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

    // Lock memory pages to prevent page faults.
    // WARNING: MCL_FUTURE locks ALL future allocations. If the process exceeds
    // the RLIMIT_MEMLOCK limit, mlockall fails and subsequent mmap/malloc may
    // also fail. Always check limits before calling.
    struct rlimit mem_limit;
    getrlimit(RLIMIT_MEMLOCK, &mem_limit);
    if (mem_limit.rlim_cur != RLIM_INFINITY) {
      RCLCPP_WARN(get_logger(),
        "RLIMIT_MEMLOCK is %lu bytes (not unlimited). "
        "Set memlock=unlimited in /etc/security/limits.d/ for RT.",
        mem_limit.rlim_cur);
    }
    if (mlockall(MCL_CURRENT | MCL_FUTURE) != 0) {
      RCLCPP_WARN(get_logger(), "mlockall failed (errno=%d) — RT performance may be degraded",
                  errno);
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

// Simplified RT-safe flag for passing data between RT and non-RT threads.
// WARNING: This is a simplified illustration. It has a race condition for
// non-trivially-copyable types (non-RT can overwrite while RT is copying).
// Use realtime_tools::RealtimeBuffer (below) in production.
template<typename T>
class SimpleRealtimeFlag
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

### realtime_tools library (ros2_control) — recommended

The `realtime_tools` package from ros2_control provides production-ready RT-safe primitives
using a proper triple-buffer scheme. **Always prefer these over custom implementations:**

```cpp
// From ros2_control's realtime_tools package
#include <realtime_tools/realtime_buffer.hpp>
#include <realtime_tools/realtime_publisher.hpp>

// RT-safe publisher — buffers messages and publishes from a non-RT thread
realtime_tools::RealtimePublisher<sensor_msgs::msg::JointState> rt_pub(
  node->create_publisher<sensor_msgs::msg::JointState>("joint_states", 10));

// In RT callback:
if (rt_pub.trylock()) {
  rt_pub.msg_.header.stamp = now;
  rt_pub.msg_.position = current_positions;
  rt_pub.unlockAndPublish();
}

// RT-safe buffer — lock-free data sharing between RT and non-RT threads
realtime_tools::RealtimeBuffer<geometry_msgs::msg::Twist> cmd_buf;
// Non-RT thread writes:
cmd_buf.writeFromNonRT(twist_msg);
// RT thread reads:
auto cmd = *cmd_buf.readFromRT();
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
    // Executor must outlive the thread — store as member
    rt_executor_ = std::make_unique<rclcpp::executors::SingleThreadedExecutor>();
    rt_executor_->add_callback_group(rt_group, node->get_node_base_interface());

    // Run on dedicated thread with RT priority
    rt_thread_ = std::thread([this, rt_priority, cpu_id]() {
      set_thread_rt_priority(rt_priority);
      pin_thread_to_cpu(cpu_id);
      rt_executor_->spin();
    });
  }

  ~DualExecutorRunner()
  {
    if (rt_executor_) { rt_executor_->cancel(); }
    if (rt_thread_.joinable()) { rt_thread_.join(); }
  }

private:
  std::unique_ptr<rclcpp::executors::SingleThreadedExecutor> rt_executor_;
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
- Limit discovery scope with `ROS_DOMAIN_ID` and `ROS_AUTOMATIC_DISCOVERY_RANGE=LOCALHOST`
  (Jazzy+; replaces deprecated `ROS_LOCALHOST_ONLY`)
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

### Benchmark reference numbers

These are **order-of-magnitude reference numbers** from published benchmarks on
specific hardware (Intel i7-12700, Ubuntu 24.04). Your numbers **will differ** based
on CPU, kernel version, BIOS settings, and workload. Always benchmark on your target
platform — never assume these numbers transfer directly.

| Metric | Without PREEMPT_RT | With PREEMPT_RT |
|---|---|---|
| cyclictest max latency (1kHz, 10 min) | 50-500 us, spikes to 10+ ms | 8-15 us |
| cyclictest avg latency | 2-5 us | 1-3 us |
| Worst-case jitter (p99.9) | 200-2000 us | 10-20 us |

DDS transport latency (loopback, **1 KB message** — small messages only):

| Middleware | Avg latency | p99 latency |
|---|---|---|
| CycloneDDS | ~30-60 us | ~100-200 us |
| FastDDS | ~40-80 us | ~150-300 us |
| Zenoh | ~20-40 us | ~60-120 us |
| Intra-process (zero-copy) | ~1-5 us | ~5-10 us |

**Large message scaling:** For `PointCloud2` (~1.5 MB) or `Image` (~900 KB), multiply
the above numbers by 50–100x due to serialization, fragmentation, and reassembly.
For large messages on the RT path, intra-process or shared memory transport is
effectively mandatory.

### Tail latency (p99/p999)

**Tail latency matters more than mean.** For safety-critical control loops, a 1ms average with occasional 50ms spikes is worse than a 5ms average with 7ms p99.9. Always measure and report p99.9 latency:

```bash
# cyclictest with histogram output for tail latency analysis
sudo cyclictest -l 100000 -m -S -p 90 -i 1000 -h 400 -q > histogram.txt
# Analyze: sort histogram, find the latency at 99.9th percentile
```

## 10. Hardware-level RT pitfalls

These low-level factors are invisible in application code but dominate tail latency
in production. A 20-year veteran will check these before any software optimization.

### CPU frequency scaling and turbo boost

Dynamic frequency scaling introduces **10–100 ms** latency spikes when the CPU
transitions between P-states. Turbo Boost causes frequency drops when thermal
limits are hit, creating non-deterministic jitter.

```bash
# Lock CPU frequency to maximum — REQUIRED for RT
sudo cpupower frequency-set -g performance

# Disable turbo boost (Intel)
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo

# Disable turbo boost (AMD)
echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost

# Verify — all cores should show the same fixed frequency
cpupower frequency-info | grep "current CPU frequency"

# Make persistent via systemd service or /etc/rc.local
```

**Why this matters:** Without this, a 1 kHz control loop that normally hits 5 µs
jitter will randomly spike to 10+ ms when the governor transitions. This is the
**single most common cause** of "works on the bench, fails in production" RT issues.

### Clock sources

The kernel clock source affects timestamp accuracy and `clock_gettime()` latency,
which directly impacts `cyclictest` results and ROS 2 timer precision.

```bash
# Check current clock source
cat /sys/devices/system/clocksource/clocksource0/current_clocksource
# Typically: tsc (best), hpet (acceptable), acpi_pm (slow)

# Check available sources
cat /sys/devices/system/clocksource/clocksource0/available_clocksource

# Force TSC if available (lowest overhead, ~20ns per read)
# In GRUB: GRUB_CMDLINE_LINUX="... clocksource=tsc tsc=reliable"
```

| Clock source | Read latency | Notes |
|---|---|---|
| TSC | ~20 ns | Best choice. Requires invariant TSC (all modern x86 CPUs) |
| HPET | ~500 ns | Acceptable fallback. Some BIOSes disable it |
| ACPI_PM | ~1000 ns | Slow. Avoid for RT |
| `arch_sys_counter` (ARM) | ~40 ns | Default on ARM64, good for Jetson/Pi |

If `cyclictest` shows good latency but your ROS 2 nodes show jitter, check the
clock source first — a slow clock source adds overhead to every `now()` call.

### NUMA awareness (multi-socket systems)

On dual-socket servers (common in industrial controllers), memory access across
NUMA nodes adds **50–200 ns per access**. If the RT thread runs on CPU socket 0
but its data (state interfaces, command buffers) is allocated on socket 1, every
`read()`/`write()` cycle pays this penalty, creating 10x worse jitter.

```bash
# Check NUMA topology
numactl --hardware

# Pin RT process to a specific NUMA node
numactl --cpunodebind=0 --membind=0 ros2 launch my_robot control.launch.py

# In code: allocate RT buffers on the same node as the RT thread
#include <numa.h>
void* rt_buffer = numa_alloc_onnode(size, 0);  // Allocate on node 0
```

**Rule of thumb:** Pin the RT executor thread and all its data to the same NUMA
node. This is irrelevant on single-socket systems (most robots), but critical for
server-grade or multi-socket industrial controllers.

### IRQ affinity

Hardware interrupts (especially from network cards and serial controllers) can
preempt RT threads, causing latency spikes. Move IRQs off isolated RT cores:

```bash
# Move all IRQs to CPU 0 (non-RT core)
for irq in /proc/irq/*/smp_affinity_list; do
  echo 0 | sudo tee "$irq" 2>/dev/null || true
done

# Verify no IRQs are firing on isolated cores
watch -n 1 cat /proc/interrupts
```

## 11. Common failures and fixes

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
| Random 10-100 ms spikes | CPU frequency scaling / turbo boost | Set governor to `performance`, disable turbo (see section 10) |
| Good cyclictest but bad ROS jitter | Slow clock source (HPET/ACPI_PM) | Switch to TSC: `clocksource=tsc tsc=reliable` in kernel cmdline |
| Latency worse on multi-socket server | NUMA cross-node memory access | Pin RT thread + data to same NUMA node with `numactl` |
| Sporadic spikes from network IRQs | IRQs firing on isolated RT cores | Move IRQ affinity off RT cores (see section 10) |
