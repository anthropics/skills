# Micro-ROS

## Table of contents
1. Architecture overview
2. Supported platforms and RTOSes
3. micro_ros_agent setup
4. rclc executor and programming model
5. Memory management on microcontrollers
6. Custom messages and type support
7. Transport layers
8. Production deployment patterns
9. Common failures and fixes

---

## 1. Architecture overview

```
+----------------------------+     +----------------------------+
|   ROS 2 Host (Linux)       |     |   Microcontroller (MCU)    |
|  +----------------------+  |     |  +----------------------+  |
|  |  Standard ROS 2      |  |     |  |   micro-ROS App      |  |
|  |  Nodes               |  |     |  |   (rclc API)         |  |
|  +----------+-----------+  |     |  +----------+-----------+  |
|             |              |     |             |              |
|  +----------v-----------+  |     |  +----------v-----------+  |
|  |  DDS / Zenoh          |  |     |  |  Micro XRCE-DDS     |  |
|  +----------+-----------+  |     |  |  Client              |  |
|             |              |     |  +----------+-----------+  |
|  +----------v-----------+  |     |             |              |
|  |  micro_ros_agent      |<-+-----+-------------+              |
|  |  (XRCE-DDS Agent)    |  |     |  Transport: Serial/UDP/USB |
|  +-----------------------+  |     |                            |
+----------------------------+     +----------------------------+
```

Key concepts:
- micro-ROS runs on the MCU using the `rclc` C API (not rclcpp/rclpy).
- The `micro_ros_agent` on the host bridges XRCE-DDS to full DDS (or Zenoh from Jazzy).
- Communication goes through a transport layer (serial UART, UDP over WiFi, USB CDC).
- The MCU node appears as a normal node on the ROS 2 graph. Standard CLI tools (`ros2 topic list`, `ros2 node info`) work transparently.
- XRCE-DDS overhead is 10-20 bytes per message beyond the serialized payload.
- One agent process can multiplex many MCU clients simultaneously.

Always match the micro-ROS branch to your ROS 2 distro. Mixing versions causes serialization failures or agent segfaults.

| ROS 2 Distro | micro-ROS Branch | Status      |
|--------------|------------------|-------------|
| Humble       | humble           | LTS, stable |
| Jazzy        | jazzy            | Latest LTS  |
| Kilted       | kilted           | Non-LTS, current |
| Rolling      | rolling          | Development |

---

## 2. Supported platforms and RTOSes

| MCU / Board               | RTOS              | Transport          | Notes                                  |
|---------------------------|-------------------|--------------------|----------------------------------------|
| ESP32 / ESP32-S3          | FreeRTOS (ESP-IDF)| WiFi (UDP), Serial | Most popular, built-in WiFi            |
| STM32F4/F7/H7             | FreeRTOS / Zephyr | Serial (UART), USB | Industrial-grade, deterministic        |
| Raspberry Pi Pico (RP2040)| FreeRTOS          | Serial, USB        | Low-cost, dual-core Cortex-M0+         |
| Teensy 4.x (i.MX RT)     | NuttX / FreeRTOS  | Serial, USB        | High-speed 600 MHz ARM Cortex-M7      |
| Renesas RA                | FreeRTOS          | Serial, Ethernet   | Industrial IoT                         |
| Linux (native)            | Linux (POSIX)     | UDP, Serial        | For testing micro-ROS apps on host     |

### Platform setup (ESP32 + FreeRTOS example)

```bash
mkdir -p ~/microros_ws/src
cd ~/microros_ws/src
git clone -b $ROS_DISTRO https://github.com/micro-ROS/micro_ros_setup.git
cd ~/microros_ws
rosdep update && rosdep install --from-paths src --ignore-src -y
colcon build --symlink-install
source install/setup.bash

ros2 run micro_ros_setup create_firmware_ws.sh freertos esp32
ros2 run micro_ros_setup configure_firmware.sh int32_publisher --transport serial
ros2 run micro_ros_setup build_firmware.sh
ros2 run micro_ros_setup flash_firmware.sh
```

---

## 3. micro_ros_agent setup

```bash
# Binary install
sudo apt install ros-jazzy-micro-ros-agent   # or ros-humble-micro-ros-agent

# Serial transport (most common)
ros2 run micro_ros_agent micro_ros_agent serial --dev /dev/ttyUSB0 -b 115200

# Higher baud rate for high-frequency sensors
ros2 run micro_ros_agent micro_ros_agent serial --dev /dev/ttyUSB0 -b 921600

# UDP transport (WiFi-enabled MCUs)
ros2 run micro_ros_agent micro_ros_agent udp4 --port 8888

# USB CDC
ros2 run micro_ros_agent micro_ros_agent serial --dev /dev/ttyACM0 -b 115200

# Verbose debugging
ros2 run micro_ros_agent micro_ros_agent serial --dev /dev/ttyUSB0 -b 115200 -v6
```

Agent in a launch file:

```python
from launch import LaunchDescription
from launch.actions import DeclareLaunchArgument, ExecuteProcess
from launch.substitutions import LaunchConfiguration

def generate_launch_description():
    return LaunchDescription([
        DeclareLaunchArgument('device', default_value='/dev/ttyUSB0'),
        DeclareLaunchArgument('baudrate', default_value='115200'),
        ExecuteProcess(
            cmd=['ros2', 'run', 'micro_ros_agent', 'micro_ros_agent',
                 'serial', '--dev', LaunchConfiguration('device'),
                 '-b', LaunchConfiguration('baudrate')],
            output='screen',
        ),
    ])
```

Serial port permissions:

```bash
sudo usermod -a -G dialout $USER   # log out/in after this
```

---

## 4. rclc executor and programming model

### Complete publisher node (ESP32 + FreeRTOS)

```c
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <esp_timer.h>
#include <rcl/rcl.h>
#include <rcl/error_handling.h>
#include <rclc/rclc.h>
#include <rclc/executor.h>
#include <sensor_msgs/msg/imu.h>

#define RCCHECK(fn) { rcl_ret_t rc = fn; if (rc != RCL_RET_OK) { error_loop(); } }
#define RCSOFTCHECK(fn) { rcl_ret_t rc = fn; if (rc != RCL_RET_OK) { \
    printf("RCSOFTCHECK: %s:%d rc=%d\n", __FILE__, __LINE__, (int)rc); } }

static void error_loop(void) { while (1) { vTaskDelay(pdMS_TO_TICKS(1000)); } }

static rcl_publisher_t imu_publisher;
static sensor_msgs__msg__Imu imu_msg;
static rcl_timer_t timer;

void timer_callback(rcl_timer_t * timer, int64_t last_call_time)
{
    (void)last_call_time;
    read_imu_sensor(&imu_msg);
    int64_t time_us = esp_timer_get_time();
    imu_msg.header.stamp.sec = (int32_t)(time_us / 1000000);
    imu_msg.header.stamp.nanosec = (uint32_t)((time_us % 1000000) * 1000);
    RCSOFTCHECK(rcl_publish(&imu_publisher, &imu_msg, NULL));
}

void micro_ros_task(void * arg)
{
    rcl_allocator_t allocator = rcl_get_default_allocator();
    rclc_support_t support;
    RCCHECK(rclc_support_init(&support, 0, NULL, &allocator));

    rcl_node_t node;
    RCCHECK(rclc_node_init_default(&node, "imu_sensor_node", "", &support));

    RCCHECK(rclc_publisher_init_best_effort(
        &imu_publisher, &node,
        ROSIDL_GET_MSG_TYPE_SUPPORT(sensor_msgs, msg, Imu), "imu/data_raw"));

    RCCHECK(rclc_timer_init_default(&timer, &support, RCL_MS_TO_NS(10), timer_callback));

    rclc_executor_t executor;
    RCCHECK(rclc_executor_init(&executor, &support.context, 1, &allocator));
    RCCHECK(rclc_executor_add_timer(&executor, &timer));

    while (1) {
        RCSOFTCHECK(rclc_executor_spin_some(&executor, RCL_MS_TO_NS(100)));
        vTaskDelay(pdMS_TO_TICKS(1));
    }
}

void app_main(void)
{
    xTaskCreate(micro_ros_task, "micro_ros_task", 16384, NULL, 5, NULL);
}
```

### Subscriber example

```c
#include <geometry_msgs/msg/twist.h>

static rcl_subscription_t twist_sub;
static geometry_msgs__msg__Twist twist_msg;

void twist_callback(const void * msgin)
{
    const geometry_msgs__msg__Twist * msg = (const geometry_msgs__msg__Twist *)msgin;
    set_motor_speeds(msg->linear.x, msg->angular.z);
}

// After node creation:
RCCHECK(rclc_subscription_init_default(
    &twist_sub, &node,
    ROSIDL_GET_MSG_TYPE_SUPPORT(geometry_msgs, msg, Twist), "cmd_vel"));

rclc_executor_t executor;
RCCHECK(rclc_executor_init(&executor, &support.context, 1, &allocator));
RCCHECK(rclc_executor_add_subscription(
    &executor, &twist_sub, &twist_msg, &twist_callback, ON_NEW_DATA));
```

Key differences from rclcpp/rclpy:
- No dynamic allocation after initialization.
- Must specify exact number of handles in executor.
- Use `rclc_executor_spin_some()` (not `spin()`) to cooperate with the RTOS scheduler.
- Error handling uses C-style return codes, not exceptions.
- Use `_init_best_effort` for sensor streams, `_init_default` (RELIABLE) for commands.
- `ON_NEW_DATA` fires the callback only when new data arrives; `ALWAYS` fires every spin.

---

## 5. Memory management on microcontrollers

micro-ROS uses static memory allocation. Dynamic allocation happens only during initialization, never at runtime.

### Message memory configuration

```c
#include <micro_ros_utilities/type_utilities.h>
#include <micro_ros_utilities/string_utilities.h>

static micro_ros_utilities_memory_conf_t conf = {
    .max_string_capacity = 50,
    .max_ros2_type_sequence_capacity = 5,
    .max_basic_type_sequence_capacity = 100
};

// Inside a function (e.g., app_main):
bool ok = micro_ros_utilities_create_message_memory(
    ROSIDL_GET_MSG_TYPE_SUPPORT(sensor_msgs, msg, Imu), &imu_msg, conf);
if (!ok) { error_loop(); }
```

### Middleware memory pools (build-time, in colcon.meta)

```json
{
    "names": {
        "rmw_microxrcedds": {
            "cmake-args": [
                "-DRMW_UXRCE_MAX_NODES=1",
                "-DRMW_UXRCE_MAX_PUBLISHERS=10",
                "-DRMW_UXRCE_MAX_SUBSCRIPTIONS=5",
                "-DRMW_UXRCE_MAX_SERVICES=1",
                "-DRMW_UXRCE_MAX_CLIENTS=1",
                "-DRMW_UXRCE_MAX_HISTORY=4"
            ]
        }
    }
}
```

Exceeding these limits causes silent failures: entities appear created but never send or receive data.

### Memory budgets

| MCU         | RAM    | Flash  | micro-ROS RAM  | micro-ROS Flash  |
|-------------|--------|--------|----------------|------------------|
| ESP32       | 520 KB | 4 MB   | 100-200 KB     | 800 KB - 1.2 MB  |
| STM32F4     | 192 KB | 512 KB | 80-150 KB      | 400 KB           |
| STM32H7     | 1 MB   | 2 MB   | 80-150 KB      | 400-600 KB       |
| RP2040      | 264 KB | 2 MB   | 100-180 KB     | 600-900 KB       |

Each additional publisher/subscriber costs approximately 1-3 KB RAM. Task stack should be at least 16 KB (32 KB for complex messages like PointCloud2).

---

## 6. Custom messages and type support

Constraints on MCU message types:
- No unbounded sequences (arrays must have fixed or bounded size).
- No unbounded strings (all string fields consume `max_string_capacity` bytes).
- Nested messages multiply memory requirements at every level.

```
# extra_packages/my_robot_msgs/msg/SensorReading.msg
std_msgs/Header header
uint32 sensor_id
float32[6] joint_positions    # Fixed-size -- OK
float32[] motor_currents      # Variable-length -- needs max_basic_type_sequence_capacity
string frame_name             # Variable string -- needs max_string_capacity
uint8 status
```

Build custom messages into firmware:

```bash
mkdir -p firmware/mcu_ws/extra_packages
cp -r ~/my_robot_msgs firmware/mcu_ws/extra_packages/
ros2 run micro_ros_setup build_firmware.sh
ros2 run micro_ros_setup flash_firmware.sh
```

Using custom messages in code:

```c
#include <my_robot_msgs/msg/sensor_reading.h>

static my_robot_msgs__msg__SensorReading sensor_msg;

micro_ros_utilities_memory_conf_t conf = {0};
conf.max_string_capacity = 32;
conf.max_basic_type_sequence_capacity = 10;
micro_ros_utilities_create_message_memory(
    ROSIDL_GET_MSG_TYPE_SUPPORT(my_robot_msgs, msg, SensorReading), &sensor_msg, conf);

sensor_msg.joint_positions[0] = 1.57f;
sensor_msg.motor_currents.size = 3;
sensor_msg.motor_currents.data[0] = 0.5f;

const char * frame = "base_link";
memcpy(sensor_msg.frame_name.data, frame, strlen(frame));
sensor_msg.frame_name.size = strlen(frame);
```

---

## 7. Transport layers

### Serial (UART)
Most reliable. Direct wired connection, no packet loss, deterministic latency.

| Use case                       | Recommended baud |
|--------------------------------|------------------|
| Single topic, 10 Hz, small msg | 115200           |
| IMU at 100 Hz                  | 460800           |
| IMU + encoders + commands      | 921600           |

### UDP (WiFi)
ESP32 native WiFi. Higher latency, potential packet loss. Use `BEST_EFFORT` QoS only. Keep messages under 1400 bytes (MTU). Not suitable for safety-critical control loops.

### USB CDC
Lower latency than UART, higher throughput. Devices appear as `/dev/ttyACM*`. Works with Teensy, STM32 OTG, RP2040 native USB.

### Custom transport
Implement `open`, `close`, `write`, `read` callbacks for CAN, Bluetooth, SPI, etc.:

```c
#include <uxr/client/transport.h>

bool my_transport_open(struct uxrCustomTransport * transport) { return hardware_init(); }
bool my_transport_close(struct uxrCustomTransport * transport) { return hardware_deinit(); }

size_t my_transport_write(struct uxrCustomTransport * transport,
    const uint8_t * buf, size_t len, uint8_t * err)
{
    ssize_t written = hardware_send(buf, len);
    if (written < 0) { *err = 1; return 0; }
    return (size_t)written;
}

size_t my_transport_read(struct uxrCustomTransport * transport,
    uint8_t * buf, size_t len, int timeout, uint8_t * err)
{
    ssize_t received = hardware_receive(buf, len, timeout);
    if (received < 0) { *err = 1; return 0; }
    return (size_t)received;
}

rmw_uros_set_custom_transport(
    false,   // false = stream (serial/SPI), true = datagram (UDP/CAN)
    NULL, my_transport_open, my_transport_close,
    my_transport_write, my_transport_read);
```

---

## 8. Production deployment patterns

### Reconnection state machine

The agent can disconnect (USB unplug, network failure, host reboot). Detect and reinitialize:

```c
typedef enum { AGENT_WAIT, AGENT_AVAILABLE, AGENT_CONNECTED, AGENT_DISCONNECTED } AgentState;
static AgentState state = AGENT_WAIT;
static uint32_t ping_counter = 0;

bool is_agent_connected(void) {
    return rmw_uros_ping_agent(100, 1) == RMW_RET_OK;
}

void micro_ros_task(void * arg)
{
    rcl_allocator_t allocator = rcl_get_default_allocator();
    rclc_support_t support;
    rcl_node_t node;
    rcl_publisher_t pub;
    rcl_timer_t timer;
    rclc_executor_t executor;

    while (1) {
        switch (state) {
        case AGENT_WAIT:
            if (is_agent_connected()) { state = AGENT_AVAILABLE; }
            else { vTaskDelay(pdMS_TO_TICKS(500)); }
            break;
        case AGENT_AVAILABLE:
            if (create_entities(&pub, &timer, &executor, &node, &support, &allocator))
                state = AGENT_CONNECTED;
            else { state = AGENT_WAIT; vTaskDelay(pdMS_TO_TICKS(1000)); }
            break;
        case AGENT_CONNECTED:
            RCSOFTCHECK(rclc_executor_spin_some(&executor, RCL_MS_TO_NS(100)));
            // Check connectivity every 100 cycles, NOT every spin (ping adds ~100ms)
            if (++ping_counter >= 100) {
                ping_counter = 0;
                if (!is_agent_connected()) { state = AGENT_DISCONNECTED; }
            }
            vTaskDelay(pdMS_TO_TICKS(1));
            break;
        case AGENT_DISCONNECTED:
            destroy_entities(&pub, &timer, &executor, &node, &support);
            state = AGENT_WAIT;
            break;
        }
    }
}
```

Do not call `rmw_uros_ping_agent()` on every spin cycle. It adds latency. Check every 50-100 cycles or use a separate low-priority RTOS task.

### Time synchronization

```c
rmw_uros_sync_session(1000);  // Sync MCU clock with agent, 1s timeout
int64_t time_ns = rmw_uros_epoch_nanos();
```

### Watchdog integration

```c
#include <esp_task_wdt.h>
// ESP-IDF v5+ API (Jazzy/Kilted micro-ROS builds)
esp_task_wdt_config_t wdt_config = {
    .timeout_ms = 10000, .idle_core_mask = 0, .trigger_panic = true,
};
esp_task_wdt_init(&wdt_config);
// ESP-IDF v4.x (Humble): esp_task_wdt_init(10, true);
// Check version: idf.py --version
esp_task_wdt_add(xTaskGetCurrentTaskHandle());
// In spin loop:
esp_task_wdt_reset();  // Feed watchdog each iteration
```

### Parameter server on MCU (Humble+)

```c
#include <rclc_parameter/rclc_parameter.h>
static rclc_parameter_server_t param_server;
rclc_parameter_server_init_default(&param_server, &node);
rclc_add_parameter(&param_server, "publish_rate_hz", RCLC_PARAMETER_DOUBLE);
rclc_parameter_set_double(&param_server, "publish_rate_hz", 100.0);
// Parameter server adds 3 executor handles (2 services + 1 guard condition)
```

---

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Agent shows "No data received" | Wrong baud rate or transport config | Match baud rate on both sides; check serial port permissions |
| Node appears then disappears | MCU running out of memory | Reduce executor handles, message sizes, or string capacities |
| Publishing at wrong rate | Timer period too short for MCU processing | Profile callback time; ensure it finishes before next timer tick |
| Custom message "type not found" | Message package not in extra_packages | Rebuild firmware with custom message package in extra_packages/ |
| WiFi transport drops messages | UDP packet loss, network congestion | Use QoS BEST_EFFORT; reduce publish rate; keep msgs under MTU |
| Agent crashes with segfault | Client-agent version mismatch | Match micro-ROS version to ROS 2 distro exactly |
| MCU watchdog resets | Callback takes too long, starves RTOS | Move heavy computation to separate RTOS task; reduce timer rate |
| Timestamps are wrong | MCU clock not synchronized | Use `rmw_uros_sync_session(timeout_ms)` after connecting |
| Subscriber callback never fires | Executor handle count too low or QoS mismatch | Verify handle count; BEST_EFFORT pub needs BEST_EFFORT sub |
| Cannot create more publishers | `RMW_UXRCE_MAX_PUBLISHERS` exceeded | Increase the limit in colcon.meta and rebuild firmware |
| "memory region RAM overflowed" | Firmware binary exceeds MCU RAM | Reduce entity counts, disable unused msg packages, use `-Os` |

### Debugging

```bash
ros2 run micro_ros_agent micro_ros_agent serial --dev /dev/ttyUSB0 -b 115200 -v6
ros2 node list
ros2 topic hz /imu/data_raw
ros2 topic info /imu/data_raw --verbose
```
