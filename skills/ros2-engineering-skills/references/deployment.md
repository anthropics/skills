# Deployment

## Table of contents
1. Docker multi-stage builds for ROS 2
2. Cross-compilation (aarch64, armhf)
3. Deployment on embedded platforms
4. Fleet management and OTA updates
5. systemd service configuration
6. Environment variable management
7. Security (SROS2)
8. Monitoring and health checks
9. Graceful shutdown
10. Common failures and fixes

---

## 1. Docker multi-stage builds for ROS 2

### Multi-stage Dockerfile pattern

```dockerfile
# ─── Stage 1: Build ──────────────────────────────────────────
FROM ros:jazzy AS builder

# Install build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3-colcon-common-extensions \
    python3-rosdep \
    && rm -rf /var/lib/apt/lists/*

# Copy source
WORKDIR /ros2_ws
COPY src/ src/

# Install rosdep dependencies
RUN rosdep update && \
    rosdep install --from-paths src --ignore-src -y

# Build
RUN . /opt/ros/jazzy/setup.sh && \
    colcon build --cmake-args -DCMAKE_BUILD_TYPE=Release \
    --event-handlers console_cohesion+

# ─── Stage 2: Runtime ────────────────────────────────────────
FROM ros:jazzy AS runtime

# Install only runtime dependencies (no build tools)
COPY --from=builder /ros2_ws/install /ros2_ws/install

# Copy runtime rosdep dependencies list from builder
COPY --from=builder /ros2_ws/src /tmp/src
RUN apt-get update && \
    rosdep update && \
    rosdep install --from-paths /tmp/src --ignore-src -y \
    --skip-keys "ament_cmake ament_lint_auto" && \
    rm -rf /tmp/src /var/lib/apt/lists/*

# Entry point
COPY docker/entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh
ENTRYPOINT ["/entrypoint.sh"]
CMD ["ros2", "launch", "my_robot_bringup", "robot.launch.py"]
```

### Entrypoint script

```bash
#!/bin/bash
# docker/entrypoint.sh
set -e

# Validate ROS 2 installation exists before sourcing
if [ ! -f /opt/ros/jazzy/setup.bash ]; then
  echo "ERROR: /opt/ros/jazzy/setup.bash not found. Check base image." >&2
  exit 1
fi

# Source ROS 2 and workspace
source /opt/ros/jazzy/setup.bash
source /ros2_ws/install/setup.bash

# Execute the command
exec "$@"
```

### Docker Compose for multi-container robot

```yaml
# docker-compose.yaml
services:
  driver:
    build:
      context: .
      target: runtime
    command: ros2 launch my_robot_driver driver.launch.py
    network_mode: host  # Required for DDS multicast discovery
    devices:
      - /dev/ttyUSB0:/dev/ttyUSB0  # Serial device passthrough
    privileged: false
    environment:
      - ROS_DOMAIN_ID=42
      - CYCLONEDDS_URI=file:///config/cyclonedds.xml

  perception:
    build:
      context: .
      target: runtime
    command: ros2 launch my_robot_perception perception.launch.py
    network_mode: host
    devices:
      - /dev/video0:/dev/video0  # Camera
    environment:
      - ROS_DOMAIN_ID=42

  navigation:
    build:
      context: .
      target: runtime
    command: ros2 launch my_robot_navigation navigation.launch.py
    network_mode: host
    volumes:
      - ./maps:/maps:ro
    environment:
      - ROS_DOMAIN_ID=42
```

### Docker build optimization

```dockerfile
# Use buildkit cache for apt and rosdep
# syntax=docker/dockerfile:1
RUN --mount=type=cache,target=/var/cache/apt \
    apt-get update && apt-get install -y --no-install-recommends \
    python3-colcon-common-extensions

# Cache colcon build artifacts between builds
RUN --mount=type=cache,target=/ros2_ws/build \
    --mount=type=cache,target=/ros2_ws/log \
    . /opt/ros/jazzy/setup.sh && \
    colcon build --cmake-args -DCMAKE_BUILD_TYPE=Release
```

### Docker networking for DDS

```yaml
# docker-compose.yml — host networking (simplest, recommended for single-machine)
services:
  robot:
    network_mode: host
    # DDS uses host networking directly — no port mapping needed
```

For multi-container on the same host without host networking:
```yaml
services:
  robot_a:
    networks:
      - ros_net
    environment:
      - CYCLONEDDS_URI=file:///config/cyclonedds_docker.xml
  robot_b:
    networks:
      - ros_net
    environment:
      - CYCLONEDDS_URI=file:///config/cyclonedds_docker.xml

networks:
  ros_net:
    driver: bridge
```

```xml
<!-- cyclonedds_docker.xml — unicast for Docker bridge network -->
<CycloneDDS xmlns="https://cdds.io/config">
  <Domain>
    <General>
      <AllowMulticast>false</AllowMulticast>
    </General>
    <Discovery>
      <Peers>
        <Peer address="robot_a"/>
        <Peer address="robot_b"/>
      </Peers>
    </Discovery>
  </Domain>
</CycloneDDS>
```

For shared memory transport inside Docker:
```bash
# Required for iceoryx/CycloneDDS shared memory
docker run --ipc=host ...
```

## 2. Cross-compilation (aarch64, armhf)

### Using Docker + QEMU (simplest approach)

```bash
# Enable multi-arch builds
docker run --rm --privileged multiarch/qemu-user-static --reset -p yes

# Build for ARM64
docker buildx build \
  --platform linux/arm64 \
  -t my_robot:arm64 \
  --load .
```

### Native cross-compilation with colcon

```bash
# Install cross-compilation toolchain
sudo apt install gcc-aarch64-linux-gnu g++-aarch64-linux-gnu

# Create cross-compilation toolchain file
cat > aarch64_toolchain.cmake << 'EOF'
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR aarch64)
set(CMAKE_C_COMPILER /usr/bin/aarch64-linux-gnu-gcc)
set(CMAKE_CXX_COMPILER /usr/bin/aarch64-linux-gnu-g++)
set(CMAKE_FIND_ROOT_PATH /usr/aarch64-linux-gnu)
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
EOF

# Build with toolchain
colcon build \
  --cmake-args -DCMAKE_TOOLCHAIN_FILE=$(pwd)/aarch64_toolchain.cmake
```

## 3. Deployment on embedded platforms

### NVIDIA Jetson (Orin, Xavier, Nano)

```dockerfile
# Jetson-specific Dockerfile using JetPack base
FROM dustynv/ros:jazzy-pytorch-l4t-r36.4.0 AS runtime

# Jetson-specific: Use CUDA-accelerated libraries
ENV CUDA_HOME=/usr/local/cuda
ENV LD_LIBRARY_PATH=/usr/local/cuda/lib64:$LD_LIBRARY_PATH

# Copy workspace
COPY --from=builder /ros2_ws/install /ros2_ws/install

# Enable GPU access
# Run with: docker run --runtime nvidia --gpus all
```

### Raspberry Pi 4/5

```bash
# Use Ubuntu 24.04 Server (64-bit) for Jazzy
# Install ROS 2 Jazzy (ARM64 packages available)
sudo apt install ros-jazzy-ros-base  # No desktop on headless Pi

# Optimize for limited resources
colcon build --parallel-workers 2 \
  --cmake-args -DCMAKE_BUILD_TYPE=Release

# Reduce DDS overhead (Jazzy+: use ROS_AUTOMATIC_DISCOVERY_RANGE instead of ROS_LOCALHOST_ONLY)
export ROS_AUTOMATIC_DISCOVERY_RANGE=LOCALHOST  # If single-machine
export CYCLONEDDS_URI='<CycloneDDS><Domain><Internal><MinimumSocketReceiveBufferSize>64KB</MinimumSocketReceiveBufferSize></Internal></Domain></CycloneDDS>'
```

### Resource optimization for embedded

- Use `ros-jazzy-ros-base` (no GUI packages)
- Compile with `-DCMAKE_BUILD_TYPE=Release` (smaller binaries, faster execution)
- Use `component_container` (single process) instead of multiple processes
- Limit DDS discovery scope with `ROS_LOCALHOST_ONLY=1`
- Disable unused DDS features in CycloneDDS config

## 4. Fleet management and OTA updates

### Fleet architecture

```
                 ┌──────────────────┐
                 │   Fleet Server    │
                 │ (cloud/on-prem)   │
                 └────────┬─────────┘
                          │ HTTPS/MQTT
           ┌──────────────┼──────────────┐
           ▼              ▼              ▼
    ┌──────────┐   ┌──────────┐   ┌──────────┐
    │ Robot 1   │   │ Robot 2   │   │ Robot 3   │
    │ Agent     │   │ Agent     │   │ Agent     │
    └──────────┘   └──────────┘   └──────────┘
```

### Container-based OTA updates

```bash
# On the fleet server — build and push new image
docker build -t registry.example.com/my_robot:v2.1.0 .
docker push registry.example.com/my_robot:v2.1.0

# On each robot — pull with integrity verification and health check
#!/bin/bash
set -e
NEW_TAG="v2.1.0"
OLD_TAG=$(docker inspect --format='{{.Config.Image}}' my_robot_driver 2>/dev/null || echo "none")

# 1. Pull new image
docker pull "registry.example.com/my_robot:${NEW_TAG}"

# 2. Pre-flight: verify the image can at least start and pass a health check
# Note: docker run has no --timeout flag; use coreutils timeout instead
timeout 30 docker run --rm "registry.example.com/my_robot:${NEW_TAG}" \
  ros2 doctor --report > /dev/null 2>&1 || {
    echo "ERROR: New image failed pre-flight check. Aborting OTA." >&2
    exit 1
  }

# 3. Deploy
IMAGE_TAG="${NEW_TAG}" docker-compose up -d --force-recreate

# 4. Post-deploy health check (wait for ROS nodes to come up)
sleep 15
if ! docker exec my_robot_driver ros2 topic list > /dev/null 2>&1; then
  echo "WARN: Post-deploy health check failed. Rolling back to ${OLD_TAG}" >&2
  IMAGE_TAG="${OLD_TAG}" docker-compose up -d --force-recreate
  exit 1
fi
echo "OTA update to ${NEW_TAG} successful."
```

### Version management

```yaml
# robot_manifest.yaml — deployed to each robot
robot_id: robot_001
fleet: warehouse_a
software_version: 2.1.0
ros_distro: jazzy
hardware_revision: rev_c
packages:
  my_robot_driver: 2.1.0
  my_robot_navigation: 2.0.3
  my_robot_perception: 2.1.0
```

## 5. systemd service configuration

### ROS 2 systemd service

```ini
# /etc/systemd/system/ros2-robot.service
[Unit]
Description=ROS 2 Robot Stack
After=network-online.target
Wants=network-online.target

[Service]
Type=exec
User=robot
Group=robot

# Environment
Environment="ROS_DOMAIN_ID=42"
Environment="RMW_IMPLEMENTATION=rmw_cyclonedds_cpp"
Environment="CYCLONEDDS_URI=file:///opt/robot/config/cyclonedds.xml"

# Source ROS and launch
ExecStart=/bin/bash -c '\
  source /opt/ros/jazzy/setup.bash && \
  source /opt/robot/install/setup.bash && \
  ros2 launch my_robot_bringup robot.launch.py'

# Restart policy
Restart=on-failure
RestartSec=5
StartLimitBurst=3
StartLimitIntervalSec=60

# Resource limits
LimitRTPRIO=99
LimitMEMLOCK=infinity

# Logging
StandardOutput=journal
StandardError=journal
SyslogIdentifier=ros2-robot

[Install]
WantedBy=multi-user.target
```

### Managing the service

```bash
# Enable and start
sudo systemctl enable ros2-robot
sudo systemctl start ros2-robot

# Check status
sudo systemctl status ros2-robot

# View logs
sudo journalctl -u ros2-robot -f

# Restart after update
sudo systemctl restart ros2-robot
```

### Watchdog integration

```ini
# Add to [Service] section
WatchdogSec=30  # systemd kills service if no heartbeat in 30s
```

```cpp
// In your lifecycle node — send heartbeat to systemd
#include <systemd/sd-daemon.h>
#include <chrono>
using namespace std::chrono_literals;

// In on_activate():
watchdog_timer_ = create_wall_timer(15s,
  [this]() { sd_notify(0, "WATCHDOG=1"); });

// In on_activate() after all setup:
sd_notify(0, "READY=1");
```

## 6. Environment variable management

### Essential ROS 2 environment variables

| Variable | Purpose | Default |
|---|---|---|
| `ROS_DOMAIN_ID` | DDS domain isolation | 0 |
| `RMW_IMPLEMENTATION` | DDS middleware selection | `rmw_cyclonedds_cpp` (Jazzy) |
| `CYCLONEDDS_URI` | CycloneDDS configuration file | None |
| `ROS_LOCALHOST_ONLY` | Restrict to localhost | 0 (disabled) |
| `ROS_LOG_DIR` | Log file directory | `~/.ros/log` |
| `RCUTILS_COLORIZED_OUTPUT` | Colorized console output | 1 |
| `RCUTILS_CONSOLE_OUTPUT_FORMAT` | Log format string | `[{severity}] [{time}] [{name}]: {message}` |

### Per-robot configuration

```bash
# /opt/robot/env.sh — robot-specific environment
export ROBOT_ID="robot_001"
export ROS_DOMAIN_ID=42
export ROBOT_TYPE="diff_drive"
export SERIAL_PORT="/dev/ttyUSB0"
```

### Discovery range control (Jazzy+)

Jazzy introduced `ROS_AUTOMATIC_DISCOVERY_RANGE` as a more flexible replacement for `ROS_LOCALHOST_ONLY`:

```bash
# Restrict discovery to localhost (replaces ROS_LOCALHOST_ONLY=1)
export ROS_AUTOMATIC_DISCOVERY_RANGE=LOCALHOST

# Allow discovery within the subnet (default behavior)
export ROS_AUTOMATIC_DISCOVERY_RANGE=SUBNET

# Disable automatic discovery entirely (manual peer configuration only)
export ROS_AUTOMATIC_DISCOVERY_RANGE=OFF

# Use system default (no restriction)
export ROS_AUTOMATIC_DISCOVERY_RANGE=SYSTEM_DEFAULT
```

**Note:** `ROS_LOCALHOST_ONLY` is deprecated in Jazzy+ but still works. Prefer `ROS_AUTOMATIC_DISCOVERY_RANGE` for new deployments.

### ROS 2 Daemon behavior

The ROS 2 daemon (`ros2 daemon`) caches discovery information to speed up CLI tools (`ros2 topic list`, `ros2 node list`). It can become stale:

```bash
# If ros2 CLI shows stale/missing topics:
ros2 daemon stop
ros2 daemon start

# Check daemon status
ros2 daemon status
```

The daemon runs as a background process. It connects to the DDS network independently of your nodes. If you change `ROS_DOMAIN_ID` or `RMW_IMPLEMENTATION` after the daemon starts, CLI commands will show data from the old configuration until the daemon is restarted.

## 7. Security (SROS2)

For production deployments, enable DDS security via SROS2. This provides mutual TLS authentication,
topic-level access control, and message encryption. See `references/security.md` for the complete
SROS2 workflow including keystore setup, governance/permissions authoring, certificate management,
supply chain hardening, and performance impact analysis.

Quick start for testing:
```bash
ros2 security create_keystore ~/sros2_keystore
ros2 security create_enclave ~/sros2_keystore /my_robot/driver
export ROS_SECURITY_KEYSTORE=~/sros2_keystore
export ROS_SECURITY_ENABLE=true
export ROS_SECURITY_STRATEGY=Permissive  # Use Enforce in production
```

## 8. Monitoring and health checks

### Health check endpoint pattern

```python
class HealthMonitor(Node):
    def __init__(self):
        super().__init__('health_monitor')
        self.srv = self.create_service(
            Trigger, 'health_check', self.health_callback)
        self.monitored_topics = {
            '/joint_states': {'timeout': 1.0, 'last_seen': None},
            '/scan': {'timeout': 2.0, 'last_seen': None},
        }
        for topic in self.monitored_topics:
            self.create_subscription(
                AnyMsg, topic,
                lambda msg, t=topic: self._update(t), 10)

    def health_callback(self, request, response):
        now = self.get_clock().now()
        unhealthy = []
        for topic, info in self.monitored_topics.items():
            if info['last_seen'] is None:
                unhealthy.append(f'{topic}: never received')
            elif (now - info['last_seen']).nanoseconds / 1e9 > info['timeout']:
                unhealthy.append(f'{topic}: timeout')

        response.success = len(unhealthy) == 0
        response.message = 'OK' if response.success else '; '.join(unhealthy)
        return response
```

### Prometheus metrics (for fleet dashboards)

```python
# Expose ROS 2 metrics to Prometheus
from prometheus_client import start_http_server, Gauge, Counter

msg_rate = Gauge('ros2_topic_rate_hz', 'Topic message rate', ['topic'])
control_latency = Gauge('ros2_control_latency_us', 'Control loop latency')
error_count = Counter('ros2_errors_total', 'Total error count', ['node', 'type'])

# Start metrics server on port 9090
start_http_server(9090)
```

## 9. Graceful shutdown

### The problem

When systemd restarts a ROS 2 service (`systemctl restart ros2-robot`), it sends
`SIGTERM` and waits `TimeoutStopSec` (default 90s) before `SIGKILL`. Lifecycle
nodes need time to transition through `deactivate → cleanup → shutdown`. If the
shutdown is too slow, `SIGKILL` leaves hardware in an unsafe state (motors running,
grippers open, sensor streams active).

### systemd configuration

```ini
# Add to [Service] section
TimeoutStopSec=15          # Give ROS 15s to shut down gracefully
KillSignal=SIGINT          # SIGINT triggers rclcpp::shutdown() cleanly
SendSIGKILL=yes            # Force-kill after TimeoutStopSec if still alive
```

### Signal handling in launch files

```python
import signal
from launch import LaunchDescription
from launch.actions import RegisterEventHandler, Shutdown
from launch.event_handlers import OnProcessExit

def generate_launch_description():
    # Ensure all nodes shut down when the main process exits
    return LaunchDescription([
        # ... your nodes ...,
        RegisterEventHandler(
            OnProcessExit(
                target_action=driver_node,
                on_exit=[Shutdown(reason='Driver exited')],
            )
        ),
    ])
```

### Hardware safety on shutdown

For lifecycle nodes that control hardware, the `on_deactivate` callback must:
1. Send a safe command (zero velocity, disable torque, close gripper to safe position)
2. Wait for acknowledgement from hardware (with timeout)
3. Close communication channels

```cpp
CallbackReturn on_deactivate(const rclcpp_lifecycle::State &) override {
  // 1. Safe the hardware BEFORE closing the connection
  if (serial_.is_open()) {
    send_zero_velocity(serial_);
    // 2. Brief wait for hardware to acknowledge
    std::this_thread::sleep_for(std::chrono::milliseconds(50));
  }
  // 3. Close
  serial_.close();
  return CallbackReturn::SUCCESS;
}
```

**Anti-pattern:** Not sending a safe command in `on_deactivate`. If the last `write()`
command was `velocity=1.0` and the node shuts down, the motor may continue at that
velocity until hardware watchdog times out (if one exists).

## 10. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| DDS discovery fails in Docker | Network mode not `host` | Use `network_mode: host` or configure DDS peers manually |
| Serial device not accessible in container | Device not passed through | Add `devices: [/dev/ttyUSB0:/dev/ttyUSB0]` in docker-compose |
| Container image too large (>5 GB) | Including build tools in runtime | Use multi-stage build, copy only `install/` to runtime stage |
| systemd service fails to start | ROS 2 environment not sourced | Source setup.bash in ExecStart script |
| OTA update breaks robot | No rollback mechanism | Use versioned Docker images, keep previous version on disk |
| Cross-compiled binary crashes on target | Mismatched libraries | Build in Docker with matching target rootfs |
| DDS traffic not encrypted | SROS2 not enabled | Set `ROS_SECURITY_ENABLE=true`, configure keystore |
| Robot disconnects from fleet server | WiFi/network instability | Implement reconnection logic, queue commands locally |
