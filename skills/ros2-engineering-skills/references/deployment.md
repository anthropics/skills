# Deployment

## Table of contents
1. Docker multi-stage builds for ROS 2
2. Cross-compilation (aarch64, armhf)
3. Deployment on embedded platforms
4. Fleet management and OTA updates
5. systemd service configuration
6. Environment variable management
7. Security (SROS2, DDS security)
8. Monitoring and health checks
9. Common failures and fixes

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

# Reduce DDS overhead
export ROS_LOCALHOST_ONLY=1  # If single-machine
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

# On each robot — pull and restart (via agent or SSH)
docker pull registry.example.com/my_robot:v2.1.0
docker-compose up -d --force-recreate

# Rollback if needed (set IMAGE_TAG in .env or docker-compose.yml)
IMAGE_TAG=v2.0.0 docker-compose up -d --force-recreate
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
// In your main node — send heartbeat to systemd
#include <systemd/sd-daemon.h>

void heartbeat_callback()
{
  sd_notify(0, "WATCHDOG=1");
}
// Create timer at half the WatchdogSec interval
timer_ = create_wall_timer(15s, heartbeat_callback);

// Notify systemd when fully started
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

## 7. Security (SROS2, DDS security)

### SROS2 setup

```bash
# Create a security keystore
ros2 security create_keystore /opt/robot/keystore

# Generate keys for each node
ros2 security create_enclave /opt/robot/keystore /my_robot/driver
ros2 security create_enclave /opt/robot/keystore /my_robot/navigation

# Enable security
export ROS_SECURITY_KEYSTORE=/opt/robot/keystore
export ROS_SECURITY_ENABLE=true
export ROS_SECURITY_STRATEGY=Enforce  # or "Permissive" for testing
```

### Access control policies

```xml
<!-- permissions.xml — define what each node can access -->
<permissions>
  <grant name="/my_robot/driver">
    <allow_rule>
      <publish>
        <topics><topic>rt/joint_states</topic></topics>
      </publish>
      <subscribe>
        <topics><topic>rt/joint_commands</topic></topics>
      </subscribe>
    </allow_rule>
    <deny_rule>
      <publish>
        <topics><topic>*</topic></topics>
      </publish>
    </deny_rule>
  </grant>
</permissions>
```

### Security best practices

- **Encrypt all inter-machine DDS traffic** — default DDS is unencrypted
- **Use SROS2 in production** — prevents unauthorized nodes from joining
- **Restrict device permissions** — use udev rules for serial/CAN devices
- **Don't run as root** — use dedicated `robot` user with minimal privileges
- **Rotate keys** — regenerate SROS2 keys periodically

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

## 9. Common failures and fixes

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
