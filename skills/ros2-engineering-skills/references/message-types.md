# Message Types & Semantic Conventions

## Table of contents
1. The Stamped vs Unstamped rule
2. Time and Header conventions (ROS 2 specific)
3. Sensor data (`sensor_msgs`) implicit rules
4. Geometry and navigation (`geometry_msgs`, `nav_msgs`)
5. Joint and control messages
6. Point cloud structure (`PointCloud2`)
7. Camera intrinsics (`CameraInfo`)
8. TF messages and QoS conventions
9. Action status codes
10. Diagnostic messages (`diagnostic_msgs`)
11. Covariance matrix conventions
12. Standard units (REP-103)
13. Common failures and anti-patterns

---

## 1. The Stamped vs Unstamped rule

ROS 2 provides both base types (e.g., `Twist`, `Pose`) and "Stamped" types
(e.g., `TwistStamped`, `PoseStamped`). The difference is the `std_msgs/msg/Header`.

| Message | Header? | When to use | Example topic |
|---|---|---|---|
| `geometry_msgs/msg/Twist` | No | Direct velocity commands where latency is minimal and frame is implicitly the robot base | `/cmd_vel` |
| `geometry_msgs/msg/TwistStamped` | Yes | Velocity measurements, external commands where network delay must be compensated, or data tied to a specific frame | `/robot_velocity` |
| `geometry_msgs/msg/Pose` | No | Abstract mathematical points (e.g., inside configuration or internal logic) | N/A |
| `geometry_msgs/msg/PoseStamped` | Yes | ANY pose communicated across the ROS network — **always prefer Stamped for spatial data** | `/goal_pose` |
| `geometry_msgs/msg/Point` | No | Bare 3D coordinate (x, y, z) with no orientation | Internal math |
| `geometry_msgs/msg/PointStamped` | Yes | 3D coordinate tied to a frame and timestamp | `/clicked_point` |
| `geometry_msgs/msg/Transform` | No | Bare rotation + translation | Internal math |
| `geometry_msgs/msg/TransformStamped` | Yes | Every TF broadcast — always Stamped | `/tf`, `/tf_static` |

**Rule of thumb:** If the data leaves a single function scope or crosses a topic
boundary, use the Stamped variant. The Header provides the frame_id and
timestamp needed for TF lookups, data fusion, and replay.

## 2. Time and Header conventions (ROS 2 specific)

In ROS 2, time is handled by the node's clock, not a global state. **Never use
system time directly** for ROS messages; always use the ROS clock to support
simulation time (`use_sim_time: true`).

### Populating headers

**C++ (`rclcpp`):**
```cpp
auto msg = std::make_shared<sensor_msgs::msg::Image>();
msg->header.stamp = this->get_clock()->now();
msg->header.frame_id = "camera_optical_frame";
```

**Python (`rclpy`):**
```python
msg = Image()
msg.header.stamp = self.get_clock().now().to_msg()
msg.header.frame_id = 'camera_optical_frame'
```

### Time sources

| Clock type | Source | When to use |
|---|---|---|
| `ROS_TIME` | `/clock` topic (when `use_sim_time: true`) or system clock | Default — works in sim and real |
| `SYSTEM_TIME` | OS monotonic clock | Never for message stamps |
| `STEADY_TIME` | Monotonic, never adjusted | Internal timing (loop measurement), not for messages |

### Common time mistakes

```python
# BAD — breaks during rosbag playback and Gazebo simulation
import time
msg.header.stamp.sec = int(time.time())

# BAD — rclpy Time object, not a msg type
msg.header.stamp = self.get_clock().now()  # Python: missing .to_msg()

# GOOD
msg.header.stamp = self.get_clock().now().to_msg()
```

```cpp
// BAD — system time, not ROS time
msg->header.stamp = rclcpp::Clock(RCL_SYSTEM_TIME).now();

// GOOD — uses node's clock (respects use_sim_time)
msg->header.stamp = this->get_clock()->now();
```

## 3. Sensor data (`sensor_msgs`) implicit rules

Sensor messages have strict frame and data conventions that are **not enforced
by the compiler or serializer** — only by convention and downstream consumers.

### `sensor_msgs/msg/Imu`

```
Header header
geometry_msgs/Quaternion orientation               # (x, y, z, w)
float64[9] orientation_covariance
geometry_msgs/Vector3 angular_velocity             # rad/s
float64[9] angular_velocity_covariance
geometry_msgs/Vector3 linear_acceleration          # m/s² (includes gravity!)
float64[9] linear_acceleration_covariance
```

- **Frame:** Typically `imu_link`.
- **Covariance rule:** If a specific measurement (orientation, angular velocity,
  or linear acceleration) is **not available** from the sensor, you MUST set the
  first element of its covariance matrix to `-1.0`.
  ```python
  # IMU does not provide orientation data
  msg.orientation_covariance[0] = -1.0
  ```
- **Units:** `linear_acceleration` **includes gravity** (e.g., ~9.81 m/s² on
  Z-axis when resting flat on a table).
- **Gravity convention:** When the IMU is level and stationary,
  `linear_acceleration.z ≈ +9.81` (gravity points upward in sensor frame).

### `sensor_msgs/msg/LaserScan`

```
Header header
float32 angle_min         # start angle (rad)
float32 angle_max         # end angle (rad)
float32 angle_increment   # angular step (rad)
float32 time_increment    # time between measurements (s)
float32 scan_time         # time between full scans (s)
float32 range_min         # minimum valid range (m)
float32 range_max         # maximum valid range (m)
float32[] ranges          # range data (m)
float32[] intensities     # intensity data (optional, device-specific)
```

- **Frame:** Typically `laser_link` or `lidar_link`. Z-axis points UP,
  X-axis points forward.
- **Angle convention:** `angle_min` and `angle_max` are in radians.
  Zero is directly forward (positive X-axis). Counter-clockwise is positive.
- **Invalid data:** If a laser ray doesn't hit anything, its range should be
  `Infinity` (or a value outside `[range_min, range_max]`).
  **Do NOT use `0.0` for no return** — that looks like an obstacle at zero distance.
- **NaN:** A range of `NaN` means the measurement is invalid/erroneous.
  Distinct from `Infinity` (valid measurement, nothing in range).

### `sensor_msgs/msg/Image`

```
Header header
uint32 height
uint32 width
string encoding           # "rgb8", "bgr8", "mono8", "16UC1", "32FC1", etc.
uint8 is_bigendian
uint32 step               # row length in bytes
uint8[] data              # actual pixel data
```

- **Frame:** CRITICAL — use `camera_optical_frame`, **NOT** `camera_link`.
  - Standard robotics frame (`camera_link`): X-forward, Y-left, Z-up
  - Optical frame (`camera_optical_frame`): X-right, Y-down, Z-forward (into scene)
  - The rotation between them is `rpy="-π/2 0 -π/2"` in the URDF joint.
- **Encoding:** Use standard strings: `"rgb8"`, `"bgr8"`, `"mono8"`,
  `"16UC1"` (depth in mm), `"32FC1"` (depth in meters).
- **`step`:** Must equal `width × bytes_per_pixel` (e.g., `width × 3` for `rgb8`).
  Some producers pad rows; consumers must use `step`, not `width × bpp`.

### `sensor_msgs/msg/JointState`

```
Header header
string[] name             # joint names
float64[] position        # radians (revolute) or meters (prismatic)
float64[] velocity        # rad/s or m/s
float64[] effort          # Nm or N
```

- **Array alignment:** `position`, `velocity`, and `effort` arrays MUST have
  the same length as `name`, and the indices correspond 1:1.
  `position[i]` is the position of `name[i]`.
- **Partial data allowed:** If velocity or effort data is unavailable, the
  array MAY be empty (length 0). But if it has any elements, it must have
  ALL elements (same length as `name`). No partial arrays.
- **Joint order:** Not guaranteed to be the same across publishers. Always
  look up by name, never assume index order.

```cpp
// GOOD — look up by name
for (size_t i = 0; i < msg->name.size(); ++i) {
  if (msg->name[i] == "joint_1") {
    double pos = msg->position[i];
  }
}

// BAD — assumes fixed index order
double pos = msg->position[0];  // Which joint is this? Depends on publisher!
```

## 4. Geometry and navigation (`geometry_msgs`, `nav_msgs`)

### `nav_msgs/msg/Odometry`

```
Header header
string child_frame_id
geometry_msgs/PoseWithCovariance pose
geometry_msgs/TwistWithCovariance twist
```

- **Frame semantics:**
  - `header.frame_id`: The fixed world frame (usually `odom`)
  - `child_frame_id`: The moving robot frame (usually `base_link`)
- **Data meaning:**
  - `pose.pose`: The position and orientation of `child_frame_id` **in**
    `header.frame_id`
  - `twist.twist`: The velocity of `child_frame_id` expressed **in**
    `child_frame_id` (NOT in the odom frame!)
- **This is the #1 misunderstanding:** The twist is body-frame velocity.
  `twist.twist.linear.x` is forward speed of the robot, regardless of its
  heading in the odom frame.

### `geometry_msgs/msg/Quaternion`

```
float64 x 0
float64 y 0
float64 z 0
float64 w 1   # Changed to 1.0 in Galactic+ (Humble, Jazzy, Kilted, Rolling)
```

- **Must always be normalized:** `x² + y² + z² + w² = 1`
- **Humble+ default is `(0,0,0,1)` (identity)** — safe to use directly.
  In Foxy (EOL), the default was `(0,0,0,0)` which crashed tf2.
- **Still explicitly initialize `w = 1.0`** when constructing quaternions in
  code that may run on mixed distros or when clarity matters.

```cpp
// Humble+: default-constructed Quaternion is (0,0,0,1) — valid identity
geometry_msgs::msg::Quaternion q;  // q.w is already 1.0

// Still recommended: explicit initialization for clarity
geometry_msgs::msg::Quaternion q;
q.w = 1.0;  // redundant on Humble+ but clear and safe

// GOOD — from yaw angle
tf2::Quaternion tf_q;
tf_q.setRPY(0, 0, yaw);
auto q = tf2::toMsg(tf_q);  // properly normalized
```

```python
# GOOD — Python identity quaternion
from geometry_msgs.msg import Quaternion
q = Quaternion(x=0.0, y=0.0, z=0.0, w=1.0)

# GOOD — from yaw
from tf_transformations import quaternion_from_euler
quat = quaternion_from_euler(0, 0, yaw)  # returns (x, y, z, w)
```

### `nav_msgs/msg/Path`

```
Header header
geometry_msgs/PoseStamped[] poses
```

- **All poses must be in the same frame** as `header.frame_id`.
- Each pose in the array should have its own timestamp (for time-parameterized paths)
  or all timestamps set to zero (for purely spatial paths).

### `nav_msgs/msg/OccupancyGrid`

```
Header header
MapMetaData info          # resolution, width, height, origin
int8[] data               # occupancy values
```

- **Cell values:** `-1` = unknown, `0` = free, `100` = occupied.
  Values 1–99 represent probability of occupancy.
- **Data layout:** Row-major, starting from the origin (lower-left corner).
  Index = `y * width + x`.

## 5. Joint and control messages

### `trajectory_msgs/msg/JointTrajectory`

```
Header header
string[] joint_names
JointTrajectoryPoint[] points
```

Each `JointTrajectoryPoint` contains:
```
float64[] positions       # target positions
float64[] velocities      # target velocities (optional)
float64[] accelerations   # target accelerations (optional)
float64[] effort          # target effort (optional)
builtin_interfaces/Duration time_from_start
```

- **`time_from_start`:** Time relative to `header.stamp`, NOT absolute time.
  Point at `time_from_start = 2.0s` means "reach this configuration 2 seconds
  after the trajectory starts."
- **Array alignment:** `positions` must have the same length as `joint_names`.
  `velocities`, `accelerations`, and `effort` are either empty (not specified)
  or the same length as `joint_names`.
- **Ordering:** Points must be ordered by increasing `time_from_start`.

### `control_msgs/action/FollowJointTrajectory`

This is the standard action used by ros2_control's `JointTrajectoryController`
and MoveIt 2.

- **Goal tolerances:** Specify per-joint position/velocity/acceleration
  tolerance for accepting the goal as reached.
- **Path tolerances:** If the robot deviates from the trajectory beyond path
  tolerance at any point, the action is aborted.
- **Result codes:**
  - `SUCCESSFUL = 0`
  - `INVALID_GOAL = -1`
  - `INVALID_JOINTS = -2`
  - `OLD_HEADER_TIMESTAMP = -3`
  - `PATH_TOLERANCE_VIOLATED = -4`
  - `GOAL_TOLERANCE_VIOLATED = -5`

## 6. Point cloud structure (`PointCloud2`)

```
Header header
uint32 height             # 1 for unorganized, rows for organized
uint32 width              # points per row
PointField[] fields       # describes data layout
bool is_bigendian
uint32 point_step         # bytes per point
uint32 row_step           # bytes per row
uint8[] data              # raw binary data
bool is_dense             # true = no invalid points (no NaN/Inf)
```

### Field layout

The `fields` array describes what data each point contains:

| Common field name | Offset (typical) | Datatype | Size | Description |
|---|---|---|---|---|
| `x` | 0 | FLOAT32 (7) | 4 | X coordinate (meters) |
| `y` | 4 | FLOAT32 (7) | 4 | Y coordinate (meters) |
| `z` | 8 | FLOAT32 (7) | 4 | Z coordinate (meters) |
| `rgb` | 12 | FLOAT32 (7) | 4 | Packed RGB color (cast to uint32) |
| `intensity` | 12 | FLOAT32 (7) | 4 | Reflectance intensity |
| `ring` | 16 | UINT16 (4) | 2 | LiDAR ring/layer number |

### Key conventions

- **`is_dense`:** When `true`, every point is valid (no NaN/Inf in xyz).
  When `false`, consumers MUST check for NaN before using each point.
  Many LiDARs produce non-dense clouds where invalid returns are NaN.
- **Organized vs unorganized:**
  - `height == 1`: Unorganized (flat list of points). `width` = total points.
  - `height > 1`: Organized (2D grid, like a depth image). Preserves spatial
    structure from the sensor.
- **Packed RGB:** Color is stored as a single float32 that must be
  reinterpreted as uint32, then split into bytes:
  ```cpp
  uint32_t rgb_packed = *reinterpret_cast<const uint32_t*>(&point.rgb);
  uint8_t r = (rgb_packed >> 16) & 0xFF;
  uint8_t g = (rgb_packed >> 8) & 0xFF;
  uint8_t b = rgb_packed & 0xFF;
  ```
- **Do NOT manually iterate `data[]` byte by byte.** Use PCL's
  `pcl::fromROSMsg()` or `sensor_msgs::PointCloud2Iterator` for safe access.

### Using PointCloud2Iterator (without PCL)

```cpp
#include <sensor_msgs/point_cloud2_iterator.hpp>

sensor_msgs::msg::PointCloud2 cloud;
// ... set header, height, width ...

sensor_msgs::PointCloud2Modifier modifier(cloud);
modifier.setPointCloud2FieldsByString(1, "xyz");
modifier.resize(100);

sensor_msgs::PointCloud2Iterator<float> iter_x(cloud, "x");
sensor_msgs::PointCloud2Iterator<float> iter_y(cloud, "y");
sensor_msgs::PointCloud2Iterator<float> iter_z(cloud, "z");

for (size_t i = 0; i < 100; ++i, ++iter_x, ++iter_y, ++iter_z) {
  *iter_x = points[i].x;
  *iter_y = points[i].y;
  *iter_z = points[i].z;
}
```

## 7. Camera intrinsics (`CameraInfo`)

```
Header header
uint32 height
uint32 width
string distortion_model    # "plumb_bob" (5 params) or "equidistant" (4 params)
float64[] d                # distortion coefficients
float64[9] k               # 3x3 intrinsic camera matrix (row-major)
float64[9] r               # 3x3 rectification matrix
float64[12] p              # 3x4 projection matrix
```

### Matrix meanings

**K (Intrinsic matrix, 3×3):**
```
K = [fx  0  cx]
    [ 0 fy  cy]
    [ 0  0   1]
```
- `fx`, `fy`: Focal length in pixels
- `cx`, `cy`: Principal point (optical center) in pixels

**D (Distortion coefficients):**
- `plumb_bob` (radial-tangential): `[k1, k2, p1, p2, k3]` (5 values)
- `equidistant` (fisheye): `[k1, k2, k3, k4]` (4 values)

**P (Projection matrix, 3×4):**
```
P = [fx'  0  cx' Tx]
    [ 0  fy' cy' Ty]
    [ 0   0   1   0]
```
- For monocular cameras: `Tx = 0`, `Ty = 0`, and `fx' = fx`, `fy' = fy`,
  `cx' = cx`, `cy' = cy` after rectification.
- For stereo cameras: `Tx = -fx' * baseline` (left-right baseline in meters).

**R (Rectification matrix, 3×3):**
- Identity for monocular cameras.
- Aligns epipolar lines for stereo pairs.

### Usage rules

- **Always publish CameraInfo alongside Image** — downstream nodes
  (depth processing, AprilTag detection, visual SLAM) need intrinsics.
- **Timestamps must match** between Image and CameraInfo.
- **Generate from calibration**, not by hand — use `camera_calibration` package.
- The CameraInfo `width` and `height` must match the Image dimensions.

## 8. TF messages and QoS conventions

### `tf2_msgs/msg/TFMessage`

```
geometry_msgs/TransformStamped[] transforms
```

- **One message can contain multiple transforms.** A single
  `robot_state_publisher` publishes all link transforms in one TFMessage.
- Published on two topics with different QoS:

| Topic | QoS Durability | QoS Reliability | Content |
|---|---|---|---|
| `/tf` | VOLATILE | RELIABLE | Dynamic transforms (change over time) |
| `/tf_static` | TRANSIENT_LOCAL | RELIABLE | Static transforms (fixed forever) |

- **Static transforms are latched:** Late-subscribing nodes immediately receive
  all previously published static transforms thanks to TRANSIENT_LOCAL durability.
- **Dynamic transforms need continuous publishing.** If a broadcaster stops,
  the transform becomes stale and `lookupTransform` will eventually fail
  with extrapolation errors.

### Transform conventions

- **Each parent→child pair must have exactly ONE publisher.** Two nodes
  publishing the same transform creates flickering and "multiple authority" warnings.
- **Timestamps must be monotonically increasing.** Publishing a transform with
  an older timestamp than the last one causes "TF_OLD_DATA" warnings.
- **`tf2::TimePointZero`** (C++) or **`rclpy.time.Time()`** (Python) means
  "get the latest available transform" — use this for most lookups.

## 9. Action status codes

### `action_msgs/msg/GoalStatus`

Every ROS 2 action server reports goal status using these codes:

| Code | Constant | Meaning |
|---|---|---|
| 0 | `STATUS_UNKNOWN` | Goal status not set (should not occur) |
| 1 | `STATUS_ACCEPTED` | Goal accepted, waiting to be executed |
| 2 | `STATUS_EXECUTING` | Goal is currently being executed |
| 3 | `STATUS_CANCELING` | Cancel requested, still processing |
| 4 | `STATUS_SUCCEEDED` | Goal completed successfully |
| 5 | `STATUS_CANCELED` | Goal was canceled before completion |
| 6 | `STATUS_ABORTED` | Goal was aborted by the server (error) |

### Action feedback conventions

- **Feedback should be lightweight** — published at high frequency during execution.
  Do not put large data (images, point clouds) in feedback.
- **Result is published once** when the goal reaches a terminal state
  (SUCCEEDED, CANCELED, or ABORTED).
- **Goal IDs are UUIDs** — unique across the system and across time.

```python
# Checking action result
from action_msgs.msg import GoalStatus

if status == GoalStatus.STATUS_SUCCEEDED:
    self.get_logger().info('Goal succeeded')
elif status == GoalStatus.STATUS_ABORTED:
    self.get_logger().error('Goal aborted')
elif status == GoalStatus.STATUS_CANCELED:
    self.get_logger().warn('Goal canceled')
```

## 10. Diagnostic messages (`diagnostic_msgs`)

### diagnostic_msgs conventions

```python
from diagnostic_msgs.msg import DiagnosticStatus, DiagnosticArray, KeyValue

status = DiagnosticStatus()
status.level = DiagnosticStatus.OK      # 0=OK, 1=WARN, 2=ERROR, 3=STALE
status.name = 'my_robot: Motor Driver'  # Convention: "robot_name: Component"
status.hardware_id = 'motor_board_v2'   # Unique hardware identifier
status.message = 'Operating normally'
status.values = [
    KeyValue(key='voltage', value='24.1'),
    KeyValue(key='temperature_c', value='42.3'),
    KeyValue(key='error_count', value='0'),
]
```

Severity levels:

| Level | Value | Meaning |
|---|---|---|
| OK | 0 | Component operating normally |
| WARN | 1 | Degraded but functional |
| ERROR | 2 | Not functioning correctly |
| STALE | 3 | No recent data from component |

Use `diagnostic_updater` to publish diagnostics at regular intervals. See `references/debugging.md` for the updater pattern.

## 11. Covariance matrix conventions

Many messages (`Odometry`, `PoseWithCovariance`, `Imu`) flatten 2D covariance
matrices into 1D arrays in **row-major order**.

### 6×6 matrix (Pose or Twist in 3D)

Represented as `float64[36]`. Row/column order: **(x, y, z, roll, pitch, yaw)**.

```
Index layout:
     x    y    z    R    P    Y
x [  0    1    2    3    4    5  ]
y [  6    7    8    9   10   11  ]
z [ 12   13   14   15   16   17  ]
R [ 18   19   20   21   22   23  ]
P [ 24   25   26   27   28   29  ]
Y [ 30   31   32   33   34   35  ]

Diagonal (variances): indices 0, 7, 14, 21, 28, 35
```

```python
# Set variance for x=0.1m, y=0.1m, yaw=0.05rad
covariance = [0.0] * 36
covariance[0] = 0.01    # x variance (0.1² m²)
covariance[7] = 0.01    # y variance
covariance[35] = 0.0025 # yaw variance (0.05² rad²)
```

### 3×3 matrix (IMU data)

Represented as `float64[9]`. Row/column order: **(x, y, z)**.

```
Index layout:
     x   y   z
x [  0   1   2 ]
y [  3   4   5 ]
z [  6   7   8 ]

Diagonal (variances): indices 0, 4, 8
```

### Covariance rules

- **Never use exact `0.0` on the diagonal.** This tells EKF/SLAM nodes the
  measurement has zero uncertainty (infinite confidence), which causes
  matrix inversion errors and filter divergence.
  Use very small values instead: `1e-6`.
- **Unknown covariance:** Set the entire matrix to zeros and document that
  covariance is unknown. Some nodes treat all-zeros as "use default covariance."
- **IMU "data unavailable" signal:** Set `covariance[0] = -1.0` to indicate
  the sensor does not provide this measurement (see section 3).

```python
# BAD — zero variance causes EKF to explode
msg.pose.covariance[0] = 0.0   # "I know x with infinite precision"

# GOOD — small but nonzero
msg.pose.covariance[0] = 1e-6  # Very confident but numerically stable

# GOOD — realistic uncertainty from sensor specs
msg.pose.covariance[0] = 0.01  # 0.1m standard deviation → 0.01 variance
```

## 12. Standard units (REP-103)

ROS strictly adheres to SI units. **Never invent units or use non-SI units
in message payloads.**

| Quantity | Unit | Notes |
|---|---|---|
| Position / Distance | meters (m) | No centimeters, millimeters, or inches |
| Angle | radians (rad) | Never use degrees in message payloads |
| Linear velocity | m/s | |
| Angular velocity | rad/s | |
| Linear acceleration | m/s² | IMU includes gravity |
| Mass | kilograms (kg) | |
| Force | Newtons (N) | |
| Torque | Newton-meters (N·m) | |
| Frequency | Hertz (Hz) | Parameter values, not message fields |
| Temperature | Celsius (°C) | Exception to SI Kelvin (widely accepted in ROS) |
| Current | Amperes (A) | Battery monitoring |
| Voltage | Volts (V) | Battery monitoring |

### Depth image unit exception

`sensor_msgs/msg/Image` with encoding `16UC1` stores depth in **millimeters**
(uint16, range 0–65535 mm). This is a historical convention from RGB-D sensors
and is the one major exception to the meters rule. Encoding `32FC1` stores
depth in **meters** (float32).

| Encoding | Type | Unit | Max range |
|---|---|---|---|
| `16UC1` | uint16 | millimeters | 65.535 m |
| `32FC1` | float32 | meters | ~3.4 × 10³⁸ m |

### Quaternion normalization

Quaternions (`geometry_msgs/msg/Quaternion`) must always satisfy:

$$x^2 + y^2 + z^2 + w^2 = 1$$

- **Default `(0,0,0,0)` is INVALID** — crashes tf2.
- **Identity (no rotation) is `(0,0,0,1)`** — always initialize `w = 1.0`.
- Use `tf2::Quaternion::normalize()` (C++) or
  `tf_transformations.quaternion_multiply` (Python) to ensure normalization
  after manual construction.

## 13. Common failures and anti-patterns

| Anti-pattern | Why it fails | Fix |
|---|---|---|
| Using `0.0` for missing LiDAR data | Looks like an obstacle at zero distance | Use `Infinity` or `NaN` (or value outside `[range_min, range_max]`) |
| Leaving Quaternion uninitialized (Foxy) | Crashes tf2 ("Quaternion has length close to zero") | Humble+ defaults to `w=1.0`; still explicit-init for safety |
| Image published in `camera_link` | Point clouds and detections rotated 90° | Publish in `camera_optical_frame` |
| Setting IMU covariance to all `0.0` when no data | EKF treats it as "perfectly accurate" → filter diverges | Set `covariance[0] = -1.0` to signal "data unavailable" |
| Using `time.time()` for `header.stamp` | Fails during rosbag playback or Gazebo simulation | Use `node.get_clock().now()` (C++) or `.to_msg()` (Python) |
| Assuming JointState index order | Different publishers may order joints differently | Look up joint by `name`, never assume position by index |
| Zero diagonal in covariance matrix | Matrix inversion fails in EKF/SLAM → NaN propagation | Use `1e-6` minimum on diagonal |
| Manually iterating PointCloud2 `data[]` | Byte offset errors, endianness bugs | Use `pcl::fromROSMsg()` or `PointCloud2Iterator` |
| Not publishing CameraInfo with Image | 3D perception nodes silently fail | Always pair Image + CameraInfo on synchronized topics |
| Putting images in action feedback | Feedback published at high rate → bandwidth explosion | Use topics for streaming data, feedback for progress status only |
| Publishing same TF from two nodes | Frame flickers between two positions | Exactly one publisher per parent→child transform pair |
| `is_dense: true` with NaN in cloud | PCL algorithms crash on unexpected NaN | Set `is_dense: false` if any points may be NaN |
