# Expected: QoS Compatibility Analysis

## Required Elements

### 1. Incompatibility Identification
- Must state that BEST_EFFORT publisher is incompatible with RELIABLE subscriber
- Must mention this is a RELIABILITY mismatch
- Must explain that DDS will silently drop the connection (no error at runtime)

### 2. DDS RxO Explanation
- Must reference Request-vs-Offered (RxO) semantics
- Must explain: subscriber's requested QoS must be <= publisher's offered QoS
- Must note: RELIABLE > BEST_EFFORT in the QoS hierarchy
- A BEST_EFFORT publisher cannot satisfy a RELIABLE subscriber's request

### 3. Fix Suggestions
At least one of the following must be present:
- **Option A**: Change subscriber to BEST_EFFORT (recommended for sensor streams)
  - Code example using `rclpy.qos.QoSProfile` or `rclcpp::QoS`
- **Option B**: Change publisher to RELIABLE (not recommended for high-rate sensors)
  - Warning about performance impact at high frame rates

### 4. Debugging Command
- Must mention `ros2 topic info /camera/image_raw -v` to inspect QoS profiles
- May mention `ros2 doctor` for general diagnostics

### 5. Best Practice Reference
- Should reference the sensor stream QoS preset (BEST_EFFORT/VOLATILE/KEEP_LAST)
- Should note depth=5 vs depth=10 mismatch as a minor warning (not blocking)
