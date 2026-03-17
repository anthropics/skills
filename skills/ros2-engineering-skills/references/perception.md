# Perception Pipelines

## Table of contents
1. image_transport
2. cv_bridge for OpenCV integration
3. Point cloud processing with PCL
4. Depth camera pipelines
5. Camera calibration
6. AprilTag / ArUco detection
7. Sensor fusion
8. ML model integration in ROS 2
9. Common failures and fixes

---

## 1. image_transport

`image_transport` provides transparent compression for image topics. Always
use it instead of raw `sensor_msgs/Image` publishers/subscribers — it
automatically handles raw, compressed (JPEG/PNG), and Theora video streams.

### Publisher (C++)

```cpp
#include <image_transport/image_transport.hpp>
#include <cv_bridge/cv_bridge.hpp>
#include <opencv2/opencv.hpp>

class CameraDriver : public rclcpp::Node
{
public:
  CameraDriver() : Node("camera_driver")
  {
    // image_transport publisher — automatically advertises:
    //   camera/image (raw)
    //   camera/image/compressed (JPEG)
    //   camera/image/compressedDepth (for depth images)
    //   camera/image/theora (video stream)
    it_pub_ = image_transport::create_publisher(this, "camera/image");

    // Also publish CameraInfo (required for 3D perception)
    info_pub_ = create_publisher<sensor_msgs::msg::CameraInfo>(
      "camera/camera_info", rclcpp::SensorDataQoS());

    timer_ = create_wall_timer(
      std::chrono::milliseconds(33),  // ~30 Hz
      std::bind(&CameraDriver::capture, this));
  }

private:
  void capture()
  {
    cv::Mat frame = grab_frame_from_camera();

    auto header = std_msgs::msg::Header();
    header.stamp = get_clock()->now();
    header.frame_id = "camera_optical_frame";

    auto msg = cv_bridge::CvImage(header, "bgr8", frame).toImageMsg();
    it_pub_.publish(*msg);

    auto info_msg = build_camera_info(header);
    info_pub_->publish(info_msg);
  }

  image_transport::Publisher it_pub_;
  rclcpp::Publisher<sensor_msgs::msg::CameraInfo>::SharedPtr info_pub_;
  rclcpp::TimerBase::SharedPtr timer_;
};
```

### Subscriber (C++)

```cpp
#include <image_transport/image_transport.hpp>
#include <cv_bridge/cv_bridge.hpp>

class ImageProcessor : public rclcpp::Node
{
public:
  ImageProcessor() : Node("image_processor")
  {
    // Subscribes to best available transport (compressed if available)
    it_sub_ = image_transport::create_subscription(
      this, "camera/image",
      std::bind(&ImageProcessor::image_callback, this, std::placeholders::_1),
      "compressed",  // Transport hint: prefer compressed
      rmw_qos_profile_sensor_data);
  }

private:
  void image_callback(const sensor_msgs::msg::Image::ConstSharedPtr & msg)
  {
    cv::Mat image = cv_bridge::toCvShare(msg, "bgr8")->image;
    // Process with OpenCV...
  }

  image_transport::Subscriber it_sub_;
};
```

### Compression parameters

```bash
# Set JPEG quality dynamically
ros2 param set /camera_driver /camera/image/compressed/jpeg_quality 50

# Set PNG compression level
ros2 param set /camera_driver /camera/image/compressed/png_level 3
```

## 2. cv_bridge for OpenCV integration

### ROS message ↔ OpenCV conversion

```cpp
#include <cv_bridge/cv_bridge.hpp>

// ROS Image → OpenCV Mat (zero-copy if possible)
void callback(const sensor_msgs::msg::Image::ConstSharedPtr & msg)
{
  // toCvShare: zero-copy (returns const reference, read-only)
  auto cv_ptr = cv_bridge::toCvShare(msg, "bgr8");
  const cv::Mat & image = cv_ptr->image;

  // toCvCopy: deep copy (when you need to modify the image)
  auto cv_copy = cv_bridge::toCvCopy(msg, "bgr8");
  cv::GaussianBlur(cv_copy->image, cv_copy->image, cv::Size(5, 5), 0);

  // Publish modified image
  pub_->publish(*cv_copy->toImageMsg());
}

// OpenCV Mat → ROS Image
cv::Mat processed;
auto out_msg = cv_bridge::CvImage(header, "bgr8", processed).toImageMsg();
```

### Encoding reference

| ROS encoding | OpenCV type | Channels | Use case |
|---|---|---|---|
| `bgr8` | `CV_8UC3` | 3 | Standard color image |
| `rgb8` | `CV_8UC3` | 3 | RGB color (some cameras) |
| `mono8` | `CV_8UC1` | 1 | Grayscale |
| `mono16` | `CV_16UC1` | 1 | Depth image (mm) |
| `32FC1` | `CV_32FC1` | 1 | Depth image (meters) |
| `bgra8` | `CV_8UC4` | 4 | Color with alpha |

### Python cv_bridge

```python
from cv_bridge import CvBridge
import cv2

bridge = CvBridge()

def image_callback(msg):
    # ROS → OpenCV
    cv_image = bridge.imgmsg_to_cv2(msg, desired_encoding='bgr8')

    # Process
    gray = cv2.cvtColor(cv_image, cv2.COLOR_BGR2GRAY)
    edges = cv2.Canny(gray, 50, 150)

    # OpenCV → ROS
    out_msg = bridge.cv2_to_imgmsg(edges, encoding='mono8')
    out_msg.header = msg.header
    publisher.publish(out_msg)
```

### Type adapters for perception (zero-copy cv::Mat)

Instead of using `cv_bridge::toCvCopy()` which copies the entire image, use a type adapter
(Humble+) to work natively with `cv::Mat` and let ROS handle serialization:

```cpp
#include <rclcpp/type_adapter.hpp>
#include <sensor_msgs/msg/image.hpp>
#include <cv_bridge/cv_bridge.hpp>

template<>
struct rclcpp::TypeAdapter<cv::Mat, sensor_msgs::msg::Image>
{
  using is_specialized = std::true_type;
  using custom_type = cv::Mat;
  using ros_message_type = sensor_msgs::msg::Image;

  static void convert_to_ros_message(const cv::Mat & source, sensor_msgs::msg::Image & destination) {
    cv_bridge::CvImage(std_msgs::msg::Header(), "bgr8", source).toImageMsg(destination);
  }
  static void convert_to_custom(const sensor_msgs::msg::Image & source, cv::Mat & destination) {
    destination = cv_bridge::toCvCopy(source, "bgr8")->image;
  }
};

// Define a convenient alias for the adapted type
using CvMatImage = rclcpp::TypeAdapter<cv::Mat, sensor_msgs::msg::Image>;

// Now publish cv::Mat directly — zero-copy when intra-process is enabled
auto pub = node->create_publisher<CvMatImage>("image", 10);
pub->publish(my_cv_mat);
```

Combined with intra-process communication, this eliminates ALL copies in an image processing pipeline.

## 3. Point cloud processing with PCL

### Subscribing to point clouds

```cpp
#include <sensor_msgs/msg/point_cloud2.hpp>
#include <pcl_conversions/pcl_conversions.h>
#include <pcl/point_types.h>
#include <pcl/filters/voxel_grid.h>
#include <pcl/filters/passthrough.h>
#include <pcl/segmentation/sac_segmentation.h>

class PointCloudProcessor : public rclcpp::Node
{
public:
  PointCloudProcessor() : Node("pcl_processor")
  {
    sub_ = create_subscription<sensor_msgs::msg::PointCloud2>(
      "points", rclcpp::SensorDataQoS(),
      std::bind(&PointCloudProcessor::cloud_callback, this, std::placeholders::_1));

    pub_ = create_publisher<sensor_msgs::msg::PointCloud2>(
      "filtered_points", rclcpp::SensorDataQoS());
  }

private:
  void cloud_callback(const sensor_msgs::msg::PointCloud2::ConstSharedPtr msg)
  {
    // ROS → PCL
    pcl::PointCloud<pcl::PointXYZ>::Ptr cloud(new pcl::PointCloud<pcl::PointXYZ>);
    pcl::fromROSMsg(*msg, *cloud);

    // Voxel grid downsampling (reduce point count)
    pcl::VoxelGrid<pcl::PointXYZ> voxel;
    voxel.setInputCloud(cloud);
    voxel.setLeafSize(0.01f, 0.01f, 0.01f);  // 1cm resolution
    pcl::PointCloud<pcl::PointXYZ>::Ptr filtered(new pcl::PointCloud<pcl::PointXYZ>);
    voxel.filter(*filtered);

    // Passthrough filter (crop to region of interest)
    pcl::PassThrough<pcl::PointXYZ> pass;
    pass.setInputCloud(filtered);
    pass.setFilterFieldName("z");
    pass.setFilterLimits(0.1, 2.0);  // Keep points 0.1m to 2.0m
    pcl::PointCloud<pcl::PointXYZ>::Ptr cropped(new pcl::PointCloud<pcl::PointXYZ>);
    pass.filter(*cropped);

    // PCL → ROS
    sensor_msgs::msg::PointCloud2 output;
    pcl::toROSMsg(*cropped, output);
    output.header = msg->header;
    pub_->publish(output);
  }

  rclcpp::Subscription<sensor_msgs::msg::PointCloud2>::SharedPtr sub_;
  rclcpp::Publisher<sensor_msgs::msg::PointCloud2>::SharedPtr pub_;
};
```

### Plane segmentation (RANSAC)

```cpp
// Find the dominant plane (e.g., table surface)
pcl::SACSegmentation<pcl::PointXYZ> seg;
seg.setOptimizeCoefficients(true);
seg.setModelType(pcl::SACMODEL_PLANE);
seg.setMethodType(pcl::SAC_RANSAC);
seg.setDistanceThreshold(0.01);  // 1cm inlier threshold
seg.setInputCloud(cloud);

pcl::ModelCoefficients::Ptr coefficients(new pcl::ModelCoefficients);
pcl::PointIndices::Ptr inliers(new pcl::PointIndices);
seg.segment(*inliers, *coefficients);

// Extract non-plane points (objects on the table)
pcl::ExtractIndices<pcl::PointXYZ> extract;
extract.setInputCloud(cloud);
extract.setIndices(inliers);
extract.setNegative(true);  // Keep points NOT on the plane
pcl::PointCloud<pcl::PointXYZ>::Ptr objects(new pcl::PointCloud<pcl::PointXYZ>);
extract.filter(*objects);
```

## 4. Depth camera pipelines

### RealSense D435/D455 setup

```bash
# Install RealSense ROS 2 wrapper
sudo apt install ros-jazzy-realsense2-camera

# Launch with aligned depth
ros2 launch realsense2_camera rs_launch.py \
  align_depth.enable:=true \
  pointcloud.enable:=true \
  depth_module.profile:=640x480x30 \
  rgb_camera.profile:=640x480x30
```

### Depth to point cloud pipeline

```
RealSense D435 → /camera/depth/image_rect_raw (depth)
                → /camera/color/image_raw (RGB)
                → /camera/depth/camera_info (intrinsics)
                       │
                       ▼
              depth_image_proc/point_cloud_xyzrgb
                       │
                       ▼
              /camera/depth/color/points (PointCloud2)
```

### Depth image processing

```cpp
void depth_callback(const sensor_msgs::msg::Image::ConstSharedPtr & depth_msg)
{
  auto cv_depth = cv_bridge::toCvShare(depth_msg, "16UC1");  // Depth in mm
  const cv::Mat & depth = cv_depth->image;

  // Get distance at pixel (320, 240) — center of VGA image
  uint16_t depth_mm = depth.at<uint16_t>(240, 320);
  double distance_m = depth_mm * 0.001;  // Convert mm to meters

  // Create obstacle mask: anything closer than 1m
  cv::Mat obstacle_mask;
  cv::inRange(depth, 1, 1000, obstacle_mask);  // 1mm to 1000mm = 0.001m to 1m
}
```

## 5. Camera calibration

### Intrinsic calibration

```bash
# Use ROS 2 camera_calibration package
ros2 run camera_calibration cameracalibrator \
  --size 8x6 \
  --square 0.025 \
  image:=/camera/image_raw \
  camera:=/camera
```

### Extrinsic calibration (camera-to-robot)

Use `hand_eye_calibration` or manual measurement:

```xml
<!-- In URDF — camera mount relative to base -->
<joint name="camera_joint" type="fixed">
  <parent link="base_link"/>
  <child link="camera_link"/>
  <origin xyz="0.3 0.0 0.5" rpy="0 0.3 0"/>
</joint>

<!-- Optical frame rotation (required!) -->
<joint name="camera_optical_joint" type="fixed">
  <parent link="camera_link"/>
  <child link="camera_optical_frame"/>
  <origin xyz="0 0 0" rpy="${-pi/2} 0 ${-pi/2}"/>
</joint>
```

**Optical frame convention:** ROS uses X-right, Y-down, Z-forward for camera
optical frames. This differs from the robot convention (X-forward, Y-left,
Z-up). The rotation above converts between them.

## 6. AprilTag / ArUco detection

### AprilTag detection

```bash
# Install
sudo apt install ros-jazzy-apriltag-ros

# Launch detector
ros2 run apriltag_ros apriltag_node --ros-args \
  -r image_rect:=/camera/image_raw \
  -r camera_info:=/camera/camera_info \
  -p family:=36h11 \
  -p size:=0.05  # Tag size in meters
```

### Using detected tags for localization

```python
from apriltag_msgs.msg import AprilTagDetectionArray

def tag_callback(msg: AprilTagDetectionArray):
    for detection in msg.detections:
        tag_id = detection.id
        # Pose is in camera_optical_frame
        pose = detection.pose.pose.pose
        # Use TF2 to transform to base_link or map frame
```

## 7. Sensor fusion

### Time synchronization for multi-sensor

```cpp
#include <message_filters/subscriber.h>
#include <message_filters/sync_policies/approximate_time.h>
#include <message_filters/synchronizer.h>

using SyncPolicy = message_filters::sync_policies::ApproximateTime<
  sensor_msgs::msg::Image,
  sensor_msgs::msg::Image>;

class RGBDProcessor : public rclcpp::Node
{
public:
  RGBDProcessor() : Node("rgbd_processor")
  {
    rgb_sub_.subscribe(this, "camera/color/image_raw");
    depth_sub_.subscribe(this, "camera/depth/image_rect_raw");

    sync_ = std::make_shared<message_filters::Synchronizer<SyncPolicy>>(
      SyncPolicy(10), rgb_sub_, depth_sub_);
    sync_->registerCallback(
      std::bind(&RGBDProcessor::synced_callback, this,
                std::placeholders::_1, std::placeholders::_2));
  }

private:
  void synced_callback(
    const sensor_msgs::msg::Image::ConstSharedPtr & rgb,
    const sensor_msgs::msg::Image::ConstSharedPtr & depth)
  {
    // Both images are time-synchronized
    auto cv_rgb = cv_bridge::toCvShare(rgb, "bgr8")->image;
    auto cv_depth = cv_bridge::toCvShare(depth, "16UC1")->image;
    // Process synchronized RGB-D pair...
  }

  message_filters::Subscriber<sensor_msgs::msg::Image> rgb_sub_;
  message_filters::Subscriber<sensor_msgs::msg::Image> depth_sub_;
  std::shared_ptr<message_filters::Synchronizer<SyncPolicy>> sync_;
};
```

### robot_localization (EKF sensor fusion)

```yaml
# ekf.yaml — fuse wheel odometry + IMU
ekf_filter_node:
  ros__parameters:
    frequency: 50.0
    sensor_timeout: 0.1
    two_d_mode: true
    publish_tf: true

    map_frame: map
    odom_frame: odom
    base_link_frame: base_link
    world_frame: odom

    odom0: /wheel_odom
    odom0_config: [true, true, false,     # x, y, z
                   false, false, true,     # roll, pitch, yaw
                   false, false, false,    # vx, vy, vz
                   false, false, true,     # vroll, vpitch, vyaw
                   false, false, false]    # ax, ay, az

    imu0: /imu/data
    imu0_config: [false, false, false,
                  false, false, true,      # yaw from IMU
                  false, false, false,
                  false, false, true,      # vyaw from IMU
                  true, false, false]      # ax from IMU
```

## 8. ML model integration in ROS 2

### YOLO detection node pattern

```python
import rclpy
from rclpy.node import Node
from sensor_msgs.msg import Image
from vision_msgs.msg import Detection2DArray, Detection2D, ObjectHypothesisWithPose
from cv_bridge import CvBridge
from ultralytics import YOLO

class YOLODetector(Node):
    def __init__(self):
        super().__init__('yolo_detector')
        self.declare_parameter('model_path', 'yolov8n.pt')
        self.declare_parameter('confidence_threshold', 0.5)

        model_path = self.get_parameter('model_path').value
        self.conf_threshold = self.get_parameter('confidence_threshold').value

        self.model = YOLO(model_path)
        self.bridge = CvBridge()

        self.sub = self.create_subscription(
            Image, 'camera/image_raw', self.detect, 10)
        self.pub = self.create_publisher(
            Detection2DArray, 'detections', 10)
        self.debug_pub = self.create_publisher(
            Image, 'detection_image', 10)

    def detect(self, msg: Image):
        frame = self.bridge.imgmsg_to_cv2(msg, 'bgr8')
        results = self.model(frame, conf=self.conf_threshold, verbose=False)

        det_array = Detection2DArray()
        det_array.header = msg.header

        for result in results:
            for box in result.boxes:
                det = Detection2D()
                det.header = msg.header

                # Bounding box
                x1, y1, x2, y2 = box.xyxy[0].cpu().numpy()
                det.bbox.center.position.x = float((x1 + x2) / 2)
                det.bbox.center.position.y = float((y1 + y2) / 2)
                det.bbox.size_x = float(x2 - x1)
                det.bbox.size_y = float(y2 - y1)

                # Classification
                hyp = ObjectHypothesisWithPose()
                hyp.hypothesis.class_id = str(int(box.cls[0]))
                hyp.hypothesis.score = float(box.conf[0])
                det.results.append(hyp)

                det_array.detections.append(det)

        self.pub.publish(det_array)
```

### Performance tips for ML inference

- Run inference on a separate thread or process (don't block executor)
- Use GPU inference (CUDA, TensorRT) for real-time requirements
- Use `image_transport` with compression to reduce bandwidth to inference node
- Consider running the model as a service (request/response) for non-real-time use cases
- Pre-warm the model in `on_configure` to avoid first-inference latency

### Isaac ROS for GPU-accelerated perception (Jetson)

NVIDIA Isaac ROS provides GPU-accelerated perception packages for Jetson platforms:
- `isaac_ros_visual_slam`: GPU-accelerated visual SLAM
- `isaac_ros_object_detection`: DNN-based detection (SSD, YOLO)
- `isaac_ros_apriltag`: GPU-accelerated AprilTag detection
- `isaac_ros_depth_segmentation`: Depth-based segmentation

These use NITROS for zero-copy GPU memory transfer between nodes. Install via Isaac ROS apt repository, not standard ROS 2 repos.

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Image appears blue/red swapped | BGR vs RGB encoding mismatch | Check source encoding; use `bgr8` for OpenCV, `rgb8` for some cameras |
| Point cloud is empty | Depth camera not producing data or wrong topic | Check `ros2 topic echo` on depth topic, verify camera is running |
| `cv_bridge` conversion error | Encoding mismatch between source and requested | Use `toCvCopy(msg, "")` with empty encoding to keep original format |
| Synchronized callback never fires | Timestamps too far apart between sensors | Increase `ApproximateTime` queue size, verify sensor clock sync |
| Depth values are all 0 or NaN | Camera too close/far, IR interference | Adjust min/max depth, check for reflective surfaces |
| Camera image is dark/overexposed | Auto-exposure not configured | Set camera exposure params via ROS parameters or vendor tools |
| PCL processing is too slow | Too many points, no downsampling | Apply `VoxelGrid` filter first, reduce point cloud resolution |
| TF error when transforming detections | Camera optical frame not in TF tree | Add optical frame joint to URDF (rotation from camera_link) |
