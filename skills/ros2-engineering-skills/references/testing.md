# Testing

## Table of contents
1. Unit testing with gtest (C++) and pytest (Python)
2. Node-level testing
3. launch_testing for integration tests
4. Mock hardware for ros2_control
5. Test fixtures and helpers
6. Code coverage
7. CI/CD pipeline design
8. Rosbag-based regression testing
9. Common failures and fixes

---

## 1. Unit testing with gtest (C++) and pytest (Python)

### gtest (C++)

```cpp
// test/test_controller_math.cpp
#include <gtest/gtest.h>
#include "my_robot_control/pid_controller.hpp"

class PIDTest : public ::testing::Test
{
protected:
  void SetUp() override
  {
    pid_ = std::make_unique<my_robot_control::PIDController>(1.0, 0.1, 0.01);
  }

  std::unique_ptr<my_robot_control::PIDController> pid_;
};

TEST_F(PIDTest, ZeroErrorProducesZeroOutput)
{
  double output = pid_->compute(0.0, 0.01);
  EXPECT_DOUBLE_EQ(output, 0.0);
}

TEST_F(PIDTest, ProportionalResponse)
{
  double output = pid_->compute(1.0, 0.01);
  EXPECT_GT(output, 0.0);  // Positive error → positive output
}

TEST_F(PIDTest, IntegralWindup)
{
  // Sustained error should accumulate
  double prev_output = 0.0;
  for (int i = 0; i < 100; ++i) {
    double output = pid_->compute(1.0, 0.01);
    EXPECT_GE(output, prev_output);  // Integral accumulates
    prev_output = output;
  }
}

TEST_F(PIDTest, DerivativeResponse)
{
  // Sudden change in error should produce derivative kick
  pid_->compute(0.0, 0.01);  // Baseline
  double output = pid_->compute(10.0, 0.01);  // Sudden error
  EXPECT_GT(output, 10.0);  // D-term adds to P-term
}
```

### CMakeLists.txt for gtest

```cmake
if(BUILD_TESTING)
  find_package(ament_lint_auto REQUIRED)
  ament_lint_auto_find_test_dependencies()

  find_package(ament_cmake_gtest REQUIRED)

  # Unit test (no ROS dependencies)
  ament_add_gtest(test_controller_math test/test_controller_math.cpp)
  target_link_libraries(test_controller_math ${PROJECT_NAME}_lib)

  # Unit test with ROS deps
  ament_add_gtest(test_node_logic test/test_node_logic.cpp)
  target_link_libraries(test_node_logic ${PROJECT_NAME}_lib)
  ament_target_dependencies(test_node_logic rclcpp sensor_msgs)
endif()
```

### pytest (Python)

```python
# test/test_utils.py
import pytest
from my_robot_monitor.utils import clamp, moving_average


def test_clamp_within_range():
    assert clamp(5.0, 0.0, 10.0) == 5.0


def test_clamp_below_min():
    assert clamp(-1.0, 0.0, 10.0) == 0.0


def test_clamp_above_max():
    assert clamp(15.0, 0.0, 10.0) == 10.0


def test_moving_average_empty():
    ma = moving_average(window_size=5)
    assert ma.value is None


def test_moving_average_full_window():
    ma = moving_average(window_size=3)
    ma.add(1.0)
    ma.add(2.0)
    ma.add(3.0)
    assert ma.value == pytest.approx(2.0)
```

### setup.cfg for pytest

```ini
[tool:pytest]
testpaths = test
python_files = test_*.py
python_classes = Test*
python_functions = test_*
```

## 2. Node-level testing

### Testing a ROS 2 node (C++)

```cpp
// test/test_joint_publisher.cpp
#include <gtest/gtest.h>
#include <rclcpp/rclcpp.hpp>
#include <sensor_msgs/msg/joint_state.hpp>
#include "my_robot_driver/joint_publisher_node.hpp"

class JointPublisherTest : public ::testing::Test
{
protected:
  static void SetUpTestSuite() { rclcpp::init(0, nullptr); }
  static void TearDownTestSuite() { rclcpp::shutdown(); }

  void SetUp() override
  {
    node_ = std::make_shared<my_robot_driver::JointPublisher>();
    test_node_ = std::make_shared<rclcpp::Node>("test_helper");

    received_ = false;
    sub_ = test_node_->create_subscription<sensor_msgs::msg::JointState>(
      "joint_states", 10,
      [this](const sensor_msgs::msg::JointState::ConstSharedPtr msg) {
        last_msg_ = msg;
        received_ = true;
      });
  }

  bool spin_until_received(std::chrono::seconds timeout = std::chrono::seconds(5))
  {
    auto start = std::chrono::steady_clock::now();
    rclcpp::executors::SingleThreadedExecutor executor;
    executor.add_node(node_);
    executor.add_node(test_node_);

    while (!received_ &&
           std::chrono::steady_clock::now() - start < timeout)
    {
      executor.spin_some(std::chrono::milliseconds(10));
    }
    return received_;
  }

  std::shared_ptr<my_robot_driver::JointPublisher> node_;
  std::shared_ptr<rclcpp::Node> test_node_;
  rclcpp::Subscription<sensor_msgs::msg::JointState>::SharedPtr sub_;
  sensor_msgs::msg::JointState::ConstSharedPtr last_msg_;
  bool received_ = false;
};

TEST_F(JointPublisherTest, PublishesJointStates)
{
  ASSERT_TRUE(spin_until_received());
  EXPECT_FALSE(last_msg_->name.empty());
  EXPECT_EQ(last_msg_->name.size(), last_msg_->position.size());
}

TEST_F(JointPublisherTest, HasValidTimestamp)
{
  ASSERT_TRUE(spin_until_received());
  rclcpp::Time stamp(last_msg_->header.stamp);
  EXPECT_GT(stamp.nanoseconds(), 0);
}
```

### Testing a ROS 2 node (Python)

```python
# test/test_monitor_node.py
import pytest
import rclpy
from rclpy.executors import SingleThreadedExecutor
from std_msgs.msg import String
from my_robot_monitor.monitor_node import MonitorNode
import threading
import time


@pytest.fixture(scope='module')
def rclpy_init():
    rclpy.init()
    yield
    rclpy.shutdown()


@pytest.fixture
def monitor_node(rclpy_init):
    node = MonitorNode()
    yield node
    node.destroy_node()


def test_node_publishes_status(monitor_node):
    received = []
    helper = rclpy.create_node('test_helper')

    sub = helper.create_subscription(
        String, 'robot_status', lambda msg: received.append(msg), 10)

    executor = SingleThreadedExecutor()
    executor.add_node(monitor_node)
    executor.add_node(helper)

    # Spin for up to 3 seconds
    start = time.time()
    while len(received) == 0 and time.time() - start < 3.0:
        executor.spin_once(timeout_sec=0.1)

    assert len(received) > 0
    helper.destroy_node()
```

## 3. launch_testing for integration tests

### Basic launch integration test

```python
# test/test_driver_integration.launch.py
import unittest
import launch
import launch.actions
import launch_testing
import launch_testing.actions
import launch_testing.markers
from launch_ros.actions import Node
import rclpy
from sensor_msgs.msg import JointState

@launch_testing.markers.keep_alive
def generate_test_description():
    driver_node = Node(
        package='my_robot_driver',
        executable='driver_node',
        name='driver',
        parameters=[{
            'use_sim_time': True,
            'publish_rate': 50.0,
        }],
    )

    return (
        launch.LaunchDescription([
            driver_node,
            launch_testing.actions.ReadyToTest(),
        ]),
        {'driver': driver_node},
    )


class TestDriverIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        rclpy.init()
        cls.node = rclpy.create_node('test_node')

    @classmethod
    def tearDownClass(cls):
        cls.node.destroy_node()
        rclpy.shutdown()

    def test_joint_states_published(self):
        """Verify driver publishes joint states within 5 seconds."""
        msgs_received = []

        sub = self.node.create_subscription(
            JointState, 'joint_states',
            lambda msg: msgs_received.append(msg), 10)

        end_time = self.node.get_clock().now() + rclpy.duration.Duration(seconds=5)
        while (self.node.get_clock().now() < end_time and
               len(msgs_received) == 0):
            rclpy.spin_once(self.node, timeout_sec=0.1)

        self.node.destroy_subscription(sub)
        self.assertGreater(len(msgs_received), 0,
                          'No JointState messages received within 5 seconds')

    def test_joint_state_has_correct_joints(self):
        """Verify joint names match expected configuration."""
        msg_received = [None]

        sub = self.node.create_subscription(
            JointState, 'joint_states',
            lambda msg: msg_received.__setitem__(0, msg), 10)

        end_time = self.node.get_clock().now() + rclpy.duration.Duration(seconds=5)
        while self.node.get_clock().now() < end_time and msg_received[0] is None:
            rclpy.spin_once(self.node, timeout_sec=0.1)

        self.node.destroy_subscription(sub)
        self.assertIsNotNone(msg_received[0])
        self.assertIn('joint_1', msg_received[0].name)


@launch_testing.post_shutdown_test()
class TestShutdown(unittest.TestCase):
    def test_exit_codes(self, proc_info):
        """Verify all processes exited cleanly."""
        launch_testing.asserts.assertExitCodes(proc_info)
```

### CMakeLists.txt for launch tests

```cmake
if(BUILD_TESTING)
  find_package(launch_testing_ament_cmake REQUIRED)
  add_launch_test(test/test_driver_integration.launch.py
    TIMEOUT 30
  )
endif()
```

### Running tests

```bash
# Run all tests for a package
colcon test --packages-select my_robot_driver

# View test results
colcon test-result --verbose

# Run specific launch test directly
launch_test test/test_driver_integration.launch.py
```

## 4. Mock hardware for ros2_control

### Using mock_components for testing

```xml
<!-- test_robot.urdf.xacro — use mock hardware for testing -->
<ros2_control name="TestSystem" type="system">
  <hardware>
    <plugin>mock_components/GenericSystem</plugin>
    <param name="mock_sensor_commands">true</param>
    <param name="state_following_offset">0.0</param>
  </hardware>
  <joint name="joint_1">
    <command_interface name="position"/>
    <state_interface name="position"><param name="initial_value">0.0</param></state_interface>
    <state_interface name="velocity"/>
  </joint>
</ros2_control>
```

### Controller integration test

```python
# test/test_controller_loading.launch.py
def generate_test_description():
    robot_description = Command(['xacro ', test_urdf_path])

    control_node = Node(
        package='controller_manager',
        executable='ros2_control_node',
        parameters=[
            {'robot_description': robot_description},
            test_controllers_yaml,
        ],
    )

    spawn_jsb = Node(
        package='controller_manager',
        executable='spawner',
        arguments=['joint_state_broadcaster'],
    )

    return launch.LaunchDescription([
        control_node,
        spawn_jsb,
        launch_testing.actions.ReadyToTest(),
    ])

class TestControllerLoading(unittest.TestCase):
    def test_joint_state_broadcaster_active(self):
        """Verify joint_state_broadcaster loads and activates."""
        import subprocess
        result = subprocess.run(
            ['ros2', 'control', 'list_controllers'],
            capture_output=True, text=True, timeout=10)
        self.assertIn('joint_state_broadcaster', result.stdout)
        self.assertIn('active', result.stdout)
```

## 5. Test fixtures and helpers

### ROS 2 test fixture pattern (C++)

```cpp
class ROS2TestFixture : public ::testing::Test
{
protected:
  static void SetUpTestSuite()
  {
    rclcpp::init(0, nullptr);
  }

  static void TearDownTestSuite()
  {
    rclcpp::shutdown();
  }

  void SetUp() override
  {
    executor_ = std::make_shared<rclcpp::executors::SingleThreadedExecutor>();
  }

  void spin_for(std::chrono::milliseconds duration)
  {
    auto start = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - start < duration) {
      executor_->spin_some(std::chrono::milliseconds(10));
    }
  }

  std::shared_ptr<rclcpp::executors::SingleThreadedExecutor> executor_;
};
```

### Python test helper for waiting on conditions

```python
def wait_for_condition(node, condition_fn, timeout_sec=5.0):
    """Spin the node until condition_fn() returns True or timeout."""
    import time
    start = time.time()
    while time.time() - start < timeout_sec:
        rclpy.spin_once(node, timeout_sec=0.1)
        if condition_fn():
            return True
    return False
```

## 6. Code coverage

### C++ coverage with lcov

```bash
# Build with coverage flags
colcon build --packages-select my_robot_driver \
  --cmake-args -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="--coverage" \
  -DCMAKE_C_FLAGS="--coverage"

# Run tests
colcon test --packages-select my_robot_driver

# Generate coverage report
lcov --capture --directory build/my_robot_driver \
  --output-file coverage.info \
  --ignore-errors mismatch

# Remove system headers from report
lcov --remove coverage.info '/usr/*' '/opt/*' \
  --output-file coverage_filtered.info

# Generate HTML report
genhtml coverage_filtered.info --output-directory coverage_html
```

### Python coverage with pytest-cov

```bash
# Install
pip install pytest-cov

# Run with coverage
cd src/my_robot_monitor
python -m pytest --cov=my_robot_monitor --cov-report=html test/
```

## 7. CI/CD pipeline design

### GitHub Actions for ROS 2

```yaml
# .github/workflows/ci.yaml
name: CI
on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  build-and-test:
    runs-on: ubuntu-24.04
    container:
      image: ros:jazzy
    steps:
      - uses: actions/checkout@v4
        with:
          path: src/my_robot

      # Cache rosdep and build artifacts
      - name: Cache dependencies
        uses: actions/cache@v4
        with:
          path: |
            /opt/ros/jazzy
            ~/.cache/ccache
          key: ros-jazzy-${{ hashFiles('src/my_robot/**/package.xml') }}

      - name: Install dependencies
        run: |
          apt-get update
          rosdep update
          rosdep install --from-paths src --ignore-src -y

      - name: Build
        run: |
          source /opt/ros/jazzy/setup.bash
          colcon build --cmake-args -DCMAKE_BUILD_TYPE=RelWithDebInfo \
            -DCMAKE_CXX_FLAGS="-Wall -Wextra -Wpedantic"

      - name: Test
        run: |
          source /opt/ros/jazzy/setup.bash
          source install/setup.bash
          colcon test --event-handlers console_cohesion+
          colcon test-result --verbose
```

### industrial_ci (de facto standard)

`industrial_ci` from ROS-Industrial is the most widely used CI tool for ROS packages.
It handles multi-distro builds, linting, and testing in a single Docker-based workflow:

```yaml
# .github/workflows/industrial_ci.yml
name: Industrial CI
on: [push, pull_request]

jobs:
  industrial_ci:
    strategy:
      matrix:
        ROS_DISTRO: [humble, jazzy]
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: ros-industrial/industrial_ci@master
        env:
          ROS_DISTRO: ${{ matrix.ROS_DISTRO }}
          # Optional: run specific tests
          # AFTER_INSTALL_TARGET_DEPENDENCIES: 'apt-get install -y ros-$ROS_DISTRO-nav2-bringup'
```

### Simulation-in-the-loop testing

Run Gazebo headless in CI for physics-based integration tests:

```yaml
    steps:
      - uses: actions/checkout@v4
      - uses: ros-industrial/industrial_ci@master
        env:
          ROS_DISTRO: jazzy
          DOCKER_RUN_OPTS: '-e DISPLAY=:99'
          BEFORE_INSTALL_TARGET_DEPENDENCIES: |
            apt-get update && apt-get install -y xvfb
            Xvfb :99 -screen 0 1024x768x24 &
          ADDITIONAL_DEBS: 'ros-jazzy-ros-gz'
```

### Key CI practices

- **Cache `/opt/ros/`, `build/`, `install/`, `.ccache/`** — reduces build from 15 min to 3 min
- **Use `colcon test-result --verbose`** — fail the CI if any test fails
- **Run linters:** `ament_lint_auto` checks copyright, style, naming
- **Test in container:** Use official `ros:jazzy` image for reproducibility
- **Matrix builds:** Test across Humble + Jazzy if supporting both

## 8. Rosbag-based regression testing

### Rosbag regression testing

Record expected outputs as MCAP bags, then replay inputs and diff outputs:

```bash
# Record baseline
ros2 bag record /output_topic -o baseline_bag --compression-mode file --compression-format zstd

# In CI: replay input, record output, compare
ros2 bag play input_bag --clock &
ros2 bag record /output_topic -o test_output --max-duration 30 &
# Compare with baseline using custom diff tool
```

### Recording test data

```bash
# Record specific topics for regression testing
ros2 bag record -o test_data \
  /joint_states \
  /scan \
  /camera/image_raw/compressed \
  /tf /tf_static \
  --max-bag-duration 30  # 30 second segments
```

### Playback-based test

```python
# test/test_perception_regression.launch.py
def generate_test_description():
    bag_play = ExecuteProcess(
        cmd=['ros2', 'bag', 'play', test_bag_path,
             '--clock', '--rate', '1.0'],
    )

    detector_node = Node(
        package='my_robot_perception',
        executable='detector_node',
        parameters=[{'use_sim_time': True}],
    )

    return launch.LaunchDescription([
        bag_play,
        detector_node,
        launch_testing.actions.ReadyToTest(),
    ])

class TestPerceptionRegression(unittest.TestCase):
    def test_detects_known_objects(self):
        """Verify detector finds objects that were present in recorded bag."""
        detections = []
        sub = self.node.create_subscription(
            Detection2DArray, 'detections',
            lambda msg: detections.extend(msg.detections), 10)

        wait_for_condition(self.node, lambda: len(detections) > 0, timeout_sec=10)
        self.assertGreater(len(detections), 0, 'No detections from known test data')
```

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| `SetUpTestSuite` crashes with "context already initialized" | Multiple test files each calling `rclcpp::init` | Use `rclcpp::init(0, nullptr)` with `InitOptions` or single test suite |
| Test passes locally, fails in CI | Timing-dependent (race condition) | Use `spin_until` patterns with timeouts, not `sleep` |
| launch_testing hangs on shutdown | Node doesn't shut down cleanly | Add `SignalProcess` on shutdown, use `@keep_alive` decorator |
| Coverage report shows 0% | Missing `--coverage` flag or wrong build directory | Verify CMake flags, ensure `lcov` points to correct build dir |
| `colcon test-result` shows "no tests" | Test not registered in CMakeLists.txt | Add `ament_add_gtest` or `add_launch_test` |
| Python test can't import package | Package not installed / not on PYTHONPATH | `source install/setup.bash` before running tests |
| Mock hardware behaves differently than real | GenericSystem has perfect response | Test with realistic delays and noise in mock hardware |
| CI build takes too long | No caching, full rebuild every time | Cache `build/`, `install/`, `.ccache/`, rosdep install |
