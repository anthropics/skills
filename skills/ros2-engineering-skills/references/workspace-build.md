# Workspace and Build System

## Table of contents
1. Workspace layout
2. colcon essentials
3. ament_cmake in depth
4. ament_python and mixed packages
5. package.xml format 3
6. Overlay mechanics
7. Build optimization
8. Dependency management
9. Common failures and fixes

---

## 1. Workspace layout

```
ros2_ws/
├── src/
│   ├── my_robot_bringup/       # Launch files, top-level config
│   ├── my_robot_description/   # URDF/xacro, meshes
│   ├── my_robot_interfaces/    # msg/srv/action definitions
│   ├── my_robot_driver/        # Hardware driver (C++)
│   ├── my_robot_control/       # Controllers, ros2_control config
│   ├── my_robot_perception/    # Camera/LiDAR processing
│   └── my_robot_navigation/    # Nav2 config and custom plugins
├── build/      # Build artifacts (never commit)
├── install/    # Install space (never commit)
└── log/        # Build and test logs
```

**Why this decomposition matters:**
- Interface packages compile first with zero downstream deps — fast CI iteration
- Description packages are pure data — no code compilation, instant rebuild
- Driver packages isolate hardware deps — other packages stay testable without hardware
- Bringup packages contain only launch and config — change robot configuration without recompiling

## 2. colcon essentials

### Build commands

```bash
# Full workspace build
colcon build --symlink-install

# Single package with dependencies
colcon build --packages-up-to my_robot_driver

# Single package only (skip deps, fast iteration)
colcon build --packages-select my_robot_driver

# Release build for deployment
colcon build --cmake-args -DCMAKE_BUILD_TYPE=Release

# Parallel jobs control (useful on resource-limited boards)
colcon build --parallel-workers 2

# Export compile_commands.json for IDE integration
colcon build --cmake-args -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
```

### colcon mixins (speed up repeated builds)

```bash
# Install mixin repo
colcon mixin add default https://raw.githubusercontent.com/colcon/colcon-mixin-repository/master/index.yaml
colcon mixin update default

# Use release mixin
colcon build --mixin release

# Use ccache mixin (dramatically speeds up rebuilds)
colcon build --mixin ccache
```

### Build isolation

colcon builds each package in isolation by default. This means:
- Each package gets its own `build/<pkg>` directory
- CMake cannot accidentally see headers from sibling packages
- Missing `find_package()` or `package.xml` deps break the build immediately (good)

To merge all packages into a single install prefix (not recommended — hides
missing `package.xml` dependencies, but simplifies Docker `PATH`/`LD_LIBRARY_PATH`):
```bash
colcon build --merge-install
```

## 3. ament_cmake in depth

### Minimal CMakeLists.txt for a library + node

```cmake
cmake_minimum_required(VERSION 3.8)
project(my_robot_driver)

# Compiler settings
if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# Dependencies
find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_lifecycle REQUIRED)
find_package(sensor_msgs REQUIRED)
find_package(my_robot_interfaces REQUIRED)

# Library (reusable logic, testable without ROS)
add_library(${PROJECT_NAME}_lib SHARED
  src/driver_core.cpp
  src/serial_transport.cpp
)
target_include_directories(${PROJECT_NAME}_lib PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include/${PROJECT_NAME}>
)
ament_target_dependencies(${PROJECT_NAME}_lib
  rclcpp rclcpp_lifecycle sensor_msgs my_robot_interfaces
)
# NOTE: ament_target_dependencies() is deprecated starting from Kilted (May 2025).
# For forward compatibility, prefer target_link_libraries() with modern CMake targets:
#   target_link_libraries(${PROJECT_NAME}_lib PUBLIC
#     rclcpp::rclcpp rclcpp_lifecycle::rclcpp_lifecycle
#     ${sensor_msgs_TARGETS} ${my_robot_interfaces_TARGETS}
#   )

# Executable (thin wrapper around library)
add_executable(driver_node src/driver_node_main.cpp)
target_link_libraries(driver_node ${PROJECT_NAME}_lib)

# Install
install(TARGETS ${PROJECT_NAME}_lib
  EXPORT export_${PROJECT_NAME}
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
)
install(TARGETS driver_node DESTINATION lib/${PROJECT_NAME})
install(DIRECTORY include/ DESTINATION include/${PROJECT_NAME})
install(DIRECTORY launch config DESTINATION share/${PROJECT_NAME})

# Testing
if(BUILD_TESTING)
  find_package(ament_lint_auto REQUIRED)
  ament_lint_auto_find_test_dependencies()

  find_package(ament_cmake_gtest REQUIRED)
  ament_add_gtest(test_driver_core test/test_driver_core.cpp)
  target_link_libraries(test_driver_core ${PROJECT_NAME}_lib)
endif()

# Export
ament_export_targets(export_${PROJECT_NAME} HAS_LIBRARY_TARGET)
ament_export_dependencies(rclcpp rclcpp_lifecycle sensor_msgs my_robot_interfaces)
ament_package()
```

### Component registration (for composition)

```cmake
# In addition to the above, register as a composable node
find_package(rclcpp_components REQUIRED)

add_library(driver_component SHARED src/driver_component.cpp)
target_link_libraries(driver_component ${PROJECT_NAME}_lib)
ament_target_dependencies(driver_component rclcpp rclcpp_components)

rclcpp_components_register_nodes(driver_component "my_robot_driver::DriverComponent")

install(TARGETS driver_component
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
)
```

### Interface package CMakeLists.txt

```cmake
cmake_minimum_required(VERSION 3.8)
project(my_robot_interfaces)

find_package(ament_cmake REQUIRED)
find_package(rosidl_default_generators REQUIRED)
find_package(geometry_msgs REQUIRED)
find_package(std_msgs REQUIRED)

rosidl_generate_interfaces(${PROJECT_NAME}
  "msg/RobotStatus.msg"
  "msg/SensorData.msg"
  "srv/SetMode.srv"
  "action/MoveToPosition.action"
  DEPENDENCIES geometry_msgs std_msgs
)

ament_export_dependencies(rosidl_default_runtime)
ament_package()
```

## 4. ament_python and mixed packages

### Pure Python package (setup.py)

```python
from setuptools import find_packages, setup

package_name = 'my_robot_monitor'

setup(
    name=package_name,
    version='0.1.0',
    packages=find_packages(exclude=['test']),
    data_files=[
        ('share/ament_index/resource_index/packages', ['resource/' + package_name]),
        ('share/' + package_name, ['package.xml']),
        ('share/' + package_name + '/launch', ['launch/monitor.launch.py']),
        ('share/' + package_name + '/config', ['config/params.yaml']),
    ],
    install_requires=['setuptools'],
    zip_safe=True,
    entry_points={
        'console_scripts': [
            'monitor_node = my_robot_monitor.monitor_node:main',
        ],
    },
)
```

### Mixed C++/Python package (ament_cmake_python)

Use `ament_cmake` as the build type but add Python module installation:

```cmake
find_package(ament_cmake_python REQUIRED)
ament_python_install_package(${PROJECT_NAME})
```

This is the correct approach when you need both a C++ library and Python bindings
or utilities in the same package.

## 5. package.xml format 3

```xml
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd"
  schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>my_robot_driver</name>
  <version>0.1.0</version>
  <description>Hardware driver for My Robot</description>
  <maintainer email="you@example.com">Your Name</maintainer>
  <license>Apache-2.0</license>

  <buildtool_depend>ament_cmake</buildtool_depend>

  <!-- Prefer <depend> when used at both build and runtime -->
  <depend>rclcpp</depend>
  <depend>rclcpp_lifecycle</depend>
  <depend>sensor_msgs</depend>
  <depend>my_robot_interfaces</depend>

  <!-- Needed at build and runtime (component container loads the shared lib) -->
  <depend>rclcpp_components</depend>

  <!-- Test deps -->
  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>
  <test_depend>ament_cmake_gtest</test_depend>

  <export>
    <build_type>ament_cmake</build_type>
  </export>
</package>
```

**`<depend>` vs `<build_depend>` vs `<exec_depend>`:**
- `<depend>` = build + exec (most common, use by default)
- `<build_depend>` = headers/libraries needed only at compile time
- `<exec_depend>` = needed at runtime only (e.g. launch file deps)
- `<test_depend>` = needed only for testing

## 6. Overlay mechanics

ROS 2 workspaces form a chain of overlays:

```
/opt/ros/jazzy/          ← underlay (system install)
  └── ~/ros2_ws/install/  ← overlay (your workspace)
       └── ~/dev_ws/install/ ← overlay (experimental)
```

**Rules:**
- Source underlays before building the overlay
- A package in the overlay shadows the same package in the underlay
- `colcon build --symlink-install` creates symlinks to source files,
  so Python edits take effect without rebuilding
- C++ changes always require a rebuild

**Multiple workspace pattern for large teams:**

```bash
# Team-shared stable workspace
source /opt/ros/jazzy/setup.bash
cd ~/team_ws && colcon build
source ~/team_ws/install/setup.bash

# Personal development workspace (overlays team_ws)
cd ~/dev_ws && colcon build
source ~/dev_ws/install/setup.bash
```

## 7. Build optimization

### ccache (10x faster rebuilds)

```bash
sudo apt install ccache
# Add to ~/.bashrc
export CC="ccache gcc"
export CXX="ccache g++"

# Or use colcon mixin
colcon build --mixin ccache
```

### Parallel linking (saves memory on ARM boards)

```bash
# Limit parallel link jobs (linking is memory-heavy)
# Use --parallel-workers to reduce package-level parallelism
colcon build --parallel-workers 2
# Or set MAKEFLAGS to limit make-level parallelism
MAKEFLAGS="-j2" colcon build
```

### Selective builds in CI

```bash
# Only build packages that contain changed files (and their dependents)
CHANGED_DIRS=$(git diff --name-only HEAD~1 | xargs -I{} dirname {} | sort -u)
CHANGED_PKGS=$(colcon list -n --base-paths $CHANGED_DIRS 2>/dev/null | tr '\n' ' ')
if [ -n "$CHANGED_PKGS" ]; then
  colcon build --packages-above $CHANGED_PKGS
fi
```

## 8. Dependency management

### rosdep

```bash
# Install all dependencies for workspace
cd ~/ros2_ws
rosdep install --from-paths src --ignore-src -y

# Check what would be installed
rosdep install --from-paths src --ignore-src --simulate
```

### Custom rosdep keys

Create `rosdep.yaml` for packages not in the official database:

```yaml
my_custom_lib:
  ubuntu:
    pip:
      packages: [my-custom-lib]
```

Register it:
```bash
echo "yaml file://$(pwd)/rosdep.yaml" | sudo tee /etc/ros/rosdep/sources.list.d/50-custom.list
rosdep update
```

### vcstool for multi-repo workspaces

```yaml
# repos.yaml
repositories:
  my_robot_driver:
    type: git
    url: https://github.com/org/my_robot_driver.git
    version: jazzy
  my_robot_interfaces:
    type: git
    url: https://github.com/org/my_robot_interfaces.git
    version: jazzy
```

```bash
vcs import src < repos.yaml   # clones into src/my_robot_driver, src/my_robot_interfaces
vcs pull src
```

## 9. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| `Could not find package X` in CMake | Missing `find_package()` or `package.xml` dep | Add both `find_package(X REQUIRED)` and `<depend>X</depend>` |
| Header not found despite package installed | Missing `target_include_directories` or `ament_target_dependencies` | Use `ament_target_dependencies` which handles include paths automatically |
| `setup.py` changes not reflected | Built without `--symlink-install` | Rebuild with `colcon build --symlink-install` |
| "Package not found" after build | Forgot to source `install/setup.bash` | Source after every build, or use `direnv` |
| Circular dependency error | Package A depends on B and B depends on A | Extract shared interfaces into a third package |
| "Multiple packages with name X" | Duplicate package in overlay and underlay | Remove the underlay version or use `--packages-select` |
| Link error: undefined reference | Library not listed in `target_link_libraries` | Add library to CMake target linking |
