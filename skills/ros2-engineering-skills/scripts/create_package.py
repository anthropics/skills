#!/usr/bin/env python3
"""Scaffold a ROS 2 package following ros2-engineering-skills conventions.

Usage:
    python create_package.py my_robot_driver --type cpp
    python create_package.py my_robot_monitor --type python
    python create_package.py my_robot_interfaces --type interfaces
    python create_package.py my_robot_driver --type cpp --component
    python create_package.py my_arm_hw --type hardware_interface
    python create_package.py my_robot --type cpp --robots 3
    python create_package.py my_robot --type cpp --sros2
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Optional


def _write(path: Path, text: str) -> None:
    """Write text to a file with explicit UTF-8 encoding (Windows safe)."""
    path.write_text(text, encoding='utf-8')


__version__ = "0.1.0"

# Apache-2.0 copyright/license headers for generated files
_APACHE2_PY = """# Copyright 2024 {maintainer}
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""

_APACHE2_CPP = """// Copyright 2024 {maintainer}
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
"""


def _copyright_py(maintainer: str = "TODO") -> str:
    return _APACHE2_PY.format(maintainer=maintainer)


def _copyright_cpp(maintainer: str = "TODO") -> str:
    return _APACHE2_CPP.format(maintainer=maintainer)


def _generate_launch_file(name: str, lifecycle: bool = False,
                          maintainer_name: str = "TODO") -> str:
    """Generate a basic bringup.launch.py file for the package."""
    header = _copyright_py(maintainer_name)
    if lifecycle:
        return header + f"""
from launch import LaunchDescription
from launch.actions import EmitEvent, RegisterEventHandler
from launch.substitutions import PathJoinSubstitution
from launch_ros.actions import LifecycleNode
from launch_ros.event_handlers import OnStateTransition
from launch_ros.events.lifecycle import ChangeState
from launch_ros.substitutions import FindPackageShare
import lifecycle_msgs.msg


def generate_launch_description():
    config = PathJoinSubstitution([
        FindPackageShare('{name}'), 'config', 'params.yaml'
    ])
    node = LifecycleNode(
        package='{name}',
        executable='{name}_node',
        name='{name}',
        namespace='',
        parameters=[config],
        output='screen',
    )
    # Auto-configure on launch
    configure_event = EmitEvent(
        event=ChangeState(
            lifecycle_node_matcher=lambda info: info,
            transition_id=lifecycle_msgs.msg.Transition.TRANSITION_CONFIGURE,
        )
    )
    # Auto-activate after configure succeeds
    activate_event = RegisterEventHandler(
        OnStateTransition(
            target_lifecycle_node=node,
            start_state='configuring',
            goal_state='inactive',
            entities=[
                EmitEvent(event=ChangeState(
                    lifecycle_node_matcher=lambda info: info,
                    transition_id=lifecycle_msgs.msg.Transition.TRANSITION_ACTIVATE,
                )),
            ],
        )
    )
    return LaunchDescription([node, configure_event, activate_event])
"""
    else:
        return header + f"""
from launch import LaunchDescription
from launch.substitutions import PathJoinSubstitution
from launch_ros.actions import Node
from launch_ros.substitutions import FindPackageShare


def generate_launch_description():
    config = PathJoinSubstitution([
        FindPackageShare('{name}'), 'config', 'params.yaml'
    ])
    return LaunchDescription([
        Node(
            package='{name}',
            executable='{name}_node',
            name='{name}',
            parameters=[config],
            output='screen',
        ),
    ])
"""


def _generate_readme(name: str) -> str:
    """Generate a basic README.md for the package."""
    return f"""# {name}

TODO: Package description

## Usage

```bash
ros2 launch {name} bringup.launch.py
```

## Parameters

See `config/params.yaml` for default parameters.
"""


def create_cpp_package(name: str, dest: Path, component: bool = False,
                       maintainer_name: str = "TODO",
                       maintainer_email: str = "todo@todo.com") -> None:
    pkg = dest / name
    dirs = [
        pkg / "include" / name,
        pkg / "src",
        pkg / "launch",
        pkg / "config",
        pkg / "test",
    ]
    for d in dirs:
        d.mkdir(parents=True, exist_ok=True)

    cpp_header = _copyright_cpp(maintainer_name)

    component_cmake = ""
    if component:
        component_cmake = f"""
find_package(rclcpp_components REQUIRED)
rclcpp_components_register_node(${{PROJECT_NAME}}_lib
  PLUGIN "{name}::{_class_name(name)}Node"
  EXECUTABLE ${{PROJECT_NAME}}_component_node
)
"""

    _write(pkg / "CMakeLists.txt", f"""cmake_minimum_required(VERSION 3.8)
project({name})

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_lifecycle REQUIRED)

add_library(${{PROJECT_NAME}}_lib SHARED
  src/{name}_node.cpp
)
target_include_directories(${{PROJECT_NAME}}_lib PUBLIC
  $<BUILD_INTERFACE:${{CMAKE_CURRENT_SOURCE_DIR}}/include>
  $<INSTALL_INTERFACE:include/${{PROJECT_NAME}}>
)
target_link_libraries(${{PROJECT_NAME}}_lib PUBLIC
  rclcpp::rclcpp
  rclcpp_lifecycle::rclcpp_lifecycle
)
# Legacy fallback (deprecated since Kilted; prefer target_link_libraries):
# ament_target_dependencies(${{PROJECT_NAME}}_lib rclcpp rclcpp_lifecycle)
{component_cmake}
add_executable({name}_node src/main.cpp)
target_link_libraries({name}_node ${{PROJECT_NAME}}_lib)

install(TARGETS ${{PROJECT_NAME}}_lib
  EXPORT export_${{PROJECT_NAME}}
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
)
install(TARGETS {name}_node DESTINATION lib/${{PROJECT_NAME}})
install(DIRECTORY include/ DESTINATION include/${{PROJECT_NAME}})
install(DIRECTORY launch config DESTINATION share/${{PROJECT_NAME}})

if(BUILD_TESTING)
  find_package(ament_lint_auto REQUIRED)
  ament_lint_auto_find_test_dependencies()
  find_package(ament_cmake_gtest REQUIRED)
  ament_add_gtest(test_{name} test/test_{name}.cpp)
  target_link_libraries(test_{name} ${{PROJECT_NAME}}_lib)
endif()

ament_export_targets(export_${{PROJECT_NAME}} HAS_LIBRARY_TARGET)
ament_export_dependencies(rclcpp rclcpp_lifecycle)
ament_package()
""")

    class_name = _class_name(name)

    _write(pkg / "include" / name / f"{name}_node.hpp", cpp_header + f"""
#pragma once

#include <rclcpp/rclcpp.hpp>
#include <rclcpp_lifecycle/lifecycle_node.hpp>

namespace {name}
{{

class {class_name}Node : public rclcpp_lifecycle::LifecycleNode
{{
public:
  explicit {class_name}Node(const rclcpp::NodeOptions & options = rclcpp::NodeOptions());

  CallbackReturn on_configure(const rclcpp_lifecycle::State &) override;
  CallbackReturn on_activate(const rclcpp_lifecycle::State &) override;
  CallbackReturn on_deactivate(const rclcpp_lifecycle::State &) override;
  CallbackReturn on_cleanup(const rclcpp_lifecycle::State &) override;

private:
  /// QoS event: called when a subscriber with incompatible QoS connects
  void on_offered_qos_incompatible(rclcpp::QOSOfferedIncompatibleQoSInfo & event);
  /// QoS event: called when a publisher with incompatible QoS is discovered
  void on_requested_qos_incompatible(rclcpp::QOSRequestedIncompatibleQoSInfo & event);
}};

}}  // namespace {name}
""")

    component_include = ""
    component_register = ""
    if component:
        component_include = "\n#include <rclcpp_components/register_node_macro.hpp>"
        component_register = f"\n\nRCLCPP_COMPONENTS_REGISTER_NODE({name}::{class_name}Node)\n"

    _write(pkg / "src" / f"{name}_node.cpp", cpp_header + f"""
#include "{name}/{name}_node.hpp"
{component_include}
namespace {name}
{{

{class_name}Node::{class_name}Node(const rclcpp::NodeOptions & options)
: LifecycleNode("{name}", options)
{{
  RCLCPP_INFO(get_logger(), "Node created");
}}

{class_name}Node::CallbackReturn
{class_name}Node::on_configure(const rclcpp_lifecycle::State &)
{{
  RCLCPP_INFO(get_logger(), "Configuring...");
  return CallbackReturn::SUCCESS;
}}

{class_name}Node::CallbackReturn
{class_name}Node::on_activate(const rclcpp_lifecycle::State &)
{{
  RCLCPP_INFO(get_logger(), "Activating...");
  return CallbackReturn::SUCCESS;
}}

{class_name}Node::CallbackReturn
{class_name}Node::on_deactivate(const rclcpp_lifecycle::State &)
{{
  RCLCPP_INFO(get_logger(), "Deactivating...");
  return CallbackReturn::SUCCESS;
}}

{class_name}Node::CallbackReturn
{class_name}Node::on_cleanup(const rclcpp_lifecycle::State &)
{{
  RCLCPP_INFO(get_logger(), "Cleaning up...");
  return CallbackReturn::SUCCESS;
}}

void {class_name}Node::on_offered_qos_incompatible(
  rclcpp::QOSOfferedIncompatibleQoSInfo & event)
{{
  RCLCPP_WARN(
    get_logger(),
    "Offered incompatible QoS: policy_kind=%d, total_count=%d",
    event.last_policy_kind, event.total_count);
}}

void {class_name}Node::on_requested_qos_incompatible(
  rclcpp::QOSRequestedIncompatibleQoSInfo & event)
{{
  RCLCPP_WARN(
    get_logger(),
    "Requested incompatible QoS: policy_kind=%d, total_count=%d",
    event.last_policy_kind, event.total_count);
}}

}}  // namespace {name}
{component_register}""")

    _write(pkg / "src" / "main.cpp", cpp_header + f"""
#include <rclcpp/rclcpp.hpp>
#include "{name}/{name}_node.hpp"

int main(int argc, char ** argv)
{{
  rclcpp::init(argc, argv);
  auto node = std::make_shared<{name}::{class_name}Node>();
  rclcpp::executors::SingleThreadedExecutor exe;
  exe.add_node(node->get_node_base_interface());
  exe.spin();
  rclcpp::shutdown();
  return 0;
}}
""")

    _write(pkg / "config" / "params.yaml", f"""{name}:
  ros__parameters:
    # Add parameters here
    publish_rate: 50.0
""")

    _write(pkg / "test" / f"test_{name}.cpp", cpp_header + f"""
#include <gtest/gtest.h>
#include <rclcpp/rclcpp.hpp>
#include "{name}/{name}_node.hpp"

class {class_name}Test : public ::testing::Test
{{
protected:
  static void SetUpTestSuite()
  {{
    rclcpp::init(0, nullptr);
  }}
  static void TearDownTestSuite()
  {{
    rclcpp::shutdown();
  }}
}};

TEST_F({class_name}Test, NodeCreation)
{{
  auto node = std::make_shared<{name}::{class_name}Node>();
  ASSERT_NE(node, nullptr);
}}
""")

    # Generate launch file (lifecycle=True since C++ template uses LifecycleNode)
    launch_content = _generate_launch_file(
        name, lifecycle=True, maintainer_name=maintainer_name)
    _write(pkg / "launch" / "bringup.launch.py", launch_content)

    # Generate README
    _write(pkg / "README.md", _generate_readme(name))

    deps = ["rclcpp", "rclcpp_lifecycle"]
    if component:
        deps.append("rclcpp_components")
    _write_package_xml(pkg, name, "ament_cmake", deps,
                       maintainer_name=maintainer_name,
                       maintainer_email=maintainer_email)
    print(f"Created C++ package: {pkg}")


def _generate_python_lifecycle_node(name: str, class_name: str,
                                    maintainer_name: str = "TODO") -> str:
    """Generate a Python LifecycleNode with proper callback hooks."""
    py_header = _copyright_py(maintainer_name)
    return py_header + f"""
import rclpy
from rclpy.lifecycle import LifecycleNode, LifecycleState, TransitionCallbackReturn


class {class_name}Node(LifecycleNode):

    def __init__(self, **kwargs):
        super().__init__('{name}', **kwargs)
        self.get_logger().info('Node created (inactive)')

    def on_configure(self, state: LifecycleState) -> TransitionCallbackReturn:
        self.declare_parameter('publish_rate', 50.0)
        rate = self.get_parameter('publish_rate').value
        self.get_logger().info(f'Configuring with rate={{rate}} Hz')
        self._timer_period = 1.0 / rate
        return TransitionCallbackReturn.SUCCESS

    def on_activate(self, state: LifecycleState) -> TransitionCallbackReturn:
        self.timer = self.create_timer(self._timer_period, self.timer_callback)
        self.get_logger().info('Activated')
        return TransitionCallbackReturn.SUCCESS

    def on_deactivate(self, state: LifecycleState) -> TransitionCallbackReturn:
        self.destroy_timer(self.timer)
        self.get_logger().info('Deactivated')
        return TransitionCallbackReturn.SUCCESS

    def on_cleanup(self, state: LifecycleState) -> TransitionCallbackReturn:
        self.get_logger().info('Cleaning up')
        return TransitionCallbackReturn.SUCCESS

    def on_shutdown(self, state: LifecycleState) -> TransitionCallbackReturn:
        self.get_logger().info('Shutting down')
        return TransitionCallbackReturn.SUCCESS

    def timer_callback(self):
        pass  # Implement your logic here


def main(args=None):
    rclpy.init(args=args)
    node = {class_name}Node()
    try:
        rclpy.spin(node)
    except KeyboardInterrupt:
        pass
    finally:
        node.destroy_node()
        rclpy.shutdown()


if __name__ == '__main__':
    main()
"""


def create_python_package(name: str, dest: Path,
                          maintainer_name: str = "TODO",
                          maintainer_email: str = "todo@todo.com",
                          lifecycle: bool = False) -> None:
    pkg = dest / name
    dirs = [
        pkg / name,
        pkg / "launch",
        pkg / "config",
        pkg / "test",
        pkg / "resource",
    ]
    for d in dirs:
        d.mkdir(parents=True, exist_ok=True)

    py_header = _copyright_py(maintainer_name)

    _write(pkg / name / "__init__.py", py_header)
    _write(pkg / "resource" / name, "")

    class_name = _class_name(name)

    if lifecycle:
        lifecycle_src = _generate_python_lifecycle_node(
            name, class_name, maintainer_name)
        _write(pkg / name / f"{name}_node.py", lifecycle_src)
    else:
        _write(pkg / name / f"{name}_node.py", py_header + f"""
import rclpy
from rclpy.node import Node


class {class_name}Node(Node):

    def __init__(self, **kwargs):
        super().__init__('{name}', **kwargs)
        self.declare_parameter('publish_rate', 50.0)
        rate = self.get_parameter('publish_rate').value
        self.timer = self.create_timer(1.0 / rate, self.timer_callback)
        self.get_logger().info('Node started')

    def timer_callback(self):
        pass  # Implement your logic here

    # QoS event callbacks — attach to publishers/subscribers via
    # event_callbacks=QoSEventHandler(incompatible_qos_callback=self.on_qos_event)
    def on_qos_event(self, event):
        self.get_logger().warn(
            f'QoS incompatibility detected: {{event.last_policy_kind}}')


def main(args=None):
    rclpy.init(args=args)
    node = {class_name}Node()
    try:
        rclpy.spin(node)
    except KeyboardInterrupt:
        pass
    finally:
        node.destroy_node()
        rclpy.shutdown()


if __name__ == '__main__':
    main()
""")

    _write(pkg / "setup.py", py_header + f"""
from setuptools import find_packages, setup

package_name = '{name}'

setup(
    name=package_name,
    version='0.1.0',
    packages=find_packages(exclude=['test']),
    data_files=[
        ('share/ament_index/resource_index/packages', ['resource/' + package_name]),
        ('share/' + package_name, ['package.xml']),
        ('share/' + package_name + '/launch', ['launch/bringup.launch.py']),
        ('share/' + package_name + '/config', ['config/params.yaml']),
    ],
    install_requires=['setuptools'],
    zip_safe=True,
    entry_points={{
        'console_scripts': [
            '{name}_node = {name}.{name}_node:main',
        ],
    }},
)
""")

    _write(pkg / "setup.cfg", f"""[develop]
script_dir=$base/lib/{name}
[install]
install_scripts=$base/lib/{name}
""")

    _write(pkg / "config" / "params.yaml", f"""{name}:
  ros__parameters:
    publish_rate: 50.0
""")

    if lifecycle:
        _write(pkg / "test" / f"test_{name}.py", py_header + f"""
import pytest
import rclpy
from {name}.{name}_node import {class_name}Node


@pytest.fixture(scope='module', autouse=True)
def init_rclpy():
    rclpy.init()
    yield
    rclpy.shutdown()


def test_node_creation():
    node = {class_name}Node()
    assert node.get_name() == '{name}'
    node.destroy_node()


def test_lifecycle_configure():
    from rclpy.lifecycle import TransitionCallbackReturn
    node = {class_name}Node()
    ret = node.trigger_configure()
    assert ret == TransitionCallbackReturn.SUCCESS
    node.destroy_node()


def test_lifecycle_activate():
    from rclpy.lifecycle import TransitionCallbackReturn
    node = {class_name}Node()
    node.trigger_configure()
    ret = node.trigger_activate()
    assert ret == TransitionCallbackReturn.SUCCESS
    node.destroy_node()
""")
    else:
        _write(pkg / "test" / f"test_{name}.py", py_header + f"""
import pytest
import rclpy
from {name}.{name}_node import {class_name}Node


@pytest.fixture(scope='module', autouse=True)
def init_rclpy():
    rclpy.init()
    yield
    rclpy.shutdown()


def test_node_creation():
    node = {class_name}Node()
    assert node.get_name() == '{name}'
    node.destroy_node()
""")

    # Standard ament lint test files for Python packages
    _write(pkg / "test" / "test_copyright.py", py_header + """
from ament_copyright.main import main
import pytest


@pytest.mark.copyright
@pytest.mark.linter
def test_copyright():
    rc = main(argv=['.', 'test'])
    assert rc == 0, 'Found errors'
""")

    _write(pkg / "test" / "test_flake8.py", py_header + """
from ament_flake8.main import main_with_errors
import pytest


@pytest.mark.flake8
@pytest.mark.linter
def test_flake8():
    rc, errors = main_with_errors(argv=[])
    assert rc == 0, \\
        'Found %d code style errors / warnings:\\n' % len(errors) + \\
        '\\n'.join(errors)
""")

    _write(pkg / "test" / "test_pep257.py", py_header + """
from ament_pep257.main import main
import pytest


@pytest.mark.pep257
@pytest.mark.linter
def test_pep257():
    rc = main(argv=['.', 'test'])
    assert rc == 0, 'Found errors'
""")

    # Generate launch file (lifecycle=True if Python lifecycle package)
    launch_content = _generate_launch_file(
        name, lifecycle=lifecycle, maintainer_name=maintainer_name)
    _write(pkg / "launch" / "bringup.launch.py", launch_content)

    # Generate README
    _write(pkg / "README.md", _generate_readme(name))

    py_deps = ["rclpy"]
    if lifecycle:
        py_deps.append("lifecycle_msgs")
    _write_package_xml(pkg, name, "ament_python", py_deps,
                       maintainer_name=maintainer_name,
                       maintainer_email=maintainer_email,
                       extra_test=["ament_copyright", "ament_flake8",
                                   "ament_pep257", "python3-pytest"])
    print(f"Created Python package: {pkg}")


def create_interfaces_package(name: str, dest: Path,
                              maintainer_name: str = "TODO",
                              maintainer_email: str = "todo@todo.com") -> None:
    pkg = dest / name
    dirs = [pkg / "msg", pkg / "srv", pkg / "action"]
    for d in dirs:
        d.mkdir(parents=True, exist_ok=True)

    _write(pkg / "msg" / "Status.msg", """std_msgs/Header header
uint8 mode
string description
float64 battery_voltage
""")

    _write(pkg / "srv" / "SetMode.srv", """string mode
bool force
---
bool success
string message
""")

    _write(pkg / "CMakeLists.txt", f"""cmake_minimum_required(VERSION 3.8)
project({name})

find_package(ament_cmake REQUIRED)
find_package(rosidl_default_generators REQUIRED)
find_package(std_msgs REQUIRED)

rosidl_generate_interfaces(${{PROJECT_NAME}}
  "msg/Status.msg"
  "srv/SetMode.srv"
  DEPENDENCIES std_msgs
)

if(BUILD_TESTING)
  find_package(ament_lint_auto REQUIRED)
  ament_lint_auto_find_test_dependencies()
endif()

ament_export_dependencies(rosidl_default_runtime)
ament_package()
""")

    # Generate README
    _write(pkg / "README.md", _generate_readme(name))

    _write_package_xml(pkg, name, "ament_cmake",
                       ["std_msgs"],
                       maintainer_name=maintainer_name,
                       maintainer_email=maintainer_email,
                       extra_buildtool=["rosidl_default_generators"],
                       extra_exec=["rosidl_default_runtime"],
                       extra_member=["rosidl_interface_packages"])
    print(f"Created interfaces package: {pkg}")


def create_hardware_interface_package(
    name: str, dest: Path,
    maintainer_name: str = "TODO",
    maintainer_email: str = "todo@todo.com",
) -> None:
    """Generate a ros2_control hardware_interface package (C++)."""
    pkg = dest / name
    dirs = [
        pkg / "include" / name,
        pkg / "src",
        pkg / "config",
        pkg / "test",
    ]
    for d in dirs:
        d.mkdir(parents=True, exist_ok=True)

    cpp_header = _copyright_cpp(maintainer_name)
    class_name = _class_name(name)

    # --- CMakeLists.txt ---
    _write(pkg / "CMakeLists.txt", f"""cmake_minimum_required(VERSION 3.8)
project({name})

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

find_package(ament_cmake REQUIRED)
find_package(hardware_interface REQUIRED)
find_package(pluginlib REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_lifecycle REQUIRED)

# Detect ros2_control API (rolling 6.x changed on_init signature)
if(hardware_interface_VERSION VERSION_GREATER_EQUAL "6.0.0")
  add_definitions(-DHARDWARE_INTERFACE_HAS_PARAMS_API)
endif()

add_library(${{PROJECT_NAME}} SHARED
  src/{name}_hardware.cpp
)
target_include_directories(${{PROJECT_NAME}} PUBLIC
  $<BUILD_INTERFACE:${{CMAKE_CURRENT_SOURCE_DIR}}/include>
  $<INSTALL_INTERFACE:include/${{PROJECT_NAME}}>
)
target_link_libraries(${{PROJECT_NAME}} PUBLIC
  hardware_interface::hardware_interface
  pluginlib::pluginlib
  rclcpp::rclcpp
  rclcpp_lifecycle::rclcpp_lifecycle
)

pluginlib_export_plugin_description_file(hardware_interface {name}_plugin.xml)

install(TARGETS ${{PROJECT_NAME}}
  EXPORT export_${{PROJECT_NAME}}
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
)
install(DIRECTORY include/ DESTINATION include/${{PROJECT_NAME}})
install(DIRECTORY config DESTINATION share/${{PROJECT_NAME}})

if(BUILD_TESTING)
  find_package(ament_lint_auto REQUIRED)
  ament_lint_auto_find_test_dependencies()
  find_package(ament_cmake_gtest REQUIRED)
  ament_add_gtest(test_{name} test/test_{name}.cpp)
  target_link_libraries(test_{name} ${{PROJECT_NAME}})
endif()

ament_export_targets(export_${{PROJECT_NAME}} HAS_LIBRARY_TARGET)
ament_export_dependencies(hardware_interface pluginlib rclcpp rclcpp_lifecycle)
ament_package()
""")

    # --- Header ---
    _write(pkg / "include" / name / f"{name}_hardware.hpp", cpp_header + f"""
#pragma once

#include <string>
#include <vector>

#include <hardware_interface/system_interface.hpp>
#include <hardware_interface/handle.hpp>
#include <hardware_interface/hardware_info.hpp>
#include <hardware_interface/types/hardware_interface_return_values.hpp>
#include <rclcpp/macros.hpp>
#include <rclcpp_lifecycle/state.hpp>

namespace {name}
{{

// Type alias for cross-distro compatibility (rolling 6.x API change)
#ifdef HARDWARE_INTERFACE_HAS_PARAMS_API
using OnInitArgType = hardware_interface::HardwareComponentInterfaceParams;
#else
using OnInitArgType = hardware_interface::HardwareInfo;
#endif

class {class_name}Hardware : public hardware_interface::SystemInterface
{{
public:
  RCLCPP_SHARED_PTR_DEFINITIONS({class_name}Hardware)

  hardware_interface::CallbackReturn on_init(
    const OnInitArgType & init_param) override;

  hardware_interface::CallbackReturn on_configure(
    const rclcpp_lifecycle::State & previous_state) override;

  hardware_interface::CallbackReturn on_activate(
    const rclcpp_lifecycle::State & previous_state) override;

  hardware_interface::CallbackReturn on_deactivate(
    const rclcpp_lifecycle::State & previous_state) override;

  hardware_interface::CallbackReturn on_cleanup(
    const rclcpp_lifecycle::State & previous_state) override;

  std::vector<hardware_interface::StateInterface> export_state_interfaces() override;
  std::vector<hardware_interface::CommandInterface> export_command_interfaces() override;

  hardware_interface::return_type read(
    const rclcpp::Time & time, const rclcpp::Duration & period) override;

  hardware_interface::return_type write(
    const rclcpp::Time & time, const rclcpp::Duration & period) override;

private:
  // Joint state storage
  std::vector<double> hw_positions_;
  std::vector<double> hw_velocities_;
  std::vector<double> hw_commands_;
}};

}}  // namespace {name}
""")

    # --- Source ---
    _write(pkg / "src" / f"{name}_hardware.cpp", cpp_header + f"""
#include "{name}/{name}_hardware.hpp"

#include <hardware_interface/types/hardware_interface_type_values.hpp>
#include <pluginlib/class_list_macros.hpp>
#include <rclcpp/rclcpp.hpp>

namespace {name}
{{

hardware_interface::CallbackReturn {class_name}Hardware::on_init(
  const OnInitArgType & init_param)
{{
  if (hardware_interface::SystemInterface::on_init(init_param) !=
    hardware_interface::CallbackReturn::SUCCESS)
  {{
    return hardware_interface::CallbackReturn::ERROR;
  }}

  hw_positions_.resize(info_.joints.size(), 0.0);
  hw_velocities_.resize(info_.joints.size(), 0.0);
  hw_commands_.resize(info_.joints.size(), 0.0);

  RCLCPP_INFO(
    rclcpp::get_logger("{name}"), "Initialized with %zu joints",
    info_.joints.size());
  return hardware_interface::CallbackReturn::SUCCESS;
}}

hardware_interface::CallbackReturn {class_name}Hardware::on_configure(
  const rclcpp_lifecycle::State & /*previous_state*/)
{{
  RCLCPP_INFO(rclcpp::get_logger("{name}"), "Configuring...");
  // Reset command and state values
  std::fill(hw_positions_.begin(), hw_positions_.end(), 0.0);
  std::fill(hw_velocities_.begin(), hw_velocities_.end(), 0.0);
  std::fill(hw_commands_.begin(), hw_commands_.end(), 0.0);
  return hardware_interface::CallbackReturn::SUCCESS;
}}

hardware_interface::CallbackReturn {class_name}Hardware::on_activate(
  const rclcpp_lifecycle::State & /*previous_state*/)
{{
  RCLCPP_INFO(rclcpp::get_logger("{name}"), "Activating...");
  return hardware_interface::CallbackReturn::SUCCESS;
}}

hardware_interface::CallbackReturn {class_name}Hardware::on_deactivate(
  const rclcpp_lifecycle::State & /*previous_state*/)
{{
  RCLCPP_INFO(rclcpp::get_logger("{name}"), "Deactivating...");
  // SAFETY: Zero all commands to prevent the robot from holding
  // the last commanded velocity/position on shutdown.
  std::fill(hw_commands_.begin(), hw_commands_.end(), 0.0);
  return hardware_interface::CallbackReturn::SUCCESS;
}}

hardware_interface::CallbackReturn {class_name}Hardware::on_cleanup(
  const rclcpp_lifecycle::State & /*previous_state*/)
{{
  RCLCPP_INFO(rclcpp::get_logger("{name}"), "Cleaning up...");
  return hardware_interface::CallbackReturn::SUCCESS;
}}

std::vector<hardware_interface::StateInterface>
{class_name}Hardware::export_state_interfaces()
{{
  std::vector<hardware_interface::StateInterface> state_interfaces;
  for (size_t i = 0; i < info_.joints.size(); i++) {{
    state_interfaces.emplace_back(
      info_.joints[i].name, hardware_interface::HW_IF_POSITION, &hw_positions_[i]);
    state_interfaces.emplace_back(
      info_.joints[i].name, hardware_interface::HW_IF_VELOCITY, &hw_velocities_[i]);
  }}
  return state_interfaces;
}}

std::vector<hardware_interface::CommandInterface>
{class_name}Hardware::export_command_interfaces()
{{
  std::vector<hardware_interface::CommandInterface> command_interfaces;
  for (size_t i = 0; i < info_.joints.size(); i++) {{
    command_interfaces.emplace_back(
      info_.joints[i].name, hardware_interface::HW_IF_POSITION, &hw_commands_[i]);
  }}
  return command_interfaces;
}}

hardware_interface::return_type {class_name}Hardware::read(
  const rclcpp::Time & /*time*/, const rclcpp::Duration & /*period*/)
{{
  // TODO(user): Read actual hardware state here
  // For simulation, mirror commands to positions:
  for (size_t i = 0; i < hw_positions_.size(); i++) {{
    hw_positions_[i] = hw_commands_[i];
  }}
  return hardware_interface::return_type::OK;
}}

hardware_interface::return_type {class_name}Hardware::write(
  const rclcpp::Time & /*time*/, const rclcpp::Duration & /*period*/)
{{
  // TODO(user): Write commands to actual hardware here
  return hardware_interface::return_type::OK;
}}

}}  // namespace {name}

PLUGINLIB_EXPORT_CLASS(
  {name}::{class_name}Hardware,
  hardware_interface::SystemInterface)
""")

    # --- Plugin description XML ---
    _write(pkg / f"{name}_plugin.xml", f"""<library path="{name}">
  <class name="{name}/{class_name}Hardware"
         type="{name}::{class_name}Hardware"
         base_class_type="hardware_interface::SystemInterface">
    <description>
      Hardware interface for {name}
    </description>
  </class>
</library>
""")

    # --- ros2_control URDF snippet ---
    _write(pkg / "config" / f"{name}.ros2_control.xacro", f"""<?xml version="1.0"?>
<robot xmlns:xacro="http://www.ros.org/wiki/xacro">
  <ros2_control name="{class_name}System" type="system">
    <hardware>
      <plugin>{name}/{class_name}Hardware</plugin>
    </hardware>
    <!-- Example joint: uncomment and adapt for your robot -->
    <!--
    <joint name="joint_1">
      <command_interface name="position"/>
      <state_interface name="position">
        <param name="initial_value">0.0</param>
      </state_interface>
      <state_interface name="velocity"/>
    </joint>
    -->
  </ros2_control>
</robot>
""")

    # --- Controller config ---
    _write(pkg / "config" / "controllers.yaml", """controller_manager:
  ros__parameters:
    update_rate: 100  # Hz

    joint_state_broadcaster:
      type: joint_state_broadcaster/JointStateBroadcaster

    # Example controller: uncomment and adapt
    # joint_trajectory_controller:
    #   type: joint_trajectory_controller/JointTrajectoryController

# joint_trajectory_controller:
#   ros__parameters:
#     joints:
#       - joint_1
#     command_interfaces:
#       - position
#     state_interfaces:
#       - position
#       - velocity
""")

    # --- Test ---
    _write(pkg / "test" / f"test_{name}.cpp", cpp_header + f"""
#include <gtest/gtest.h>
#include "{name}/{name}_hardware.hpp"

TEST({class_name}Test, InterfaceCreation)
{{
  // Verify the hardware interface class can be instantiated
  auto hw = std::make_shared<{name}::{class_name}Hardware>();
  ASSERT_NE(hw, nullptr);
}}

TEST({class_name}Test, OnInitWithEmptyInfo)
{{
  auto hw = std::make_shared<{name}::{class_name}Hardware>();
  {name}::OnInitArgType init_param;
  auto ret = hw->on_init(init_param);
  ASSERT_EQ(ret, hardware_interface::CallbackReturn::SUCCESS);
}}
""")

    # --- README ---
    _write(pkg / "README.md", f"""# {name}

ros2_control hardware interface package.

## Usage

Include the xacro snippet in your robot URDF:
```xml
<xacro:include filename="$(find {name})/config/{name}.ros2_control.xacro"/>
```

Load controllers:
```bash
ros2 launch {name} bringup.launch.py  # if using a launch file
# or manually:
ros2 control load_controller joint_state_broadcaster --set-state active
```

## Configuration

- `config/controllers.yaml` — Controller manager configuration
- `config/{name}.ros2_control.xacro` — Hardware interface URDF snippet
""")

    _write_package_xml(
        pkg, name, "ament_cmake",
        ["hardware_interface", "pluginlib", "rclcpp", "rclcpp_lifecycle"],
        maintainer_name=maintainer_name,
        maintainer_email=maintainer_email)
    print(f"Created hardware_interface package: {pkg}")


def _generate_fleet_launch(name: str, num_robots: int,
                           lifecycle: bool = False,
                           maintainer_name: str = "TODO") -> str:
    """Generate a multi-robot fleet launch file with namespace isolation."""
    header = _copyright_py(maintainer_name)
    node_type = "LifecycleNode" if lifecycle else "Node"
    imports = "from launch_ros.actions import Node" if not lifecycle else \
        "from launch_ros.actions import LifecycleNode"

    robot_blocks = []
    for i in range(1, num_robots + 1):
        robot_blocks.append(f"""
        GroupAction(
            scoped=True,
            actions=[
                PushRosNamespace('robot_{i}'),
                {node_type}(
                    package='{name}',
                    executable='{name}_node',
                    name='{name}_robot_{i}',
                    parameters=[config],
                    output='screen',
                ),
            ],
        ),""")

    robots_str = "".join(robot_blocks)

    return header + f"""
from launch import LaunchDescription
from launch.actions import GroupAction
from launch.substitutions import PathJoinSubstitution
from launch_ros.actions import PushRosNamespace
{imports}
from launch_ros.substitutions import FindPackageShare


def generate_launch_description():
    config = PathJoinSubstitution([
        FindPackageShare('{name}'), 'config', 'params.yaml'
    ])
    return LaunchDescription([{robots_str}
    ])
"""


def _generate_sros2_enclave(name: str, dest: Path,
                            maintainer_name: str = "TODO") -> None:
    """Generate SROS2 security enclave directory and policy files."""
    enclave = dest / name / "security" / "enclaves" / name
    enclave.mkdir(parents=True, exist_ok=True)

    _write(dest / name / "security" / "policies.xml", f"""<?xml version="1.0" encoding="UTF-8"?>
<policy version="0.2.0">
  <enclaves>
    <enclave path="/{name}">
      <profiles>
        <profile ns="/" node="{name}">
          <topics publish="ALLOW" subscribe="ALLOW">
            <topic>/*</topic>
          </topics>
          <services reply="ALLOW" request="ALLOW">
            <service>/*</service>
          </services>
          <actions call="ALLOW" execute="ALLOW">
            <action>/*</action>
          </actions>
        </profile>
      </profiles>
    </enclave>
  </enclaves>
</policy>
""")

    _write(dest / name / "security" / "governance.xml", """<?xml version="1.0" encoding="UTF-8"?>
<dds xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
     xsi:noNamespaceSchemaLocation="omg_shared_ca_governance.xsd">
  <domain_access_rules>
    <domain_rule>
      <domains>
        <id_range>
          <min>0</min>
          <max>230</max>
        </id_range>
      </domains>
      <allow_unauthenticated_participants>false</allow_unauthenticated_participants>
      <enable_join_access_control>true</enable_join_access_control>
      <discovery_protection_kind>ENCRYPT</discovery_protection_kind>
      <liveliness_protection_kind>ENCRYPT</liveliness_protection_kind>
      <rtps_protection_kind>ENCRYPT</rtps_protection_kind>
      <topic_access_rules>
        <topic_rule>
          <topic_expression>*</topic_expression>
          <enable_discovery_protection>true</enable_discovery_protection>
          <enable_liveliness_protection>true</enable_liveliness_protection>
          <enable_read_access_control>true</enable_read_access_control>
          <enable_write_access_control>true</enable_write_access_control>
          <metadata_protection_kind>ENCRYPT</metadata_protection_kind>
          <data_protection_kind>ENCRYPT</data_protection_kind>
        </topic_rule>
      </topic_access_rules>
    </domain_rule>
  </domain_access_rules>
</dds>
""")

    _write(dest / name / "security" / "README.md", f"""# SROS2 Security Configuration for {name}

## Quick Start

```bash
# Create a keystore
ros2 security create_keystore ~/sros2_keystore

# Generate keys for this enclave
ros2 security create_enclave ~/sros2_keystore /{name}

# Generate permissions from policies
ros2 security create_permission ~/sros2_keystore /{name} \\
  security/policies.xml

# Run with security enabled
export ROS_SECURITY_KEYSTORE=~/sros2_keystore
export ROS_SECURITY_ENABLE=true
export ROS_SECURITY_STRATEGY=Enforce
ros2 launch {name} bringup.launch.py
```

## Files

- `policies.xml` — Node-level access control policies
- `governance.xml` — Domain-level security governance rules
- `enclaves/{name}/` — Generated keys and certificates (after `create_enclave`)
""")


def _class_name(name: str) -> str:
    """Convert a snake_case package name to CamelCase class name."""
    return "".join(w.capitalize() for w in name.split("_"))


def _write_package_xml(pkg: Path, name: str, build_type: str,
                       deps: list,
                       maintainer_name: str = "TODO",
                       maintainer_email: str = "todo@todo.com",
                       extra_exec: Optional[list] = None,
                       extra_member: Optional[list] = None,
                       extra_buildtool: Optional[list] = None,
                       extra_test: Optional[list] = None) -> None:
    dep_lines = "\n".join(f"  <depend>{d}</depend>" for d in deps)
    exec_lines = ""
    if extra_exec:
        exec_lines = "\n" + "\n".join(
            f"  <exec_depend>{d}</exec_depend>" for d in extra_exec)
    buildtool_lines = ""
    if extra_buildtool:
        buildtool_lines = "\n" + "\n".join(
            f"  <buildtool_depend>{b}</buildtool_depend>" for b in extra_buildtool)
    member_lines = ""
    if extra_member:
        member_lines = "\n" + "\n".join(
            f"  <member_of_group>{m}</member_of_group>" for m in extra_member)
    test_lines = "\n  <test_depend>ament_lint_auto</test_depend>" \
                 "\n  <test_depend>ament_lint_common</test_depend>"
    if extra_test:
        test_lines += "\n" + "\n".join(
            f"  <test_depend>{t}</test_depend>" for t in extra_test)

    _write(pkg / "package.xml", f"""<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd"
  schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>{name}</name>
  <version>0.1.0</version>
  <description>TODO: Package description</description>
  <maintainer email="{maintainer_email}">{maintainer_name}</maintainer>
  <license>Apache-2.0</license>

  <buildtool_depend>{build_type}</buildtool_depend>{buildtool_lines}
{dep_lines}{exec_lines}
{test_lines}
{member_lines}
  <export>
    <build_type>{build_type}</build_type>
  </export>
</package>
""")


def main():
    parser = argparse.ArgumentParser(
        description="Scaffold a ROS 2 package with best-practice structure")
    parser.add_argument("--version", action="version", version=f"%(prog)s {__version__}")
    parser.add_argument("name", help="Package name (snake_case)")
    parser.add_argument("--type",
                        choices=["cpp", "python", "interfaces",
                                 "hardware_interface"],
                        default="cpp", help="Package type")
    parser.add_argument("--dest", default=".", help="Destination directory")
    parser.add_argument("--component", action="store_true", default=False,
                        help="Register as a composable node component (C++ only)")
    parser.add_argument("--lifecycle", action="store_true", default=False,
                        help="Use LifecycleNode pattern (Python: rclpy LifecycleNode; "
                             "C++: already lifecycle by default)")
    parser.add_argument("--maintainer-name", default="TODO",
                        help="Maintainer name for package.xml (default: TODO)")
    parser.add_argument("--maintainer-email", default="todo@todo.com",
                        help="Maintainer email for package.xml (default: todo@todo.com)")
    parser.add_argument("--robots", type=int, default=0, metavar="N",
                        help="Generate multi-robot fleet launch for N robots")
    parser.add_argument("--sros2", action="store_true", default=False,
                        help="Generate SROS2 security enclave and policy files")
    parser.add_argument("--force", action="store_true", default=False,
                        help="Overwrite existing package directory")
    args = parser.parse_args()

    if not re.match(r'^[a-z][a-z0-9_]*$', args.name):
        print(f"Error: Package name '{args.name}' is invalid. "
              "Use snake_case (lowercase letters, digits, underscores; "
              "must start with a letter).", file=sys.stderr)
        sys.exit(1)

    dest = Path(args.dest)
    if not dest.exists():
        dest.mkdir(parents=True)

    # Overwrite protection
    pkg_dir = dest / args.name
    if pkg_dir.exists() and not args.force:
        print(f"Warning: Package directory '{pkg_dir}' already exists. "
              f"Use --force to overwrite.", file=sys.stderr)
        sys.exit(1)

    m_name = args.maintainer_name
    m_email = args.maintainer_email
    creators = {
        "cpp": lambda n, d: create_cpp_package(
            n, d, args.component, m_name, m_email),
        "python": lambda n, d: create_python_package(
            n, d, m_name, m_email, lifecycle=args.lifecycle),
        "interfaces": lambda n, d: create_interfaces_package(
            n, d, m_name, m_email),
        "hardware_interface": lambda n, d: create_hardware_interface_package(
            n, d, m_name, m_email),
    }
    creators[args.type](args.name, dest)

    # Post-creation extras
    if args.robots > 0 and args.type in ("cpp", "python"):
        lifecycle = args.lifecycle or args.type == "cpp"
        fleet_content = _generate_fleet_launch(
            args.name, args.robots, lifecycle=lifecycle,
            maintainer_name=m_name)
        fleet_path = dest / args.name / "launch" / "fleet.launch.py"
        _write(fleet_path, fleet_content)
        print(f"  + fleet launch for {args.robots} robots: {fleet_path}")

    if args.sros2:
        _generate_sros2_enclave(args.name, dest, maintainer_name=m_name)
        print(f"  + SROS2 security enclave: {dest / args.name / 'security'}")


if __name__ == "__main__":
    main()
