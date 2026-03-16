#!/usr/bin/env python3
"""Scaffold a ROS 2 package following ros2-engineering-skills conventions.

Usage:
    python create_package.py my_robot_driver --type cpp
    python create_package.py my_robot_monitor --type python
    python create_package.py my_robot_interfaces --type interfaces
"""

import argparse
import os
import re
import sys
from pathlib import Path


def create_cpp_package(name: str, dest: Path) -> None:
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

    (pkg / "CMakeLists.txt").write_text(f"""cmake_minimum_required(VERSION 3.8)
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
ament_target_dependencies(${{PROJECT_NAME}}_lib rclcpp rclcpp_lifecycle)
# NOTE: ament_target_dependencies() is deprecated from Kilted (May 2025).
# For forward compat, prefer: target_link_libraries(${{PROJECT_NAME}}_lib PUBLIC rclcpp::rclcpp ...)

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

    class_name = "".join(w.capitalize() for w in name.split("_"))

    (pkg / "include" / name / f"{name}_node.hpp").write_text(f"""#pragma once
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
}};

}}  // namespace {name}
""")

    (pkg / "src" / f"{name}_node.cpp").write_text(f"""#include "{name}/{name}_node.hpp"

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

}}  // namespace {name}
""")

    (pkg / "src" / "main.cpp").write_text(f"""#include <rclcpp/rclcpp.hpp>
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

    (pkg / "config" / "params.yaml").write_text(f"""{name}:
  ros__parameters:
    # Add parameters here
    publish_rate: 50.0
""")

    (pkg / "test" / f"test_{name}.cpp").write_text(f"""#include <gtest/gtest.h>
#include <rclcpp/rclcpp.hpp>
#include "{name}/{name}_node.hpp"

class {class_name}Test : public ::testing::Test
{{
protected:
  static void SetUpTestSuite() {{ rclcpp::init(0, nullptr); }}
  static void TearDownTestSuite() {{ rclcpp::shutdown(); }}
}};

TEST_F({class_name}Test, NodeCreation)
{{
  auto node = std::make_shared<{name}::{class_name}Node>();
  ASSERT_NE(node, nullptr);
}}
""")

    _write_package_xml(pkg, name, "ament_cmake",
                       ["rclcpp", "rclcpp_lifecycle"])
    print(f"Created C++ package: {pkg}")


def create_python_package(name: str, dest: Path) -> None:
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

    (pkg / name / "__init__.py").write_text("")
    (pkg / "resource" / name).write_text("")

    class_name = "".join(w.capitalize() for w in name.split("_"))

    (pkg / name / f"{name}_node.py").write_text(f"""import rclpy
from rclpy.node import Node


class {class_name}Node(Node):
    def __init__(self):
        super().__init__('{name}')
        self.declare_parameter('publish_rate', 10.0)
        rate = self.get_parameter('publish_rate').value
        self.timer = self.create_timer(1.0 / rate, self.timer_callback)
        self.get_logger().info('Node started')

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
""")

    (pkg / "setup.py").write_text(f"""from setuptools import find_packages, setup

package_name = '{name}'

setup(
    name=package_name,
    version='0.1.0',
    packages=find_packages(exclude=['test']),
    data_files=[
        ('share/ament_index/resource_index/packages', ['resource/' + package_name]),
        ('share/' + package_name, ['package.xml']),
        # launch files will be added here when created, e.g.:
        # ('share/' + package_name + '/launch', ['launch/bringup.launch.py']),
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

    (pkg / "setup.cfg").write_text(f"""[develop]
script_dir=$base/lib/{name}
[install]
install_scripts=$base/lib/{name}
""")

    (pkg / "config" / "params.yaml").write_text(f"""{name}:
  ros__parameters:
    publish_rate: 10.0
""")

    (pkg / "test" / f"test_{name}.py").write_text(f"""import pytest
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

    _write_package_xml(pkg, name, "ament_python", ["rclpy"])
    print(f"Created Python package: {pkg}")


def create_interfaces_package(name: str, dest: Path) -> None:
    pkg = dest / name
    dirs = [pkg / "msg", pkg / "srv", pkg / "action"]
    for d in dirs:
        d.mkdir(parents=True, exist_ok=True)

    (pkg / "msg" / "Status.msg").write_text("""std_msgs/Header header
uint8 mode
string description
float64 battery_voltage
""")

    (pkg / "srv" / "SetMode.srv").write_text("""string mode
bool force
---
bool success
string message
""")

    (pkg / "CMakeLists.txt").write_text(f"""cmake_minimum_required(VERSION 3.8)
project({name})

find_package(ament_cmake REQUIRED)
find_package(rosidl_default_generators REQUIRED)
find_package(std_msgs REQUIRED)

rosidl_generate_interfaces(${{PROJECT_NAME}}
  "msg/Status.msg"
  "srv/SetMode.srv"
  DEPENDENCIES std_msgs
)

ament_export_dependencies(rosidl_default_runtime)
ament_package()
""")

    _write_package_xml(pkg, name, "ament_cmake",
                       ["std_msgs"],
                       extra_buildtool=["rosidl_default_generators"],
                       extra_exec=["rosidl_default_runtime"],
                       extra_member=["rosidl_interface_packages"])
    print(f"Created interfaces package: {pkg}")


def _write_package_xml(pkg: Path, name: str, build_type: str,
                       deps: list, extra_exec: list = None,
                       extra_member: list = None,
                       extra_buildtool: list = None) -> None:
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
            f"    <member_of_group>{m}</member_of_group>" for m in extra_member)

    (pkg / "package.xml").write_text(f"""<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd"
  schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>{name}</name>
  <version>0.1.0</version>
  <description>TODO: Package description</description>
  <maintainer email="todo@todo.com">TODO</maintainer>
  <license>Apache-2.0</license>

  <buildtool_depend>{build_type}</buildtool_depend>{buildtool_lines}
{dep_lines}{exec_lines}

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>{build_type}</build_type>{member_lines}
  </export>
</package>
""")


def main():
    parser = argparse.ArgumentParser(
        description="Scaffold a ROS 2 package with best-practice structure")
    parser.add_argument("name", help="Package name (snake_case)")
    parser.add_argument("--type", choices=["cpp", "python", "interfaces"],
                        default="cpp", help="Package type")
    parser.add_argument("--dest", default=".", help="Destination directory")
    args = parser.parse_args()

    if not re.match(r'^[a-z][a-z0-9_]*$', args.name):
        print(f"Error: Package name '{args.name}' is invalid. "
              "Use snake_case (lowercase letters, digits, underscores; "
              "must start with a letter).", file=sys.stderr)
        sys.exit(1)

    dest = Path(args.dest)
    if not dest.exists():
        dest.mkdir(parents=True)

    creators = {
        "cpp": create_cpp_package,
        "python": create_python_package,
        "interfaces": create_interfaces_package,
    }
    creators[args.type](args.name, dest)


if __name__ == "__main__":
    main()
