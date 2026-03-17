"""Tests for create_package.py - package scaffolding utility."""

import os
import subprocess
import sys
import xml.etree.ElementTree as ET

SCRIPT = os.path.join(os.path.dirname(__file__), "..", "scripts", "create_package.py")

# Also import the module directly for coverage tracking
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
from create_package import (
    create_cpp_package, create_python_package, create_interfaces_package,
    _class_name, _copyright_cpp, _copyright_py, _generate_launch_file,
    _generate_readme,
)


def run_script(*args: str, cwd: str | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, SCRIPT, *args],
        capture_output=True, text=True, cwd=cwd,
    )


class TestCppPackage:
    def test_creates_expected_structure(self, tmp_path):
        result = run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        assert result.returncode == 0
        pkg = tmp_path / "my_robot"
        assert (pkg / "CMakeLists.txt").exists()
        assert (pkg / "package.xml").exists()
        assert (pkg / "include" / "my_robot" / "my_robot_node.hpp").exists()
        assert (pkg / "src" / "my_robot_node.cpp").exists()
        assert (pkg / "src" / "main.cpp").exists()
        assert (pkg / "launch" / "bringup.launch.py").exists()
        assert (pkg / "config" / "params.yaml").exists()
        assert (pkg / "test" / "test_my_robot.cpp").exists()
        assert (pkg / "README.md").exists()

    def test_package_xml_valid(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        tree = ET.parse(tmp_path / "my_robot" / "package.xml")
        root = tree.getroot()
        assert root.tag == "package"
        assert root.attrib["format"] == "3"
        assert root.find("name").text == "my_robot"
        assert root.find("buildtool_depend").text == "ament_cmake"
        deps = [d.text for d in root.findall("depend")]
        assert "rclcpp" in deps
        assert "rclcpp_lifecycle" in deps

    def test_cmake_contains_project_name(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        cmake = (tmp_path / "my_robot" / "CMakeLists.txt").read_text()
        assert "project(my_robot)" in cmake
        assert "ament_package()" in cmake
        assert "ament_add_gtest" in cmake

    def test_cpp_class_name_camelcase(self, tmp_path):
        run_script("my_cool_robot", "--type", "cpp", "--dest", str(tmp_path))
        hpp = (tmp_path / "my_cool_robot" / "include" / "my_cool_robot" / "my_cool_robot_node.hpp").read_text()
        assert "MyCoolRobotNode" in hpp

    def test_component_flag(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--component", "--dest", str(tmp_path))
        cmake = (tmp_path / "my_robot" / "CMakeLists.txt").read_text()
        assert "rclcpp_components" in cmake
        assert "rclcpp_components_register_node" in cmake
        cpp = (tmp_path / "my_robot" / "src" / "my_robot_node.cpp").read_text()
        assert "RCLCPP_COMPONENTS_REGISTER_NODE" in cpp

    def test_lifecycle_launch_file(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        launch = (tmp_path / "my_robot" / "launch" / "bringup.launch.py").read_text()
        assert "LifecycleNode" in launch
        assert "generate_launch_description" in launch
        assert "Copyright" in launch

    def test_cpp_files_have_copyright(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        hpp = (tmp_path / "my_robot" / "include" / "my_robot" / "my_robot_node.hpp").read_text()
        assert hpp.startswith("// Copyright")
        cpp = (tmp_path / "my_robot" / "src" / "my_robot_node.cpp").read_text()
        assert cpp.startswith("// Copyright")
        main = (tmp_path / "my_robot" / "src" / "main.cpp").read_text()
        assert main.startswith("// Copyright")
        test = (tmp_path / "my_robot" / "test" / "test_my_robot.cpp").read_text()
        assert test.startswith("// Copyright")

    def test_maintainer_args(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path),
                   "--maintainer-name", "Test User", "--maintainer-email", "test@example.com")
        xml = (tmp_path / "my_robot" / "package.xml").read_text()
        assert "Test User" in xml
        assert "test@example.com" in xml


class TestPythonPackage:
    def test_creates_expected_structure(self, tmp_path):
        result = run_script("my_monitor", "--type", "python", "--dest", str(tmp_path))
        assert result.returncode == 0
        pkg = tmp_path / "my_monitor"
        assert (pkg / "setup.py").exists()
        assert (pkg / "setup.cfg").exists()
        assert (pkg / "package.xml").exists()
        assert (pkg / "my_monitor" / "__init__.py").exists()
        assert (pkg / "my_monitor" / "my_monitor_node.py").exists()
        assert (pkg / "launch" / "bringup.launch.py").exists()
        assert (pkg / "config" / "params.yaml").exists()
        assert (pkg / "test" / "test_my_monitor.py").exists()
        assert (pkg / "test" / "test_copyright.py").exists()
        assert (pkg / "test" / "test_flake8.py").exists()
        assert (pkg / "test" / "test_pep257.py").exists()
        assert (pkg / "resource" / "my_monitor").exists()

    def test_package_xml_python_build_type(self, tmp_path):
        run_script("my_monitor", "--type", "python", "--dest", str(tmp_path))
        tree = ET.parse(tmp_path / "my_monitor" / "package.xml")
        root = tree.getroot()
        export = root.find("export")
        assert export is not None
        build_type = export.find("build_type")
        assert build_type is not None
        assert build_type.text == "ament_python"

    def test_entry_point_in_setup(self, tmp_path):
        run_script("my_monitor", "--type", "python", "--dest", str(tmp_path))
        setup = (tmp_path / "my_monitor" / "setup.py").read_text()
        assert "my_monitor_node = my_monitor.my_monitor_node:main" in setup

    def test_node_class_exists(self, tmp_path):
        run_script("my_monitor", "--type", "python", "--dest", str(tmp_path))
        node = (tmp_path / "my_monitor" / "my_monitor" / "my_monitor_node.py").read_text()
        assert "class MyMonitorNode" in node
        assert "def main" in node
        assert "Copyright" in node

    def test_python_files_have_copyright(self, tmp_path):
        run_script("my_monitor", "--type", "python", "--dest", str(tmp_path))
        init = (tmp_path / "my_monitor" / "my_monitor" / "__init__.py").read_text()
        assert "Copyright" in init
        setup = (tmp_path / "my_monitor" / "setup.py").read_text()
        assert "Copyright" in setup
        launch = (tmp_path / "my_monitor" / "launch" / "bringup.launch.py").read_text()
        assert "Copyright" in launch

    def test_standard_launch_file(self, tmp_path):
        run_script("my_monitor", "--type", "python", "--dest", str(tmp_path))
        launch = (tmp_path / "my_monitor" / "launch" / "bringup.launch.py").read_text()
        # Python packages use regular Node, not LifecycleNode
        assert "Node(" in launch
        assert "generate_launch_description" in launch


class TestInterfacesPackage:
    def test_creates_expected_structure(self, tmp_path):
        result = run_script("my_interfaces", "--type", "interfaces", "--dest", str(tmp_path))
        assert result.returncode == 0
        pkg = tmp_path / "my_interfaces"
        assert (pkg / "CMakeLists.txt").exists()
        assert (pkg / "package.xml").exists()
        assert (pkg / "msg" / "Status.msg").exists()
        assert (pkg / "srv" / "SetMode.srv").exists()

    def test_cmake_has_rosidl(self, tmp_path):
        run_script("my_interfaces", "--type", "interfaces", "--dest", str(tmp_path))
        cmake = (tmp_path / "my_interfaces" / "CMakeLists.txt").read_text()
        assert "rosidl_generate_interfaces" in cmake
        assert "std_msgs" in cmake

    def test_package_xml_has_rosidl_deps(self, tmp_path):
        run_script("my_interfaces", "--type", "interfaces", "--dest", str(tmp_path))
        tree = ET.parse(tmp_path / "my_interfaces" / "package.xml")
        root = tree.getroot()
        buildtool_deps = [d.text for d in root.findall("buildtool_depend")]
        assert "rosidl_default_generators" in buildtool_deps
        exec_deps = [d.text for d in root.findall("exec_depend")]
        assert "rosidl_default_runtime" in exec_deps

    def test_member_of_group_at_package_level(self, tmp_path):
        """member_of_group must be a direct child of <package>, not inside <export>."""
        run_script("my_interfaces", "--type", "interfaces", "--dest", str(tmp_path))
        tree = ET.parse(tmp_path / "my_interfaces" / "package.xml")
        root = tree.getroot()
        # Must exist at package level
        members = [m.text for m in root.findall("member_of_group")]
        assert "rosidl_interface_packages" in members
        # Must NOT be inside <export>
        export = root.find("export")
        export_members = [m.text for m in export.findall("member_of_group")]
        assert len(export_members) == 0


class TestDirectFunctions:
    """Test functions directly (not via subprocess) for coverage."""

    def test_class_name_conversion(self):
        assert _class_name("my_robot") == "MyRobot"
        assert _class_name("arm_controller") == "ArmController"
        assert _class_name("single") == "Single"
        assert _class_name("a_b_c") == "ABC"

    def test_generate_launch_file_standard(self):
        launch = _generate_launch_file("test_pkg")
        assert "generate_launch_description" in launch
        assert "Node(" in launch
        assert "package='test_pkg'" in launch
        assert "LifecycleNode" not in launch
        assert "Copyright" in launch

    def test_generate_launch_file_lifecycle(self):
        launch = _generate_launch_file("test_pkg", lifecycle=True)
        assert "generate_launch_description" in launch
        assert "LifecycleNode(" in launch
        assert "package='test_pkg'" in launch
        assert "Copyright" in launch

    def test_copyright_py_header(self):
        header = _copyright_py("TestMaintainer")
        assert "Copyright 2024 TestMaintainer" in header
        assert "Apache License" in header

    def test_copyright_cpp_header(self):
        header = _copyright_cpp("TestMaintainer")
        assert "Copyright 2024 TestMaintainer" in header
        assert "Apache License" in header

    def test_generate_readme(self):
        readme = _generate_readme("my_pkg")
        assert "# my_pkg" in readme
        assert "ros2 launch my_pkg" in readme

    def test_create_cpp_direct(self, tmp_path):
        create_cpp_package("test_bot", tmp_path)
        pkg = tmp_path / "test_bot"
        assert (pkg / "CMakeLists.txt").exists()
        assert (pkg / "include" / "test_bot" / "test_bot_node.hpp").exists()
        assert (pkg / "src" / "test_bot_node.cpp").exists()
        assert (pkg / "src" / "main.cpp").exists()
        assert (pkg / "config" / "params.yaml").exists()
        assert (pkg / "test" / "test_test_bot.cpp").exists()

    def test_create_cpp_component_direct(self, tmp_path):
        create_cpp_package("test_bot", tmp_path, component=True)
        cmake = (tmp_path / "test_bot" / "CMakeLists.txt").read_text()
        assert "rclcpp_components_register_node" in cmake
        cpp = (tmp_path / "test_bot" / "src" / "test_bot_node.cpp").read_text()
        assert "RCLCPP_COMPONENTS_REGISTER_NODE" in cpp

    def test_create_python_direct(self, tmp_path):
        create_python_package("test_mon", tmp_path)
        pkg = tmp_path / "test_mon"
        assert (pkg / "setup.py").exists()
        assert (pkg / "setup.cfg").exists()
        assert (pkg / "test_mon" / "__init__.py").exists()
        assert (pkg / "test_mon" / "test_mon_node.py").exists()
        assert (pkg / "resource" / "test_mon").exists()

    def test_create_interfaces_direct(self, tmp_path):
        create_interfaces_package("test_iface", tmp_path)
        pkg = tmp_path / "test_iface"
        assert (pkg / "CMakeLists.txt").exists()
        assert (pkg / "msg" / "Status.msg").exists()
        assert (pkg / "srv" / "SetMode.srv").exists()


class TestMainFunction:
    """Test main() directly for coverage."""

    def test_main_creates_package(self, tmp_path, monkeypatch):
        from create_package import main
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "test_pkg", "--type", "cpp",
             "--dest", str(tmp_path)])
        main()
        assert (tmp_path / "test_pkg" / "CMakeLists.txt").exists()

    def test_main_invalid_name_exits(self, tmp_path, monkeypatch):
        from create_package import main
        import pytest as _pytest
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "BadName", "--type", "cpp",
             "--dest", str(tmp_path)])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1

    def test_main_overwrite_protection_exits(self, tmp_path, monkeypatch):
        from create_package import main
        import pytest as _pytest
        # Create first
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "test_pkg", "--type", "cpp",
             "--dest", str(tmp_path)])
        main()
        # Try again without --force
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "test_pkg", "--type", "cpp",
             "--dest", str(tmp_path)])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1

    def test_main_python_type(self, tmp_path, monkeypatch):
        from create_package import main
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "py_pkg", "--type", "python",
             "--dest", str(tmp_path)])
        main()
        assert (tmp_path / "py_pkg" / "setup.py").exists()

    def test_main_interfaces_type(self, tmp_path, monkeypatch):
        from create_package import main
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "iface_pkg", "--type", "interfaces",
             "--dest", str(tmp_path)])
        main()
        assert (tmp_path / "iface_pkg" / "msg" / "Status.msg").exists()

    def test_main_creates_dest_if_missing(self, tmp_path, monkeypatch):
        from create_package import main
        dest = tmp_path / "new_dir"
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "test_pkg", "--type", "cpp",
             "--dest", str(dest)])
        main()
        assert (dest / "test_pkg" / "CMakeLists.txt").exists()

    def test_main_maintainer_args(self, tmp_path, monkeypatch):
        from create_package import main
        monkeypatch.setattr(
            "sys.argv",
            ["create_package.py", "test_pkg", "--type", "cpp",
             "--dest", str(tmp_path),
             "--maintainer-name", "Bot",
             "--maintainer-email", "bot@test.com"])
        main()
        xml = (tmp_path / "test_pkg" / "package.xml").read_text()
        assert "Bot" in xml
        assert "bot@test.com" in xml


class TestVersion:
    def test_version_flag(self):
        result = run_script("--version")
        assert result.returncode == 0
        assert "0.1.0" in result.stdout


class TestValidation:
    def test_invalid_name_rejected(self, tmp_path):
        result = run_script("InvalidName", "--type", "cpp", "--dest", str(tmp_path))
        assert result.returncode != 0
        assert "invalid" in result.stderr.lower()

    def test_name_starting_with_digit_rejected(self, tmp_path):
        result = run_script("1bad_name", "--type", "cpp", "--dest", str(tmp_path))
        assert result.returncode != 0

    def test_overwrite_protection(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        result = run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        assert result.returncode != 0
        assert "already exists" in result.stderr

    def test_force_overwrite(self, tmp_path):
        run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path))
        result = run_script("my_robot", "--type", "cpp", "--dest", str(tmp_path), "--force")
        assert result.returncode == 0
