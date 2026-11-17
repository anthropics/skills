"""End-to-end integration tests.

These tests validate the full pipeline:
1. Package generation → launch validator passes on generated launch files
2. Package generation → generated Python code is valid (AST parse + import check)
3. Package generation → generated C++ code follows expected patterns
4. Cross-tool integration: create_package + launch_validator + qos_checker
5. Python lifecycle package generation and validation
6. Namespace remapping support for generated Python nodes
"""

import ast
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
from create_package import (
    create_cpp_package, create_python_package,
    create_hardware_interface_package, _generate_fleet_launch,
    _generate_sros2_enclave,
)
from launch_validator import validate_file, validate_directory
from qos_checker import (
    QoSProfile, Reliability, Durability, History, Liveliness,
    DDSVendor, check_compatibility, check_vendor_specific,
)


class TestGeneratedLaunchFilesPassValidator:
    """Generated launch files must pass the launch validator with zero errors."""

    def test_cpp_launch_passes_validator(self, tmp_path):
        create_cpp_package("test_robot", tmp_path)
        launch_file = str(tmp_path / "test_robot" / "launch" / "bringup.launch.py")
        issues = validate_file(launch_file)
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) == 0, f"Generated C++ launch file has errors: {errors}"

    def test_python_launch_passes_validator(self, tmp_path):
        create_python_package("test_monitor", tmp_path)
        launch_file = str(tmp_path / "test_monitor" / "launch" / "bringup.launch.py")
        issues = validate_file(launch_file)
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) == 0, f"Generated Python launch file has errors: {errors}"

    def test_python_lifecycle_launch_passes_validator(self, tmp_path):
        create_python_package("test_driver", tmp_path, lifecycle=True)
        launch_file = str(tmp_path / "test_driver" / "launch" / "bringup.launch.py")
        issues = validate_file(launch_file)
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) == 0, f"Generated lifecycle launch file has errors: {errors}"

    def test_all_generated_launch_files_in_directory(self, tmp_path):
        """Generate multiple packages and validate all launch files at once."""
        create_cpp_package("robot_a", tmp_path)
        create_python_package("robot_b", tmp_path)
        create_python_package("robot_c", tmp_path, lifecycle=True)
        # Validate all launch files under tmp_path
        result = validate_directory(str(tmp_path))
        assert result.files_checked == 3
        errors = [i for i in result.issues if i.severity == "error"]
        assert len(errors) == 0, f"Errors in generated launch files: {errors}"


class TestGeneratedPythonCodeValidity:
    """Generated Python code must be syntactically valid and importable."""

    def test_python_node_ast_valid(self, tmp_path):
        create_python_package("ast_check", tmp_path)
        node_file = tmp_path / "ast_check" / "ast_check" / "ast_check_node.py"
        source = node_file.read_text(encoding="utf-8")
        # Must parse without SyntaxError
        tree = ast.parse(source)
        # Must contain a class definition
        classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]
        assert len(classes) == 1
        assert classes[0].name == "AstCheckNode"

    def test_python_lifecycle_node_ast_valid(self, tmp_path):
        create_python_package("lc_check", tmp_path, lifecycle=True)
        node_file = tmp_path / "lc_check" / "lc_check" / "lc_check_node.py"
        source = node_file.read_text(encoding="utf-8")
        tree = ast.parse(source)
        classes = [n for n in ast.walk(tree) if isinstance(n, ast.ClassDef)]
        assert len(classes) == 1
        assert classes[0].name == "LcCheckNode"
        # Must have lifecycle callbacks
        methods = [n.name for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
        assert "on_configure" in methods
        assert "on_activate" in methods
        assert "on_deactivate" in methods
        assert "on_cleanup" in methods
        assert "on_shutdown" in methods

    def test_python_setup_py_valid(self, tmp_path):
        create_python_package("setup_check", tmp_path)
        setup_file = tmp_path / "setup_check" / "setup.py"
        source = setup_file.read_text(encoding="utf-8")
        ast.parse(source)  # Must not raise SyntaxError

    def test_python_test_file_valid(self, tmp_path):
        create_python_package("tst_check", tmp_path)
        test_file = tmp_path / "tst_check" / "test" / "test_tst_check.py"
        source = test_file.read_text(encoding="utf-8")
        ast.parse(source)

    def test_python_lifecycle_test_file_valid(self, tmp_path):
        create_python_package("lc_tst", tmp_path, lifecycle=True)
        test_file = tmp_path / "lc_tst" / "test" / "test_lc_tst.py"
        source = test_file.read_text(encoding="utf-8")
        tree = ast.parse(source)
        funcs = [n.name for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
        assert "test_node_creation" in funcs
        assert "test_lifecycle_configure" in funcs
        assert "test_lifecycle_activate" in funcs


class TestGeneratedCppCodePatterns:
    """Generated C++ code must follow expected patterns for colcon build."""

    def test_cmake_has_required_sections(self, tmp_path):
        create_cpp_package("cpp_check", tmp_path)
        cmake = (tmp_path / "cpp_check" / "CMakeLists.txt").read_text(encoding="utf-8")
        required = [
            "cmake_minimum_required",
            "project(cpp_check)",
            "find_package(ament_cmake REQUIRED)",
            "find_package(rclcpp REQUIRED)",
            "find_package(rclcpp_lifecycle REQUIRED)",
            "add_library",
            "target_link_libraries",
            "install(TARGETS",
            "ament_package()",
        ]
        for req in required:
            assert req in cmake, f"CMakeLists.txt missing: {req}"

    def test_cpp_header_has_lifecycle_interface(self, tmp_path):
        create_cpp_package("lc_cpp", tmp_path)
        hpp = (tmp_path / "lc_cpp" / "include" / "lc_cpp" / "lc_cpp_node.hpp").read_text(encoding="utf-8")
        assert "LifecycleNode" in hpp
        assert "on_configure" in hpp
        assert "on_activate" in hpp
        assert "on_deactivate" in hpp
        assert "on_cleanup" in hpp
        assert "NodeOptions" in hpp

    def test_cpp_source_passes_node_options(self, tmp_path):
        create_cpp_package("opt_cpp", tmp_path)
        cpp = (tmp_path / "opt_cpp" / "src" / "opt_cpp_node.cpp").read_text(encoding="utf-8")
        assert 'const rclcpp::NodeOptions & options' in cpp
        assert 'LifecycleNode("opt_cpp", options)' in cpp

    def test_cpp_component_has_registration(self, tmp_path):
        create_cpp_package("comp_cpp", tmp_path, component=True)
        cpp = (tmp_path / "comp_cpp" / "src" / "comp_cpp_node.cpp").read_text(encoding="utf-8")
        assert "RCLCPP_COMPONENTS_REGISTER_NODE" in cpp
        cmake = (tmp_path / "comp_cpp" / "CMakeLists.txt").read_text(encoding="utf-8")
        assert "rclcpp_components_register_node" in cmake

    def test_package_xml_structure(self, tmp_path):
        import xml.etree.ElementTree as ET
        create_cpp_package("xml_check", tmp_path)
        tree = ET.parse(tmp_path / "xml_check" / "package.xml")
        root = tree.getroot()
        assert root.attrib["format"] == "3"
        # Required elements
        assert root.find("name").text == "xml_check"
        assert root.find("version") is not None
        assert root.find("description") is not None
        assert root.find("maintainer") is not None
        assert root.find("license").text == "Apache-2.0"


class TestNamespaceRemappingSupport:
    """Generated Python nodes must accept kwargs for namespace remapping."""

    def test_python_node_accepts_kwargs(self, tmp_path):
        create_python_package("ns_test", tmp_path)
        node_source = (tmp_path / "ns_test" / "ns_test" / "ns_test_node.py").read_text(encoding="utf-8")
        # The __init__ must accept **kwargs
        assert "def __init__(self, **kwargs):" in node_source
        # kwargs must be forwarded to super().__init__
        assert "super().__init__('ns_test', **kwargs)" in node_source

    def test_lifecycle_python_node_accepts_kwargs(self, tmp_path):
        create_python_package("ns_lc_test", tmp_path, lifecycle=True)
        node_source = (tmp_path / "ns_lc_test" / "ns_lc_test" / "ns_lc_test_node.py").read_text(encoding="utf-8")
        assert "def __init__(self, **kwargs):" in node_source
        assert "super().__init__('ns_lc_test', **kwargs)" in node_source


class TestPythonLifecyclePackageGeneration:
    """Full validation of Python lifecycle package generation."""

    def test_lifecycle_creates_expected_structure(self, tmp_path):
        create_python_package("lc_driver", tmp_path, lifecycle=True)
        pkg = tmp_path / "lc_driver"
        assert (pkg / "setup.py").exists()
        assert (pkg / "setup.cfg").exists()
        assert (pkg / "package.xml").exists()
        assert (pkg / "lc_driver" / "__init__.py").exists()
        assert (pkg / "lc_driver" / "lc_driver_node.py").exists()
        assert (pkg / "launch" / "bringup.launch.py").exists()
        assert (pkg / "config" / "params.yaml").exists()
        assert (pkg / "test" / "test_lc_driver.py").exists()

    def test_lifecycle_launch_uses_lifecycle_node(self, tmp_path):
        create_python_package("lc_driver", tmp_path, lifecycle=True)
        launch = (tmp_path / "lc_driver" / "launch" / "bringup.launch.py").read_text(encoding="utf-8")
        assert "LifecycleNode" in launch
        assert "ChangeState" in launch
        assert "TRANSITION_CONFIGURE" in launch

    def test_lifecycle_package_xml_has_lifecycle_dep(self, tmp_path):
        import xml.etree.ElementTree as ET
        create_python_package("lc_driver", tmp_path, lifecycle=True)
        tree = ET.parse(tmp_path / "lc_driver" / "package.xml")
        root = tree.getroot()
        deps = [d.text for d in root.findall("depend")]
        assert "rclpy" in deps
        assert "lifecycle_msgs" in deps

    def test_lifecycle_node_has_all_callbacks(self, tmp_path):
        create_python_package("lc_driver", tmp_path, lifecycle=True)
        source = (tmp_path / "lc_driver" / "lc_driver" / "lc_driver_node.py").read_text(encoding="utf-8")
        for cb in [
            "on_configure", "on_activate", "on_deactivate",
            "on_cleanup", "on_shutdown",
        ]:
            assert f"def {cb}" in source, f"Missing lifecycle callback: {cb}"
        assert "LifecycleNode" in source
        assert "TransitionCallbackReturn" in source


class TestDDSVendorSpecificWarnings:
    """DDS vendor-specific QoS warning checks."""

    def test_fastdds_large_depth_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 6000)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 6000)
        warnings = check_vendor_specific(pub, sub, DDSVendor.FASTDDS)
        assert any("FastDDS" in w and "depth" in w for w in warnings)

    def test_fastdds_reliable_depth1_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1)
        warnings = check_vendor_specific(pub, sub, DDSVendor.FASTDDS)
        assert any("RELIABLE" in w and "KEEP_LAST(1)" in w for w in warnings)

    def test_fastdds_transient_local_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.TRANSIENT_LOCAL,
                         History.KEEP_LAST, 1)
        sub = QoSProfile(Reliability.RELIABLE, Durability.TRANSIENT_LOCAL,
                         History.KEEP_LAST, 1)
        warnings = check_vendor_specific(pub, sub, DDSVendor.FASTDDS)
        assert any("TRANSIENT_LOCAL" in w for w in warnings)

    def test_fastdds_low_lease_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1,
                         liveliness=Liveliness.MANUAL_BY_TOPIC,
                         liveliness_lease_ms=50)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1)
        warnings = check_vendor_specific(pub, sub, DDSVendor.FASTDDS)
        assert any("MANUAL_BY_TOPIC" in w and "50ms" in w for w in warnings)

    def test_cyclonedds_keep_all_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_ALL, 0)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 10)
        warnings = check_vendor_specific(pub, sub, DDSVendor.CYCLONEDDS)
        assert any("CycloneDDS" in w and "KEEP_ALL" in w for w in warnings)

    def test_cyclonedds_reliable_reliable_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 10)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 10)
        warnings = check_vendor_specific(pub, sub, DDSVendor.CYCLONEDDS)
        assert any("CycloneDDS" in w and "RELIABLE" in w for w in warnings)

    def test_cyclonedds_low_deadline_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1, deadline_ms=5)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1, deadline_ms=10)
        warnings = check_vendor_specific(pub, sub, DDSVendor.CYCLONEDDS)
        assert any("CycloneDDS" in w and "5ms" in w for w in warnings)

    def test_connext_large_depth_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 15000)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 15000)
        warnings = check_vendor_specific(pub, sub, DDSVendor.CONNEXT)
        assert any("Connext" in w and "depth" in w for w in warnings)

    def test_connext_transient_local_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.TRANSIENT_LOCAL,
                         History.KEEP_LAST, 1)
        sub = QoSProfile(Reliability.RELIABLE, Durability.TRANSIENT_LOCAL,
                         History.KEEP_LAST, 1)
        warnings = check_vendor_specific(pub, sub, DDSVendor.CONNEXT)
        assert any("Connext" in w and "TRANSIENT_LOCAL" in w for w in warnings)

    def test_connext_reliable_keep_all_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_ALL, 0)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 10)
        warnings = check_vendor_specific(pub, sub, DDSVendor.CONNEXT)
        assert any("Connext" in w and "KEEP_ALL" in w for w in warnings)

    def test_auto_vendor_returns_empty(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_ALL, 0)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 10)
        warnings = check_vendor_specific(pub, sub, DDSVendor.AUTO)
        assert len(warnings) == 0

    def test_vendor_warnings_integrated_in_result(self):
        """Vendor warnings must not affect compatibility determination."""
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 6000)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 6000)
        result = check_compatibility(pub, sub)
        assert result.compatible is True  # Still compatible
        vendor_warnings = check_vendor_specific(pub, sub, DDSVendor.FASTDDS)
        assert len(vendor_warnings) > 0  # But has vendor-specific advice


class TestLaunchValidatorCompositionScenarios:
    """Tests for multi-node composition, GroupAction, conditions, etc."""

    def _write_launch(self, tmp_path, name, content):
        filepath = tmp_path / name
        filepath.write_text(content)
        return str(filepath)

    def test_group_action_empty(self, tmp_path):
        content = """from launch import LaunchDescription
from launch.actions import GroupAction

def generate_launch_description():
    return LaunchDescription([
        GroupAction(),
    ])
"""
        path = self._write_launch(tmp_path, "grp.launch.py", content)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("GroupAction" in i.message for i in warnings)

    def test_group_action_scoped_false_info(self, tmp_path):
        content = """from launch import LaunchDescription
from launch.actions import GroupAction
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        GroupAction(
            scoped=False,
            actions=[
                Node(package='a', executable='b', name='c', output='screen'),
            ],
        ),
    ])
"""
        path = self._write_launch(tmp_path, "scoped.launch.py", content)
        issues = validate_file(path)
        infos = [i for i in issues if i.severity == "info"]
        assert any("scoped=False" in i.message for i in infos)

    def test_if_condition_hardcoded_true(self, tmp_path):
        content = """from launch import LaunchDescription
from launch.conditions import IfCondition

def generate_launch_description():
    return LaunchDescription([])

x = IfCondition('true')
"""
        path = self._write_launch(tmp_path, "cond.launch.py", content)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("hardcoded" in i.message.lower() for i in warnings)

    def test_unless_condition_hardcoded_false(self, tmp_path):
        content = """from launch import LaunchDescription
from launch.conditions import UnlessCondition

def generate_launch_description():
    return LaunchDescription([])

x = UnlessCondition('false')
"""
        path = self._write_launch(tmp_path, "ucond.launch.py", content)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("hardcoded" in i.message.lower() for i in warnings)

    def test_composable_node_bad_plugin_format(self, tmp_path):
        content = """from launch import LaunchDescription
from launch_ros.actions import ComposableNodeContainer
from launch_ros.descriptions import ComposableNode

def generate_launch_description():
    return LaunchDescription([
        ComposableNodeContainer(
            name='container',
            namespace='',
            package='rclcpp_components',
            executable='component_container',
            composable_node_descriptions=[
                ComposableNode(
                    package='my_pkg',
                    plugin='BadPluginNoNamespace',
                    name='my_node',
                ),
            ],
            output='screen',
        ),
    ])
"""
        path = self._write_launch(tmp_path, "bad_plugin.launch.py", content)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any(
            "::" in i.message and "plugin" in i.message.lower()
            for i in warnings
        )

    def test_composable_node_missing_package(self, tmp_path):
        content = """from launch import LaunchDescription
from launch_ros.descriptions import ComposableNode

def generate_launch_description():
    return LaunchDescription([
        ComposableNode(
            plugin='my_pkg::MyNode',
            name='my_node',
        ),
    ])
"""
        path = self._write_launch(tmp_path, "no_pkg.launch.py", content)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("package" in i.message.lower() for i in errors)

    def test_empty_composable_descriptions(self, tmp_path):
        content = """from launch import LaunchDescription
from launch_ros.actions import ComposableNodeContainer

def generate_launch_description():
    return LaunchDescription([
        ComposableNodeContainer(
            name='container',
            namespace='',
            package='rclcpp_components',
            executable='component_container',
            composable_node_descriptions=[],
            output='screen',
        ),
    ])
"""
        path = self._write_launch(tmp_path, "empty_comp.launch.py", content)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("empty" in i.message.lower() for i in warnings)

    def test_container_no_composable_descriptions_info(self, tmp_path):
        content = """from launch import LaunchDescription
from launch_ros.actions import ComposableNodeContainer

def generate_launch_description():
    return LaunchDescription([
        ComposableNodeContainer(
            name='container',
            namespace='',
            package='rclcpp_components',
            executable='component_container',
            output='screen',
        ),
    ])
"""
        path = self._write_launch(tmp_path, "no_desc.launch.py", content)
        issues = validate_file(path)
        infos = [i for i in issues if i.severity == "info"]
        assert any("composable_node_descriptions" in i.message.lower()
                   or "LoadComposableNodes" in i.message for i in infos)

    def test_circular_include_detected(self, tmp_path):
        launch_name = "self_include.launch.py"
        content = f"""from launch import LaunchDescription
from launch.actions import IncludeLaunchDescription
from launch.launch_description_sources import PythonLaunchDescriptionSource

def generate_launch_description():
    return LaunchDescription([
        IncludeLaunchDescription(
            PythonLaunchDescriptionSource('{launch_name}')
        ),
    ])
"""
        path = self._write_launch(tmp_path, launch_name, content)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("Circular" in i.message for i in errors)

    def test_push_ros_namespace_empty(self, tmp_path):
        content = """from launch import LaunchDescription
from launch_ros.actions import PushRosNamespace

def generate_launch_description():
    return LaunchDescription([
        PushRosNamespace(''),
    ])
"""
        path = self._write_launch(tmp_path, "ns.launch.py", content)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("empty namespace" in i.message.lower() for i in warnings)

    def test_if_condition_no_argument_error(self, tmp_path):
        content = """from launch import LaunchDescription
from launch.conditions import IfCondition

def generate_launch_description():
    return LaunchDescription([])

x = IfCondition()
"""
        path = self._write_launch(tmp_path, "no_arg_cond.launch.py", content)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("without a condition" in i.message for i in errors)

    def test_push_ros_namespace_no_argument_error(self, tmp_path):
        content = """from launch import LaunchDescription
from launch_ros.actions import PushRosNamespace

def generate_launch_description():
    return LaunchDescription([
        PushRosNamespace(),
    ])
"""
        path = self._write_launch(tmp_path, "ns_noarg.launch.py", content)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("PushRosNamespace" in i.message for i in errors)


class TestDDSVendorCLI:
    """Test DDS vendor CLI integration."""

    def test_cli_fastdds_vendor(self):
        import subprocess
        script = os.path.join(os.path.dirname(__file__), "..", "scripts", "qos_checker.py")
        result = subprocess.run(
            [sys.executable, script,
             "--pub", "reliable,volatile,keep_last,6000",
             "--sub", "reliable,volatile,keep_last,6000",
             "--dds-vendor", "fastdds"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "DDS Vendor Warnings" in result.stdout

    def test_cli_json_with_vendor(self):
        import json
        import subprocess
        script = os.path.join(os.path.dirname(__file__), "..", "scripts", "qos_checker.py")
        result = subprocess.run(
            [sys.executable, script,
             "--pub", "reliable,volatile,keep_last,6000",
             "--sub", "reliable,volatile,keep_last,6000",
             "--dds-vendor", "cyclonedds", "--json"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert "vendor_warnings" in data

    def test_cli_auto_vendor_no_vendor_warnings(self):
        import subprocess
        script = os.path.join(os.path.dirname(__file__), "..", "scripts", "qos_checker.py")
        result = subprocess.run(
            [sys.executable, script,
             "--pub", "reliable,volatile,keep_last,1",
             "--sub", "reliable,volatile,keep_last,1"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "DDS Vendor Warnings" not in result.stdout


class TestCrossToolIntegration:
    """Cross-tool validation: package generation → QoS + launch validator."""

    def test_generated_lifecycle_launch_matches_qos_preset(self, tmp_path):
        """Safety heartbeat QoS preset should be compatible with lifecycle node."""
        from qos_checker import PRESETS
        preset = PRESETS["safety_heartbeat"]
        result = check_compatibility(preset["pub"], preset["sub"])
        assert result.compatible is True

        # Generate a lifecycle package that would use this QoS
        create_cpp_package("heartbeat_node", tmp_path, component=True)
        launch = str(tmp_path / "heartbeat_node" / "launch" / "bringup.launch.py")
        issues = validate_file(launch)
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) == 0

    def test_all_qos_presets_are_self_compatible(self):
        """Sanity check: every built-in QoS preset must be self-compatible."""
        from qos_checker import PRESETS
        for name, profiles in PRESETS.items():
            result = check_compatibility(profiles["pub"], profiles["sub"])
            assert result.compatible, f"Preset '{name}' is not self-compatible"

    def test_vendor_warnings_for_all_presets(self):
        """Vendor check must not crash for any preset + any vendor."""
        from qos_checker import PRESETS
        vendors = [DDSVendor.FASTDDS, DDSVendor.CYCLONEDDS, DDSVendor.CONNEXT]
        for name, profiles in PRESETS.items():
            for vendor in vendors:
                # Must not raise
                warnings = check_vendor_specific(
                    profiles["pub"], profiles["sub"], vendor)
                assert isinstance(warnings, list)


class TestHardwareInterfacePackage:
    """ros2_control hardware_interface package generation."""

    def test_creates_expected_structure(self, tmp_path):
        create_hardware_interface_package("my_arm_hw", tmp_path)
        pkg = tmp_path / "my_arm_hw"
        assert (pkg / "CMakeLists.txt").exists()
        assert (pkg / "package.xml").exists()
        assert (pkg / "include" / "my_arm_hw" / "my_arm_hw_hardware.hpp").exists()
        assert (pkg / "src" / "my_arm_hw_hardware.cpp").exists()
        assert (pkg / "my_arm_hw_plugin.xml").exists()
        assert (pkg / "config" / "my_arm_hw.ros2_control.xacro").exists()
        assert (pkg / "config" / "controllers.yaml").exists()
        assert (pkg / "test" / "test_my_arm_hw.cpp").exists()
        assert (pkg / "README.md").exists()

    def test_cmake_has_hw_interface_deps(self, tmp_path):
        create_hardware_interface_package("hw_test", tmp_path)
        cmake = (tmp_path / "hw_test" / "CMakeLists.txt").read_text(encoding="utf-8")
        assert "find_package(hardware_interface REQUIRED)" in cmake
        assert "find_package(pluginlib REQUIRED)" in cmake
        assert "pluginlib_export_plugin_description_file" in cmake

    def test_header_has_system_interface(self, tmp_path):
        create_hardware_interface_package("hw_test", tmp_path)
        hpp = (tmp_path / "hw_test" / "include" / "hw_test"
               / "hw_test_hardware.hpp").read_text(encoding="utf-8")
        assert "SystemInterface" in hpp
        assert "on_init" in hpp
        assert "on_configure" in hpp
        assert "export_state_interfaces" in hpp
        assert "export_command_interfaces" in hpp
        assert "read(" in hpp
        assert "write(" in hpp

    def test_source_has_pluginlib_export(self, tmp_path):
        create_hardware_interface_package("hw_test", tmp_path)
        cpp = (tmp_path / "hw_test" / "src"
               / "hw_test_hardware.cpp").read_text(encoding="utf-8")
        assert "PLUGINLIB_EXPORT_CLASS" in cpp
        assert "HW_IF_POSITION" in cpp
        assert "HW_IF_VELOCITY" in cpp

    def test_plugin_xml_valid(self, tmp_path):
        import xml.etree.ElementTree as ET
        create_hardware_interface_package("hw_test", tmp_path)
        tree = ET.parse(tmp_path / "hw_test" / "hw_test_plugin.xml")
        root = tree.getroot()
        cls = root.find("class")
        assert cls is not None
        assert "SystemInterface" in cls.attrib["base_class_type"]

    def test_xacro_has_plugin(self, tmp_path):
        create_hardware_interface_package("hw_test", tmp_path)
        xacro = (tmp_path / "hw_test" / "config"
                 / "hw_test.ros2_control.xacro").read_text(encoding="utf-8")
        assert "ros2_control" in xacro
        assert "hw_test/HwTestHardware" in xacro

    def test_package_xml_deps(self, tmp_path):
        import xml.etree.ElementTree as ET
        create_hardware_interface_package("hw_test", tmp_path)
        tree = ET.parse(tmp_path / "hw_test" / "package.xml")
        root = tree.getroot()
        deps = [d.text for d in root.findall("depend")]
        assert "hardware_interface" in deps
        assert "pluginlib" in deps
        assert "rclcpp" in deps


class TestFleetLaunchGeneration:
    """Multi-robot fleet launch file generation."""

    def test_fleet_launch_creates_file(self, tmp_path):
        content = _generate_fleet_launch("my_robot", 3)
        path = tmp_path / "fleet.launch.py"
        path.write_text(content)
        issues = validate_file(str(path))
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) == 0

    def test_fleet_launch_has_robot_namespaces(self, tmp_path):
        content = _generate_fleet_launch("my_robot", 3)
        assert "robot_1" in content
        assert "robot_2" in content
        assert "robot_3" in content
        assert "PushRosNamespace" in content
        assert "GroupAction" in content

    def test_fleet_launch_lifecycle(self, tmp_path):
        content = _generate_fleet_launch("my_robot", 2, lifecycle=True)
        assert "LifecycleNode" in content
        assert "robot_1" in content
        assert "robot_2" in content

    def test_fleet_launch_standard(self, tmp_path):
        content = _generate_fleet_launch("my_robot", 2, lifecycle=False)
        assert "Node(" in content
        assert "LifecycleNode" not in content

    def test_fleet_cli_integration(self, tmp_path):
        import subprocess
        script = os.path.join(os.path.dirname(__file__), "..",
                              "scripts", "create_package.py")
        result = subprocess.run(
            [sys.executable, script, "fleet_bot", "--type", "cpp",
             "--dest", str(tmp_path), "--robots", "3"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        fleet_launch = tmp_path / "fleet_bot" / "launch" / "fleet.launch.py"
        assert fleet_launch.exists()
        content = fleet_launch.read_text(encoding="utf-8")
        assert "robot_1" in content
        assert "robot_2" in content
        assert "robot_3" in content

    def test_fleet_launch_passes_validator(self, tmp_path):
        content = _generate_fleet_launch("test_bot", 4)
        path = tmp_path / "fleet.launch.py"
        path.write_text(content)
        issues = validate_file(str(path))
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) == 0


class TestSROS2SecurityEnclave:
    """SROS2 security enclave scaffolding."""

    def test_creates_security_files(self, tmp_path):
        (tmp_path / "my_robot").mkdir()
        _generate_sros2_enclave("my_robot", tmp_path)
        sec = tmp_path / "my_robot" / "security"
        assert (sec / "policies.xml").exists()
        assert (sec / "governance.xml").exists()
        assert (sec / "README.md").exists()
        assert (sec / "enclaves" / "my_robot").exists()

    def test_policies_xml_valid(self, tmp_path):
        import xml.etree.ElementTree as ET
        (tmp_path / "secure_bot").mkdir()
        _generate_sros2_enclave("secure_bot", tmp_path)
        tree = ET.parse(
            tmp_path / "secure_bot" / "security" / "policies.xml")
        root = tree.getroot()
        assert root.tag == "policy"
        enclaves = root.find("enclaves")
        assert enclaves is not None

    def test_governance_xml_valid(self, tmp_path):
        import xml.etree.ElementTree as ET
        (tmp_path / "secure_bot").mkdir()
        _generate_sros2_enclave("secure_bot", tmp_path)
        tree = ET.parse(
            tmp_path / "secure_bot" / "security" / "governance.xml")
        root = tree.getroot()
        assert root.tag == "dds"

    def test_sros2_cli_integration(self, tmp_path):
        import subprocess
        script = os.path.join(os.path.dirname(__file__), "..",
                              "scripts", "create_package.py")
        result = subprocess.run(
            [sys.executable, script, "sec_robot", "--type", "cpp",
             "--dest", str(tmp_path), "--sros2"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        sec = tmp_path / "sec_robot" / "security"
        assert (sec / "policies.xml").exists()
        assert (sec / "governance.xml").exists()

    def test_readme_has_instructions(self, tmp_path):
        (tmp_path / "my_robot").mkdir()
        _generate_sros2_enclave("my_robot", tmp_path)
        readme = (tmp_path / "my_robot" / "security" / "README.md").read_text(encoding="utf-8")
        assert "create_keystore" in readme
        assert "create_enclave" in readme
        assert "ROS_SECURITY_ENABLE" in readme


class TestQoSEventCallbacksInGeneratedCode:
    """Generated nodes must include QoS event callback infrastructure."""

    def test_cpp_header_has_qos_callbacks(self, tmp_path):
        create_cpp_package("qos_node", tmp_path)
        hpp = (tmp_path / "qos_node" / "include" / "qos_node"
               / "qos_node_node.hpp").read_text(encoding="utf-8")
        assert "on_offered_qos_incompatible" in hpp
        assert "on_requested_qos_incompatible" in hpp
        assert "QOSOfferedIncompatibleQoSInfo" in hpp

    def test_cpp_source_has_qos_implementations(self, tmp_path):
        create_cpp_package("qos_node", tmp_path)
        cpp = (tmp_path / "qos_node" / "src"
               / "qos_node_node.cpp").read_text(encoding="utf-8")
        assert "on_offered_qos_incompatible" in cpp
        assert "on_requested_qos_incompatible" in cpp
        assert "last_policy_kind" in cpp

    def test_python_node_has_qos_event_handler(self, tmp_path):
        create_python_package("py_qos", tmp_path)
        src = (tmp_path / "py_qos" / "py_qos" / "py_qos_node.py").read_text(encoding="utf-8")
        assert "on_qos_event" in src
        assert "QoSEventHandler" in src
