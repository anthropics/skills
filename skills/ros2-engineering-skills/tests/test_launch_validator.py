"""Tests for launch_validator.py - ROS 2 launch file static analysis."""

import os
import subprocess
import sys

SCRIPT = os.path.join(os.path.dirname(__file__), "..", "scripts", "launch_validator.py")

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
from launch_validator import validate_file, validate_directory, check_raw_patterns, Issue


def run_script(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, SCRIPT, *args],
        capture_output=True, text=True,
    )


def write_launch_file(tmp_path, name: str, content: str) -> str:
    filepath = tmp_path / name
    filepath.write_text(content)
    return str(filepath)


VALID_LAUNCH = """from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        Node(
            package='my_robot',
            executable='my_node',
            name='my_node',
            output='screen',
        ),
    ])
"""

MISSING_GENERATE = """from launch import LaunchDescription
from launch_ros.actions import Node

def some_other_function():
    return LaunchDescription([])
"""

MISSING_PACKAGE = """from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        Node(
            executable='my_node',
            name='my_node',
        ),
    ])
"""

DUPLICATE_NODES = """from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        Node(package='a', executable='n1', name='my_node', output='screen'),
        Node(package='b', executable='n2', name='my_node', output='screen'),
    ])
"""

DEPRECATED_KEYWORDS = """from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        Node(
            package='my_robot',
            node_executable='my_node',
            node_name='my_node',
            node_namespace='/ns',
        ),
    ])
"""

HARDCODED_PATH = """from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    config = '/home/user/catkin_ws/config/params.yaml'
    return LaunchDescription([
        Node(
            package='my_robot',
            executable='my_node',
            name='my_node',
            parameters=[config],
            output='screen',
        ),
    ])
"""

WITH_SLEEP = """from launch import LaunchDescription
from launch_ros.actions import Node
import time

def generate_launch_description():
    time.sleep(2)
    return LaunchDescription([
        Node(package='a', executable='n', name='n', output='screen'),
    ])
"""

WITH_SUPPRESSION = """from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        Node(  # noqa
            executable='my_node',
            name='my_node',
        ),
    ])
"""

COMPOSABLE_MISSING_PLUGIN = """from launch import LaunchDescription
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
                    name='my_node',
                ),
            ],
            output='screen',
        ),
    ])
"""

MISSING_OUTPUT = """from launch import LaunchDescription
from launch_ros.actions import Node

def generate_launch_description():
    return LaunchDescription([
        Node(
            package='my_robot',
            executable='my_node',
            name='my_node',
        ),
    ])
"""

DECLARE_ARG_NO_DESC = """from launch import LaunchDescription
from launch.actions import DeclareLaunchArgument

def generate_launch_description():
    return LaunchDescription([
        DeclareLaunchArgument('use_sim_time'),
    ])
"""

SYNTAX_ERROR_LAUNCH = """from launch import LaunchDescription

def generate_launch_description(
    # Missing closing paren
"""


class TestValidateFile:
    def test_valid_file_no_errors(self, tmp_path):
        path = write_launch_file(tmp_path, "good.launch.py", VALID_LAUNCH)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) == 0

    def test_missing_generate_function(self, tmp_path):
        path = write_launch_file(tmp_path, "bad.launch.py", MISSING_GENERATE)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("generate_launch_description" in i.message for i in errors)

    def test_missing_package_arg(self, tmp_path):
        path = write_launch_file(tmp_path, "bad.launch.py", MISSING_PACKAGE)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("package" in i.message for i in errors)

    def test_duplicate_node_names(self, tmp_path):
        path = write_launch_file(tmp_path, "dup.launch.py", DUPLICATE_NODES)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("Duplicate" in i.message for i in errors)

    def test_deprecated_keywords_warned(self, tmp_path):
        path = write_launch_file(tmp_path, "dep.launch.py", DEPRECATED_KEYWORDS)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("deprecated" in i.message.lower() for i in warnings)

    def test_hardcoded_path_warned(self, tmp_path):
        path = write_launch_file(tmp_path, "hard.launch.py", HARDCODED_PATH)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("Hardcoded" in i.message for i in warnings)

    def test_sleep_warned(self, tmp_path):
        path = write_launch_file(tmp_path, "sleep.launch.py", WITH_SLEEP)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("sleep" in i.message for i in warnings)

    def test_suppression_respected(self, tmp_path):
        path = write_launch_file(tmp_path, "sup.launch.py", WITH_SUPPRESSION)
        issues = validate_file(path)
        # The Node() missing 'package' error on the suppressed line should be gone
        errors = [i for i in issues if i.severity == "error" and "package" in i.message.lower()]
        assert len(errors) == 0

    def test_composable_missing_plugin(self, tmp_path):
        path = write_launch_file(tmp_path, "comp.launch.py", COMPOSABLE_MISSING_PLUGIN)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("plugin" in i.message.lower() for i in errors)

    def test_missing_output_info(self, tmp_path):
        path = write_launch_file(tmp_path, "out.launch.py", MISSING_OUTPUT)
        issues = validate_file(path)
        infos = [i for i in issues if i.severity == "info"]
        assert any("output" in i.message.lower() for i in infos)

    def test_declare_arg_no_description(self, tmp_path):
        path = write_launch_file(tmp_path, "arg.launch.py", DECLARE_ARG_NO_DESC)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("description" in i.message.lower() for i in warnings)

    def test_syntax_error_reported(self, tmp_path):
        path = write_launch_file(tmp_path, "syn.launch.py", SYNTAX_ERROR_LAUNCH)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("yntax" in i.message for i in errors)

    def test_nonexistent_file(self):
        issues = validate_file("/nonexistent/file.launch.py")
        errors = [i for i in issues if i.severity == "error"]
        assert len(errors) > 0


class TestValidateDirectory:
    def test_finds_launch_files(self, tmp_path):
        write_launch_file(tmp_path, "a.launch.py", VALID_LAUNCH)
        write_launch_file(tmp_path, "b.launch.py", VALID_LAUNCH)
        result = validate_directory(str(tmp_path))
        assert result.files_checked == 2

    def test_ignores_non_launch_files(self, tmp_path):
        write_launch_file(tmp_path, "a.launch.py", VALID_LAUNCH)
        (tmp_path / "not_a_launch.py").write_text("print('hello')")
        result = validate_directory(str(tmp_path))
        assert result.files_checked == 1

    def test_empty_directory(self, tmp_path):
        result = validate_directory(str(tmp_path))
        assert result.files_checked == 0


class TestCheckRawPatterns:
    def test_detects_os_system(self):
        source = "os.system('roslaunch ...')"
        issues = check_raw_patterns("test.py", source)
        assert any("Shell command" in i.message for i in issues)

    def test_detects_subprocess(self):
        source = "subprocess.run(['ros2', 'run'])"
        issues = check_raw_patterns("test.py", source)
        assert any("Shell command" in i.message for i in issues)

    def test_suppression_in_raw_patterns(self):
        source = "os.system('something')  # noqa"
        issues = check_raw_patterns("test.py", source)
        assert len(issues) == 0


class TestCLI:
    def test_valid_file(self, tmp_path):
        path = write_launch_file(tmp_path, "good.launch.py", VALID_LAUNCH)
        result = run_script(path)
        assert result.returncode == 0
        assert "Checked 1" in result.stdout

    def test_errors_return_nonzero(self, tmp_path):
        path = write_launch_file(tmp_path, "bad.launch.py", MISSING_GENERATE)
        result = run_script(path)
        assert result.returncode != 0

    def test_severity_filter(self, tmp_path):
        path = write_launch_file(tmp_path, "info.launch.py", MISSING_OUTPUT)
        # With --severity error, info-level "missing output" should not appear
        result = run_script(path, "--severity", "error")
        assert result.returncode == 0

    def test_nonexistent_path(self):
        result = run_script("/nonexistent/path")
        assert result.returncode != 0

    def test_directory_scan(self, tmp_path):
        write_launch_file(tmp_path, "a.launch.py", VALID_LAUNCH)
        write_launch_file(tmp_path, "b.launch.py", VALID_LAUNCH)
        result = run_script(str(tmp_path))
        assert "Checked 2" in result.stdout


EXECUTE_PROCESS_MISSING_CMD = """from launch import LaunchDescription
from launch.actions import ExecuteProcess

def generate_launch_description():
    return LaunchDescription([
        ExecuteProcess(),
    ])
"""

INCLUDE_LAUNCH_RELATIVE = """from launch import LaunchDescription
from launch.actions import IncludeLaunchDescription
from launch.launch_description_sources import PythonLaunchDescriptionSource

def generate_launch_description():
    return LaunchDescription([
        IncludeLaunchDescription(
            PythonLaunchDescriptionSource('nonexistent.launch.py')
        ),
    ])
"""

INCLUDE_LAUNCH_ABS = """from launch import LaunchDescription
from launch.actions import IncludeLaunchDescription

def generate_launch_description():
    return LaunchDescription([
        IncludeLaunchDescription('/nonexistent/path.launch.py'),
    ])
"""

COMPOSABLE_CONTAINER_MISSING_PKG = """from launch import LaunchDescription
from launch_ros.actions import ComposableNodeContainer

def generate_launch_description():
    return LaunchDescription([
        ComposableNodeContainer(
            name='container',
            namespace='',
            executable='component_container',
        ),
    ])
"""


class TestMainFunction:
    """Test main() directly for coverage."""

    def test_main_valid_file(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from launch_validator import main
        path = write_launch_file(tmp_path, "good.launch.py", VALID_LAUNCH)
        monkeypatch.setattr(
            "sys.argv", ["launch_validator.py", path])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_error_file(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from launch_validator import main
        path = write_launch_file(tmp_path, "bad.launch.py", MISSING_GENERATE)
        monkeypatch.setattr(
            "sys.argv", ["launch_validator.py", path])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1

    def test_main_directory(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from launch_validator import main
        write_launch_file(tmp_path, "a.launch.py", VALID_LAUNCH)
        monkeypatch.setattr(
            "sys.argv", ["launch_validator.py", str(tmp_path)])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_severity_filter(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from launch_validator import main
        path = write_launch_file(tmp_path, "info.launch.py", MISSING_OUTPUT)
        monkeypatch.setattr(
            "sys.argv",
            ["launch_validator.py", path, "--severity", "error"])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_nonexistent(self, monkeypatch):
        import pytest as _pytest
        from launch_validator import main
        monkeypatch.setattr(
            "sys.argv", ["launch_validator.py", "/nonexistent/path"])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1

    def test_main_empty_directory(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from launch_validator import main
        monkeypatch.setattr(
            "sys.argv", ["launch_validator.py", str(tmp_path)])
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0


class TestAdditionalVisitors:
    """Test AST visitor paths not covered by main test constants."""

    def test_execute_process_missing_cmd(self, tmp_path):
        path = write_launch_file(tmp_path, "exec.launch.py",
                                 EXECUTE_PROCESS_MISSING_CMD)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("cmd" in i.message.lower() for i in errors)

    def test_include_launch_relative_missing(self, tmp_path):
        path = write_launch_file(tmp_path, "inc.launch.py",
                                 INCLUDE_LAUNCH_RELATIVE)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("not found" in i.message for i in warnings)

    def test_include_launch_abs_missing(self, tmp_path):
        path = write_launch_file(tmp_path, "inc_abs.launch.py",
                                 INCLUDE_LAUNCH_ABS)
        issues = validate_file(path)
        warnings = [i for i in issues if i.severity == "warning"]
        assert any("not found" in i.message for i in warnings)

    def test_composable_container_missing_package(self, tmp_path):
        path = write_launch_file(tmp_path, "cont.launch.py",
                                 COMPOSABLE_CONTAINER_MISSING_PKG)
        issues = validate_file(path)
        errors = [i for i in issues if i.severity == "error"]
        assert any("package" in i.message.lower() for i in errors)

    def test_validation_result_counts(self, tmp_path):
        from launch_validator import ValidationResult
        result = ValidationResult()
        result.issues.append(
            Issue("test.py", 1, "error", "err"))
        result.issues.append(
            Issue("test.py", 2, "warning", "warn"))
        result.issues.append(
            Issue("test.py", 3, "info", "info"))
        assert result.error_count == 1
        assert result.warning_count == 1

    def test_suppression_out_of_range_line(self):
        from launch_validator import _line_has_suppression
        assert _line_has_suppression("hello\nworld", 0) is False
        assert _line_has_suppression("hello\nworld", 5) is False


class TestVersion:
    def test_version_flag(self):
        result = run_script("--version")
        assert result.returncode == 0
        assert "0.1.0" in result.stdout


class TestIssueDisplay:
    def test_issue_str_format(self):
        issue = Issue("test.launch.py", 10, "error", "something wrong")
        s = str(issue)
        assert "ERROR" in s
        assert "test.launch.py:10" in s
        assert "something wrong" in s
