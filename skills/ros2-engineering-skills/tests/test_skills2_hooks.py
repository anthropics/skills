"""Tests for Skills 2.0 hook scripts — validates hook execution and output.

These tests ensure:
1. Hook scripts are executable and produce valid JSON output
2. Stop hook correctly validates ROS 2 artifacts
3. PreToolUse hook detects anti-patterns
4. Hooks return correct exit codes
"""

import json
import os
import subprocess
import sys

SCRIPTS_DIR = os.path.join(os.path.dirname(__file__), '..', 'scripts')

sys.path.insert(0, SCRIPTS_DIR)
from skill_stop_hook import (
    find_generated_launch_files,
    validate_launch_file_syntax,
    validate_package_xml,
    find_package_xmls,
)
from skill_validate_hook import (
    check_content,
    check_file,
    _check_dangerous_commands,
    ANTIPATTERN_CHECKS,
    CHECKABLE_EXTENSIONS,
    DANGEROUS_COMMAND_PATTERNS,
)


class TestStopHookLaunchValidation:
    """Test the stop hook's launch file validation."""

    def test_valid_launch_file(self, tmp_path):
        launch = tmp_path / 'test.launch.py'
        launch.write_text(
            'from launch import LaunchDescription\n'
            'def generate_launch_description():\n'
            '    return LaunchDescription([])\n'
        )
        issues = validate_launch_file_syntax(str(launch))
        assert len(issues) == 0

    def test_missing_generate_function(self, tmp_path):
        launch = tmp_path / 'bad.launch.py'
        launch.write_text(
            'from launch import LaunchDescription\n'
            'def create_nodes():\n'
            '    return LaunchDescription([])\n'
        )
        issues = validate_launch_file_syntax(str(launch))
        assert len(issues) == 1
        assert issues[0]['severity'] == 'error'
        assert 'generate_launch_description' in issues[0]['message']

    def test_syntax_error(self, tmp_path):
        launch = tmp_path / 'syntax.launch.py'
        launch.write_text('def broken(\n')
        issues = validate_launch_file_syntax(str(launch))
        assert len(issues) == 1
        assert issues[0]['severity'] == 'error'
        assert 'yntax' in issues[0]['message']

    def test_nonexistent_file(self):
        issues = validate_launch_file_syntax('/nonexistent/file.launch.py')
        assert len(issues) == 0  # File read errors are silently skipped

    def test_find_launch_files(self, tmp_path):
        launch_dir = tmp_path / 'pkg' / 'launch'
        launch_dir.mkdir(parents=True)
        (launch_dir / 'a.launch.py').write_text('# launch')
        (launch_dir / 'b.launch.py').write_text('# launch')
        (tmp_path / 'not_launch.py').write_text('# not a launch')
        files = find_generated_launch_files(str(tmp_path))
        assert len(files) == 2

    def test_find_launch_files_skips_hidden(self, tmp_path):
        hidden = tmp_path / '.hidden' / 'launch'
        hidden.mkdir(parents=True)
        (hidden / 'skip.launch.py').write_text('# skip')
        files = find_generated_launch_files(str(tmp_path))
        assert len(files) == 0

    def test_find_launch_files_skips_build(self, tmp_path):
        build = tmp_path / 'build' / 'pkg' / 'launch'
        build.mkdir(parents=True)
        (build / 'skip.launch.py').write_text('# skip')
        files = find_generated_launch_files(str(tmp_path))
        assert len(files) == 0


class TestStopHookPackageXmlValidation:
    """Test the stop hook's package.xml validation."""

    def test_valid_package_xml(self, tmp_path):
        pkg_xml = tmp_path / 'package.xml'
        pkg_xml.write_text(
            '<?xml version="1.0"?>\n'
            '<package format="3">\n'
            '  <name>test_pkg</name>\n'
            '  <version>0.1.0</version>\n'
            '  <description>Test</description>\n'
            '  <maintainer email="a@b.c">Test</maintainer>\n'
            '  <license>Apache-2.0</license>\n'
            '</package>\n'
        )
        issues = validate_package_xml(str(pkg_xml))
        assert len(issues) == 0

    def test_old_format_warns(self, tmp_path):
        pkg_xml = tmp_path / 'package.xml'
        pkg_xml.write_text(
            '<?xml version="1.0"?>\n'
            '<package format="2">\n'
            '  <name>test_pkg</name>\n'
            '  <license>Apache-2.0</license>\n'
            '</package>\n'
        )
        issues = validate_package_xml(str(pkg_xml))
        warnings = [i for i in issues if i['severity'] == 'warning']
        assert any('format' in i['message'] for i in warnings)

    def test_missing_name_errors(self, tmp_path):
        pkg_xml = tmp_path / 'package.xml'
        pkg_xml.write_text(
            '<?xml version="1.0"?>\n'
            '<package format="3">\n'
            '  <license>Apache-2.0</license>\n'
            '</package>\n'
        )
        issues = validate_package_xml(str(pkg_xml))
        errors = [i for i in issues if i['severity'] == 'error']
        assert any('name' in i['message'] for i in errors)

    def test_missing_license_warns(self, tmp_path):
        pkg_xml = tmp_path / 'package.xml'
        pkg_xml.write_text(
            '<?xml version="1.0"?>\n'
            '<package format="3">\n'
            '  <name>test_pkg</name>\n'
            '</package>\n'
        )
        issues = validate_package_xml(str(pkg_xml))
        warnings = [i for i in issues if i['severity'] == 'warning']
        assert any('license' in i['message'] for i in warnings)

    def test_invalid_xml_errors(self, tmp_path):
        pkg_xml = tmp_path / 'package.xml'
        pkg_xml.write_text('not xml at all')
        issues = validate_package_xml(str(pkg_xml))
        assert any(i['severity'] == 'error' for i in issues)

    def test_find_package_xmls(self, tmp_path):
        (tmp_path / 'pkg_a').mkdir()
        (tmp_path / 'pkg_a' / 'package.xml').write_text('<package/>')
        (tmp_path / 'pkg_b').mkdir()
        (tmp_path / 'pkg_b' / 'package.xml').write_text('<package/>')
        files = find_package_xmls(str(tmp_path))
        assert len(files) == 2

    def test_find_package_xmls_skips_build(self, tmp_path):
        build = tmp_path / 'build' / 'pkg'
        build.mkdir(parents=True)
        (build / 'package.xml').write_text('<package/>')
        files = find_package_xmls(str(tmp_path))
        assert len(files) == 0


class TestStopHookCLI:
    """Test the stop hook as a CLI command."""

    def test_clean_workspace_passes(self, tmp_path):
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_stop_hook.py')],
            capture_output=True, text=True,
            env={**os.environ, 'SKILL_WORKSPACE': str(tmp_path)},
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data['status'] == 'pass'
        assert data['issues_count'] == 0

    def test_workspace_with_valid_artifacts(self, tmp_path):
        (tmp_path / 'launch').mkdir()
        (tmp_path / 'launch' / 'test.launch.py').write_text(
            'from launch import LaunchDescription\n'
            'def generate_launch_description():\n'
            '    return LaunchDescription([])\n'
        )
        (tmp_path / 'package.xml').write_text(
            '<?xml version="1.0"?>\n'
            '<package format="3">\n'
            '  <name>test</name>\n'
            '  <license>Apache-2.0</license>\n'
            '</package>\n'
        )
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_stop_hook.py')],
            capture_output=True, text=True,
            env={**os.environ, 'SKILL_WORKSPACE': str(tmp_path)},
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data['status'] == 'pass'

    def test_workspace_with_errors_fails(self, tmp_path):
        (tmp_path / 'launch').mkdir()
        (tmp_path / 'launch' / 'bad.launch.py').write_text(
            'from launch import LaunchDescription\n'
            'def wrong_name():\n'
            '    return LaunchDescription([])\n'
        )
        (tmp_path / 'package.xml').write_text(
            '<?xml version="1.0"?>\n'
            '<package format="3">\n'
            '  <license>Apache-2.0</license>\n'
            '</package>\n'
        )
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_stop_hook.py')],
            capture_output=True, text=True,
            env={**os.environ, 'SKILL_WORKSPACE': str(tmp_path)},
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data['status'] == 'fail'
        assert data['issues_count'] >= 1

    def test_output_is_valid_json(self, tmp_path):
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_stop_hook.py')],
            capture_output=True, text=True,
            env={**os.environ, 'SKILL_WORKSPACE': str(tmp_path)},
        )
        data = json.loads(result.stdout)
        assert 'hook' in data
        assert 'version' in data
        assert 'issues_count' in data
        assert 'issues' in data
        assert 'status' in data


class TestValidateHookAntiPatterns:
    """Test the PreToolUse hook's anti-pattern detection."""

    def test_detects_time_sleep(self):
        issues = check_content('time.sleep(5)', 'test.py')
        assert len(issues) >= 1
        assert any('sleep' in i['message'] for i in issues)

    def test_detects_spin_until_future_complete(self):
        issues = check_content(
            'rclpy.spin_until_future_complete(node, future)', 'test.py')
        assert len(issues) >= 1
        assert any('spin_until_future_complete' in i['message'] for i in issues)

    def test_detects_global_variables(self):
        issues = check_content('global node_state', 'test.py')
        assert len(issues) >= 1
        assert any('Global' in i['message'] for i in issues)

    def test_detects_ros_localhost_only(self):
        issues = check_content(
            'os.environ["ROS_LOCALHOST_ONLY"] = "1"', 'test.py')
        assert len(issues) >= 1
        assert any('ROS_LOCALHOST_ONLY' in i['message'] for i in issues)

    def test_detects_deprecated_node_executable(self):
        issues = check_content(
            'Node(node_executable="my_node")', 'test.py')
        assert len(issues) >= 1
        assert any('deprecated' in i['message'] for i in issues)

    def test_detects_deprecated_node_name(self):
        issues = check_content(
            'Node(node_name="my_node")', 'test.py')
        assert len(issues) >= 1
        assert any('deprecated' in i['message'] for i in issues)

    def test_detects_deprecated_node_namespace(self):
        issues = check_content(
            'Node(node_namespace="/ns")', 'test.py')
        assert len(issues) >= 1
        assert any('deprecated' in i['message'] for i in issues)

    def test_clean_code_no_issues(self):
        clean_code = (
            'import rclpy\n'
            'class MyNode(Node):\n'
            '    def __init__(self):\n'
            '        super().__init__("my_node")\n'
        )
        issues = check_content(clean_code, 'test.py')
        assert len(issues) == 0

    def test_check_file_returns_empty_for_non_checkable(self, tmp_path):
        f = tmp_path / 'test.yaml'
        f.write_text('key: value')
        issues = check_file(str(f))
        assert len(issues) == 0

    def test_check_file_checks_python(self, tmp_path):
        f = tmp_path / 'test.py'
        f.write_text('time.sleep(1)')
        issues = check_file(str(f))
        assert len(issues) >= 1

    def test_check_file_checks_cpp(self, tmp_path):
        f = tmp_path / 'test.cpp'
        f.write_text('// clean C++ code\n')
        issues = check_file(str(f))
        assert len(issues) == 0

    def test_check_file_nonexistent(self):
        issues = check_file('/nonexistent/file.py')
        assert len(issues) == 0

    def test_antipattern_checks_non_empty(self):
        assert len(ANTIPATTERN_CHECKS) >= 5

    def test_checkable_extensions(self):
        assert '.py' in CHECKABLE_EXTENSIONS
        assert '.cpp' in CHECKABLE_EXTENSIONS
        assert '.hpp' in CHECKABLE_EXTENSIONS


class TestDangerousCommandDetection:
    """Test dangerous command detection in the PreToolUse hook."""

    def test_rm_rf_root(self):
        issues = _check_dangerous_commands('rm -rf /')
        assert len(issues) >= 1
        assert any('root' in i['message'].lower() for i in issues)

    def test_rm_rf_root_star(self):
        issues = _check_dangerous_commands('rm -rf /*')
        assert len(issues) >= 1

    def test_rm_rf_opt_ros(self):
        issues = _check_dangerous_commands('rm -rf /opt/ros')
        assert len(issues) >= 1
        assert any('ROS' in i['message'] for i in issues)

    def test_rm_rf_system_dirs(self):
        for d in ['/usr', '/bin', '/etc', '/var', '/boot', '/lib']:
            issues = _check_dangerous_commands(f'rm -rf {d}')
            assert len(issues) >= 1, f"Should detect rm -rf {d}"

    def test_rm_rf_home(self):
        issues = _check_dangerous_commands('rm -rf ~')
        assert len(issues) >= 1

    def test_mkfs_detected(self):
        issues = _check_dangerous_commands('mkfs.ext4 /dev/sda1')
        assert len(issues) >= 1
        assert any('mkfs' in i['message'] for i in issues)

    def test_dd_to_disk(self):
        issues = _check_dangerous_commands('dd if=/dev/zero of=/dev/sda')
        assert len(issues) >= 1
        assert any('dd' in i['message'].lower() for i in issues)

    def test_chmod_777_root(self):
        issues = _check_dangerous_commands('chmod -R 777 /')
        assert len(issues) >= 1
        assert any('chmod' in i['message'] for i in issues)

    def test_safe_commands_pass(self):
        safe_commands = [
            'colcon build',
            'ros2 run demo_nodes_cpp talker',
            'rm -rf build/ install/ log/',
            'cat /etc/os-release',
        ]
        for cmd in safe_commands:
            issues = _check_dangerous_commands(cmd)
            assert len(issues) == 0, f"Safe command flagged: {cmd}"

    def test_dangerous_patterns_non_empty(self):
        assert len(DANGEROUS_COMMAND_PATTERNS) >= 5

    def test_rm_rf_root_cli(self):
        """Test via CLI that rm -rf / is blocked."""
        tool_input = json.dumps({'command': 'rm -rf /'})
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': 'Bash', 'TOOL_INPUT': tool_input},
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data['status'] == 'fail'


class TestValidateHookCLI:
    """Test the PreToolUse hook as a CLI command."""

    def test_no_input_passes(self):
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': '', 'TOOL_INPUT': ''},
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data['status'] == 'pass'

    def test_write_clean_code_passes(self):
        tool_input = json.dumps({
            'file_path': 'test.py',
            'content': 'import rclpy\nclass MyNode: pass\n',
        })
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': 'Write', 'TOOL_INPUT': tool_input},
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data['status'] == 'pass'

    def test_write_antipattern_warns(self):
        tool_input = json.dumps({
            'file_path': 'test.py',
            'content': 'time.sleep(5)\n',
        })
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': 'Write', 'TOOL_INPUT': tool_input},
        )
        assert result.returncode == 0  # Warnings don't block
        data = json.loads(result.stdout)
        assert data['issues_count'] >= 1

    def test_dangerous_bash_command_fails(self):
        tool_input = json.dumps({
            'command': 'rm -rf /opt/ros',
        })
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': 'Bash', 'TOOL_INPUT': tool_input},
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data['status'] == 'fail'

    def test_output_is_valid_json(self):
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': '', 'TOOL_INPUT': ''},
        )
        data = json.loads(result.stdout)
        assert 'hook' in data
        assert 'version' in data
        assert 'issues_count' in data
        assert 'issues' in data
        assert 'status' in data

    def test_edit_tool_with_antipattern(self):
        tool_input = json.dumps({
            'file_path': 'test.py',
            'new_string': 'global node_state\n',
        })
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': 'Edit', 'TOOL_INPUT': tool_input},
        )
        assert result.returncode == 0  # Warnings don't block
        data = json.loads(result.stdout)
        assert data['issues_count'] >= 1

    def test_invalid_json_input_passes(self):
        result = subprocess.run(
            [sys.executable,
             os.path.join(SCRIPTS_DIR, 'skill_validate_hook.py')],
            capture_output=True, text=True,
            env={**os.environ,
                 'TOOL_NAME': 'Write', 'TOOL_INPUT': 'not json'},
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data['status'] == 'pass'


class TestStopHookMainDirect:
    """Test skill_stop_hook.main() directly for coverage."""

    def test_main_clean_workspace(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from skill_stop_hook import main
        monkeypatch.setenv('SKILL_WORKSPACE', str(tmp_path))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_with_valid_launch(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from skill_stop_hook import main
        (tmp_path / 'launch').mkdir()
        (tmp_path / 'launch' / 'ok.launch.py').write_text(
            'from launch import LaunchDescription\n'
            'def generate_launch_description():\n'
            '    return LaunchDescription([])\n'
        )
        monkeypatch.setenv('SKILL_WORKSPACE', str(tmp_path))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_with_error_launch(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from skill_stop_hook import main
        (tmp_path / 'launch').mkdir()
        (tmp_path / 'launch' / 'bad.launch.py').write_text(
            'from launch import LaunchDescription\n'
            'def wrong_name():\n'
            '    return LaunchDescription([])\n'
        )
        monkeypatch.setenv('SKILL_WORKSPACE', str(tmp_path))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1

    def test_main_with_package_xml(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from skill_stop_hook import main
        (tmp_path / 'package.xml').write_text(
            '<?xml version="1.0"?>\n'
            '<package format="3"><name>t</name>'
            '<license>Apache-2.0</license></package>\n'
        )
        monkeypatch.setenv('SKILL_WORKSPACE', str(tmp_path))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_missing_name_in_pkg_xml(self, tmp_path, monkeypatch):
        import pytest as _pytest
        from skill_stop_hook import main
        (tmp_path / 'package.xml').write_text(
            '<?xml version="1.0"?>\n'
            '<package format="3"><license>Apache-2.0</license></package>\n'
        )
        monkeypatch.setenv('SKILL_WORKSPACE', str(tmp_path))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1


class TestValidateHookMainDirect:
    """Test skill_validate_hook.main() directly for coverage."""

    def test_main_no_input(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', '')
        monkeypatch.setenv('TOOL_INPUT', '')
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_write_clean(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Write')
        monkeypatch.setenv('TOOL_INPUT', json.dumps({
            'file_path': 'test.py',
            'content': 'import rclpy\n',
        }))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_write_antipattern(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Write')
        monkeypatch.setenv('TOOL_INPUT', json.dumps({
            'file_path': 'test.py',
            'content': 'time.sleep(5)\n',
        }))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0  # Warnings don't block

    def test_main_edit_antipattern(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Edit')
        monkeypatch.setenv('TOOL_INPUT', json.dumps({
            'file_path': 'test.py',
            'new_string': 'global node_ref\n',
        }))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_bash_dangerous(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Bash')
        monkeypatch.setenv('TOOL_INPUT', json.dumps({
            'command': 'rm -rf /opt/ros',
        }))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1

    def test_main_bash_safe(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Bash')
        monkeypatch.setenv('TOOL_INPUT', json.dumps({
            'command': 'colcon build',
        }))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_bash_invalid_json(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Bash')
        monkeypatch.setenv('TOOL_INPUT', 'not json')
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_write_no_content(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Write')
        monkeypatch.setenv('TOOL_INPUT', json.dumps({
            'file_path': 'test.py',
        }))
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_invalid_json_write(self, monkeypatch):
        import pytest as _pytest
        from skill_validate_hook import main
        monkeypatch.setenv('TOOL_NAME', 'Write')
        monkeypatch.setenv('TOOL_INPUT', '{bad json')
        with _pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0
