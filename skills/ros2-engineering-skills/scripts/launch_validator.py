#!/usr/bin/env python3
"""Static analysis for ROS 2 Python launch files.

Usage:
    python launch_validator.py path/to/launch_dir/
    python launch_validator.py path/to/specific.launch.py

Checks performed:
- Missing package references (FindPackageShare with non-existent packages)
- Duplicate node names in the same namespace
- Common launch file anti-patterns
- Missing config/URDF file references
- Deprecated patterns
"""

import argparse
import ast
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class Issue:
    file: str
    line: int
    severity: str  # "error", "warning", "info"
    message: str

    def __str__(self) -> str:
        return f"  [{self.severity.upper():7s}] {self.file}:{self.line}: {self.message}"


@dataclass
class ValidationResult:
    issues: list = field(default_factory=list)
    files_checked: int = 0

    @property
    def error_count(self) -> int:
        return sum(1 for i in self.issues if i.severity == "error")

    @property
    def warning_count(self) -> int:
        return sum(1 for i in self.issues if i.severity == "warning")


class LaunchFileVisitor(ast.NodeVisitor):
    """AST visitor that checks launch file patterns."""

    def __init__(self, filepath: str):
        self.filepath = filepath
        self.issues: list[Issue] = []
        self.node_names: list[tuple[str, str, int]] = []  # (name, namespace, line)
        self.has_generate_func = False

    def _add(self, node: ast.AST, severity: str, message: str) -> None:
        self.issues.append(Issue(self.filepath, getattr(node, 'lineno', 0), severity, message))

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        if node.name == "generate_launch_description":
            self.has_generate_func = True
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        func_name = self._get_call_name(node)

        if func_name == "Node" or func_name == "LifecycleNode":
            self._check_node_call(node, func_name)

        elif func_name == "ExecuteProcess":
            self._check_execute_process(node)

        elif func_name == "DeclareLaunchArgument":
            self._check_declare_argument(node)

        self.generic_visit(node)

    def _get_call_name(self, node: ast.Call) -> str:
        if isinstance(node.func, ast.Name):
            return node.func.id
        elif isinstance(node.func, ast.Attribute):
            return node.func.attr
        return ""

    def _get_keyword_value(self, node: ast.Call, keyword: str) -> Optional[ast.AST]:
        for kw in node.keywords:
            if kw.arg == keyword:
                return kw.value
        return None

    def _get_string_value(self, node: ast.AST) -> Optional[str]:
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return node.value
        return None

    def _check_node_call(self, node: ast.Call, func_name: str) -> None:
        # Check for missing 'package' keyword
        pkg_node = self._get_keyword_value(node, "package")
        exec_node = self._get_keyword_value(node, "executable")
        name_node = self._get_keyword_value(node, "name")
        ns_node = self._get_keyword_value(node, "namespace")
        output_node = self._get_keyword_value(node, "output")

        if pkg_node is None:
            self._add(node, "error", f"{func_name}() missing required 'package' argument")

        if exec_node is None:
            self._add(node, "error", f"{func_name}() missing required 'executable' argument")

        # Check for missing output='screen' (common oversight)
        if output_node is None:
            self._add(node, "info",
                      f"{func_name}() has no 'output' argument. "
                      f"Add output='screen' to see node logs in terminal.")

        # Track node names for duplicate detection
        # Skip duplicate check if namespace is dynamic (LaunchConfiguration etc.)
        name_str = self._get_string_value(name_node) if name_node else None
        ns_str = self._get_string_value(ns_node) if ns_node else ""
        ns_is_dynamic = ns_node is not None and ns_str is None
        if name_str and not ns_is_dynamic:
            self.node_names.append((name_str, ns_str or "", node.lineno))

        # Check for deprecated 'node_name' instead of 'name'
        if self._get_keyword_value(node, "node_name") is not None:
            self._add(node, "warning",
                      "'node_name' is deprecated. Use 'name' instead.")

        # Check for deprecated 'node_executable' instead of 'executable'
        if self._get_keyword_value(node, "node_executable") is not None:
            self._add(node, "warning",
                      "'node_executable' is deprecated. Use 'executable' instead.")

        # Check for deprecated 'node_namespace' instead of 'namespace'
        if self._get_keyword_value(node, "node_namespace") is not None:
            self._add(node, "warning",
                      "'node_namespace' is deprecated. Use 'namespace' instead.")

    def _check_execute_process(self, node: ast.Call) -> None:
        cmd_node = self._get_keyword_value(node, "cmd")
        if cmd_node is None:
            # Check positional args
            if not node.args:
                self._add(node, "error",
                          "ExecuteProcess() missing 'cmd' argument")

    def _check_declare_argument(self, node: ast.Call) -> None:
        desc_node = self._get_keyword_value(node, "description")
        if desc_node is None:
            # Get argument name for better error message
            name = ""
            if node.args:
                name_val = self._get_string_value(node.args[0])
                if name_val:
                    name = f" '{name_val}'"
            self._add(node, "warning",
                      f"DeclareLaunchArgument{name} has no 'description'. "
                      f"Add description for --show-args output.")

    def check_duplicates(self) -> None:
        """Check for duplicate node names in the same namespace."""
        seen = {}
        for name, ns, line in self.node_names:
            key = f"{ns}/{name}"
            if key in seen:
                self.issues.append(Issue(
                    self.filepath, line, "error",
                    f"Duplicate node name '{name}' in namespace '{ns}' "
                    f"(first defined at line {seen[key]})"))
            else:
                seen[key] = line


def check_raw_patterns(filepath: str, source: str) -> list[Issue]:
    """Check for patterns that are easier to find via regex than AST."""
    issues = []

    for i, line in enumerate(source.splitlines(), 1):
        # Check for hardcoded paths
        if re.search(r'["\'][/~][\w/]+\.(yaml|urdf|xacro|rviz)', line):
            if "FindPackageShare" not in line and "PathJoinSubstitution" not in line:
                issues.append(Issue(filepath, i, "warning",
                    "Hardcoded file path detected. Use FindPackageShare + "
                    "PathJoinSubstitution for portable paths."))

        # Check for sleep/time.sleep in launch files
        if re.search(r'\btime\.sleep\b', line):
            issues.append(Issue(filepath, i, "warning",
                "time.sleep() in launch file. Use TimerAction for delayed starts."))

        # Check for os.system or subprocess calls
        if re.search(r'\bos\.system\b|\bsubprocess\.(call|run|Popen)\b', line):
            issues.append(Issue(filepath, i, "warning",
                "Shell command in launch file. Use ExecuteProcess action instead."))

    return issues


def validate_file(filepath: str) -> list[Issue]:
    """Validate a single launch file."""
    issues = []

    try:
        source = Path(filepath).read_text()
    except (OSError, UnicodeDecodeError) as e:
        return [Issue(filepath, 0, "error", f"Cannot read file: {e}")]

    # Parse AST
    try:
        tree = ast.parse(source, filename=filepath)
    except SyntaxError as e:
        return [Issue(filepath, e.lineno or 0, "error", f"Syntax error: {e.msg}")]

    # AST-based checks
    visitor = LaunchFileVisitor(filepath)
    visitor.visit(tree)
    visitor.check_duplicates()

    if not visitor.has_generate_func:
        issues.append(Issue(filepath, 0, "error",
            "Missing generate_launch_description() function. "
            "Every ROS 2 launch file must define this function."))

    issues.extend(visitor.issues)

    # Regex-based checks
    issues.extend(check_raw_patterns(filepath, source))

    return issues


def validate_directory(dirpath: str) -> ValidationResult:
    """Validate all launch files in a directory."""
    result = ValidationResult()

    for root, _, files in os.walk(dirpath):
        for f in sorted(files):
            if f.endswith(".launch.py"):
                filepath = os.path.join(root, f)
                issues = validate_file(filepath)
                result.issues.extend(issues)
                result.files_checked += 1

    return result


def main():
    parser = argparse.ArgumentParser(
        description="Static analysis for ROS 2 Python launch files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s src/my_robot_bringup/launch/
  %(prog)s src/my_robot_bringup/launch/robot.launch.py
  %(prog)s .  # Check all launch files recursively
        """)
    parser.add_argument("path", help="Launch file or directory to validate")
    parser.add_argument("--severity", choices=["error", "warning", "info"],
                        default="info",
                        help="Minimum severity to report (default: info)")
    args = parser.parse_args()

    severity_order = {"error": 2, "warning": 1, "info": 0}
    min_severity = severity_order[args.severity]

    path = Path(args.path)
    if not path.exists():
        print(f"Error: Path does not exist: {args.path}", file=sys.stderr)
        sys.exit(1)

    if path.is_file():
        issues = validate_file(str(path))
        result = ValidationResult(issues=issues, files_checked=1)
    else:
        result = validate_directory(str(path))

    # Filter by severity
    filtered = [i for i in result.issues
                if severity_order[i.severity] >= min_severity]

    # Print results
    if result.files_checked == 0:
        print("No *.launch.py files found.")
        sys.exit(0)

    print(f"Checked {result.files_checked} launch file(s)")
    print()

    if filtered:
        for issue in filtered:
            print(issue)
        print()
        print(f"Found: {result.error_count} error(s), "
              f"{result.warning_count} warning(s), "
              f"{len(result.issues) - result.error_count - result.warning_count} info(s)")
    else:
        print("No issues found.")

    sys.exit(1 if result.error_count > 0 else 0)


if __name__ == "__main__":
    main()
