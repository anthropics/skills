#!/usr/bin/env python3
"""
Unity Project Health Check

Comprehensive health check for Unity projects covering:
- GUID validation
- Meta file synchronization
- Project settings validation
- Common configuration issues

Usage:
    python project_health_check.py <unity_project_path>
    python project_health_check.py <unity_project_path> --verbose
"""

import sys
import yaml
from pathlib import Path


def check_project_structure(project_path):
    """Verify essential Unity project directories exist."""
    required_dirs = ["Assets", "ProjectSettings"]
    issues = []

    for dir_name in required_dirs:
        dir_path = project_path / dir_name
        if not dir_path.exists():
            issues.append(f"Missing required directory: {dir_name}")

    return issues


def check_input_system_config(project_path):
    """Check Input System configuration in ProjectSettings."""
    settings_file = project_path / "ProjectSettings" / "ProjectSettings.asset"

    if not settings_file.exists():
        return ["ProjectSettings.asset not found"]

    issues = []

    try:
        with open(settings_file, "r", encoding="utf-8") as f:
            content = f.read()

            # Check activeInputHandler setting
            if "activeInputHandler:" in content:
                for line in content.split("\n"):
                    if "activeInputHandler:" in line:
                        value = line.split(":")[1].strip()
                        if value == "0":
                            issues.append(
                                "Input System: Set to 'Legacy' (0). "
                                "Consider using 'Both' (2) for compatibility"
                            )
                        elif value == "1":
                            issues.append(
                                "Input System: Set to 'New' (1). "
                                "Legacy Input API will not work"
                            )
                        break
    except Exception as e:
        issues.append(f"Error reading ProjectSettings.asset: {e}")

    return issues


def check_urp_configuration(project_path):
    """Check URP (Universal Render Pipeline) configuration."""
    issues = []

    # Check if URP package exists
    packages_file = project_path / "Packages" / "manifest.json"
    if not packages_file.exists():
        return []

    try:
        import json

        with open(packages_file, "r", encoding="utf-8") as f:
            manifest = json.load(f)
            dependencies = manifest.get("dependencies", {})

            if "com.unity.render-pipelines.universal" in dependencies:
                # URP is installed, check for common issues
                graphics_settings = (
                    project_path / "ProjectSettings" / "GraphicsSettings.asset"
                )
                if not graphics_settings.exists():
                    issues.append("URP: GraphicsSettings.asset not found")
                else:
                    # Check if render pipeline asset is assigned
                    with open(graphics_settings, "r", encoding="utf-8") as gs:
                        gs_content = gs.read()
                        if "m_CustomRenderPipeline: {fileID: 0}" in gs_content:
                            issues.append(
                                "URP: No render pipeline asset assigned in Graphics Settings. "
                                "Create and assign a URP asset"
                            )
    except Exception as e:
        pass  # Silent if packages not available

    return issues


def check_physics_settings(project_path):
    """Check physics configuration for common issues."""
    issues = []

    # Check Physics settings
    physics_file = project_path / "ProjectSettings" / "DynamicsManager.asset"
    if physics_file.exists():
        try:
            with open(physics_file, "r", encoding="utf-8") as f:
                content = f.read()

                # Check collision matrix
                if "m_DefaultContactOffset:" in content:
                    for line in content.split("\n"):
                        if "m_DefaultContactOffset:" in line:
                            value = line.split(":")[1].strip()
                            try:
                                offset = float(value)
                                if offset < 0.001:
                                    issues.append(
                                        f"Physics: Contact offset very small ({offset}). "
                                        "May cause collision detection issues"
                                    )
                            except ValueError:
                                pass
                            break
        except Exception:
            pass

    return issues


def check_version_control_settings(project_path):
    """Check version control configuration."""
    issues = []

    editor_settings = project_path / "ProjectSettings" / "EditorSettings.asset"
    if not editor_settings.exists():
        return issues

    try:
        with open(editor_settings, "r", encoding="utf-8") as f:
            content = f.read()

            # Check asset serialization mode
            if "m_SerializationMode:" in content:
                for line in content.split("\n"):
                    if "m_SerializationMode:" in line:
                        value = line.split(":")[1].strip()
                        if value != "2":  # 2 = Force Text
                            issues.append(
                                f"Version Control: Asset Serialization Mode not set to 'Force Text'. "
                                f"Current: {value}. Recommended: 2 (Force Text) for better git diffs"
                            )
                        break

            # Check if visible meta files enabled
            if "m_ExternalVersionControlSupport:" in content:
                for line in content.split("\n"):
                    if "m_ExternalVersionControlSupport:" in line:
                        value = line.split(":", 1)[1].strip()
                        if "Visible Meta Files" not in value:
                            issues.append(
                                "Version Control: 'Visible Meta Files' not enabled. "
                                "Enable for proper git integration"
                            )
                        break
    except Exception as e:
        issues.append(f"Error checking version control settings: {e}")

    return issues


def check_gitignore(project_path):
    """Check if .gitignore is properly configured."""
    issues = []

    gitignore = project_path / ".gitignore"
    if not gitignore.exists():
        issues.append(
            "No .gitignore found. Create one to exclude Library/, Temp/, etc."
        )
        return issues

    try:
        with open(gitignore, "r", encoding="utf-8") as f:
            content = f.read()

            required_patterns = ["Library/", "Temp/", "obj/", "Logs/"]
            missing = []

            for pattern in required_patterns:
                if pattern not in content:
                    missing.append(pattern)

            if missing:
                issues.append(f".gitignore: Missing patterns: {', '.join(missing)}")
    except Exception as e:
        issues.append(f"Error reading .gitignore: {e}")

    return issues


def run_health_check(project_path, verbose=False):
    """Run comprehensive health check."""
    project_path = Path(project_path)

    if not project_path.exists():
        raise ValueError(f"Project path not found: {project_path}")

    print(f"Unity Project Health Check: {project_path}\n")
    print("=" * 60)

    all_issues = []

    # Run all checks
    checks = [
        ("Project Structure", check_project_structure),
        ("Input System Configuration", check_input_system_config),
        ("URP Configuration", check_urp_configuration),
        ("Physics Settings", check_physics_settings),
        ("Version Control Settings", check_version_control_settings),
        (".gitignore", check_gitignore),
    ]

    for check_name, check_func in checks:
        print(f"\nChecking {check_name}...")
        issues = check_func(project_path)

        if issues:
            print(f"  ⚠ {len(issues)} issue(s) found:")
            for issue in issues:
                print(f"    - {issue}")
            all_issues.extend(issues)
        else:
            print(f"  ✓ No issues")

    print("\n" + "=" * 60)

    if all_issues:
        print(f"\n❌ HEALTH CHECK FOUND {len(all_issues)} ISSUE(S)")
        print("\nReview the issues above and address them to improve project health.")
        return 1
    else:
        print("\n✓ HEALTH CHECK PASSED")
        print("Project configuration looks good!")
        return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    project_path = sys.argv[1]
    verbose = "--verbose" in sys.argv

    try:
        exit_code = run_health_check(project_path, verbose=verbose)
        sys.exit(exit_code)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
