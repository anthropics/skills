#!/usr/bin/env python3
"""
Safe test runner for the vscode skill.

Default tests do not write user settings, install extensions, open remote
windows, or modify any IDE state outside a temporary scratch directory. Temp
artifacts land in an isolated subdirectory under $VSCODE_SKILL_TEMP when set,
otherwise under the platform temp directory.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import hashlib
from contextlib import contextmanager
from pathlib import Path
from typing import Any


SKILL_DIR = Path(__file__).resolve().parents[1]
SCRIPT = SKILL_DIR / "scripts" / "vscode-cli.ps1"
SSHD_SCRIPT = SKILL_DIR / "scripts" / "setup-local-sshd.ps1"


def _default_quick_validate() -> Path | None:
    """Look for quick_validate.py from the Agent Skills skill-creator reference.

    Search order:
      1. $VSCODE_SKILL_QUICK_VALIDATE (explicit override)
      2. <skill-creator>/scripts/quick_validate.py under common dev locations
    Returns None if not found; the caller decides whether to skip the test.
    """
    env = os.environ.get("VSCODE_SKILL_QUICK_VALIDATE")
    if env:
        p = Path(env)
        return p if p.is_file() else None

    candidates: list[Path] = []
    for base in (
        os.environ.get("VSCODE_SKILL_CREATOR_HOME"),
        os.environ.get("CODEX_HOME"),
        os.environ.get("ZCODE_HOME"),
        os.environ.get("USERPROFILE"),
        os.environ.get("HOME"),
    ):
        if not base:
            continue
        root = Path(base)
        candidates.extend(
            [
                root / ".codex" / "skills" / ".system" / "skill-creator" / "scripts" / "quick_validate.py",
                root / ".zcode" / "skills" / ".system" / "skill-creator" / "scripts" / "quick_validate.py",
                root / ".agents" / "skills" / "skill-creator" / "scripts" / "quick_validate.py",
            ]
        )

    seen: set[Path] = set()
    for c in candidates:
        try:
            resolved = c.resolve()
        except OSError:
            continue
        if resolved in seen:
            continue
        seen.add(resolved)
        if resolved.is_file():
            return resolved
    return None


QUICK_VALIDATE = _default_quick_validate()


def _default_temp_base() -> Path:
    override = os.environ.get("VSCODE_SKILL_TEMP")
    base = Path(override) if override else Path(os.environ.get("TEMP", tempfile.gettempdir()))
    return base / "vscode-skill-tests"


def _default_temp_root() -> Path:
    digest = hashlib.sha1(str(SKILL_DIR).encode("utf-8")).hexdigest()[:10]
    return _default_temp_base() / f"{SKILL_DIR.name}-{digest}"


TEMP_ROOT = _default_temp_root()


def ps_quote(value: str) -> str:
    return "'" + value.replace("'", "''") + "'"


def run(
    args: list[str],
    *,
    name: str,
    timeout: int = 60,
    expect_ok: bool = True,
    cwd: Path | None = None,
) -> dict[str, Any]:
    proc = subprocess.run(
        args,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout,
        shell=False,
    )
    ok = proc.returncode == 0
    passed = ok if expect_ok else not ok
    return {
        "name": name,
        "command": args,
        "returncode": proc.returncode,
        "expectOk": expect_ok,
        "passed": passed,
        "stdout": proc.stdout[-6000:],
        "stderr": proc.stderr[-6000:],
    }


def run_ps(command: str, *, name: str, timeout: int = 60, expect_ok: bool = True) -> dict[str, Any]:
    return run(
        ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", command],
        name=name,
        timeout=timeout,
        expect_ok=expect_ok,
    )


def run_pwsh(command: str, *, name: str, timeout: int = 60, expect_ok: bool = True) -> dict[str, Any]:
    """Run through PowerShell 7 (pwsh) when available, fall back to Windows PowerShell."""
    candidates: list[list[str]] = []
    if shutil.which("pwsh"):
        candidates.append(["pwsh", "-NoProfile", "-Command", command])
    candidates.append(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", command])
    last: dict[str, Any] | None = None
    for cmd in candidates:
        result = run(cmd, name=name, timeout=timeout, expect_ok=expect_ok)
        last = result
        if result["passed"]:
            return result
    return last or {"name": name, "passed": False, "stderr": "no powershell host found"}


def run_vscode_cli(area: str, action: str | None = None, *extra: str, name: str, timeout: int = 60, expect_ok: bool = True) -> dict[str, Any]:
    cmd = ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(SCRIPT), area]
    if action:
        cmd.append(action)
    cmd.extend(extra)
    return run(cmd, name=name, timeout=timeout, expect_ok=expect_ok)


def powershell_parse(path: Path, name: str) -> dict[str, Any]:
    command = (
        "$tokens=$null; $errors=$null; "
        f"[System.Management.Automation.Language.Parser]::ParseFile({ps_quote(str(path))},[ref]$tokens,[ref]$errors) | Out-Null; "
        "if ($errors.Count) { $errors | Format-List Message,Extent; exit 1 } else { 'parse OK' }"
    )
    return run_pwsh(command, name=name)


def add(results: list[dict[str, Any]], result: dict[str, Any]) -> None:
    results.append(result)


@contextmanager
def temporary_env(updates: dict[str, str]):
    original = {key: os.environ.get(key) for key in updates}
    os.environ.update(updates)
    try:
        yield
    finally:
        for key, value in original.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


def write_fake_cli(path: Path, label: str = "Fake VS Code CLI") -> None:
    if os.name == "nt":
        path.write_text(
            "@echo off\r\n"
            "if \"%~1\"==\"--version\" (\r\n"
            f"  echo {label} 0.0.0\r\n"
            "  echo test-commit\r\n"
            "  echo x64\r\n"
            "  exit /b 0\r\n"
            ")\r\n"
            "if \"%~1\"==\"--list-extensions\" exit /b 0\r\n"
            f"echo {label} %*\r\n"
            "exit /b 0\r\n",
            encoding="utf-8",
        )
    else:
        path.write_text(
            "#!/usr/bin/env sh\n"
            "case \"$1\" in\n"
            f"  --version) printf '%s\\n' '{label} 0.0.0' 'test-commit' 'x64'; exit 0 ;;\n"
            "  --list-extensions) exit 0 ;;\n"
            f"  *) printf '%s %s\\n' '{label}' \"$*\"; exit 0 ;;\n"
            "esac\n",
            encoding="utf-8",
        )
        path.chmod(0o755)


def basic_tests(results: list[dict[str, Any]], scratch: Path) -> None:
    if QUICK_VALIDATE is not None:
        add(results, run([sys.executable, "-X", "utf8", str(QUICK_VALIDATE), str(SKILL_DIR)], name="quick_validate"))
    else:
        results.append(
            {
                "name": "quick_validate",
                "command": ["quick_validate.py"],
                "returncode": 0,
                "expectOk": False,
                "passed": True,
                "stdout": "skipped (quick_validate.py not located; set VSCODE_SKILL_QUICK_VALIDATE to enable)",
                "stderr": "",
            }
        )
    add(results, powershell_parse(SCRIPT, "parse vscode-cli.ps1"))
    if SSHD_SCRIPT.exists():
        add(results, powershell_parse(SSHD_SCRIPT, "parse setup-local-sshd.ps1"))

    fake_code = scratch / ("fake-code.cmd" if os.name == "nt" else "fake-code")
    fake_user = scratch / "Code" / "User"
    fake_ext = scratch / ".vscode" / "extensions"
    write_fake_cli(fake_code)
    fake_user.mkdir(parents=True, exist_ok=True)
    fake_ext.mkdir(parents=True, exist_ok=True)

    with temporary_env({
        "VSCODE_CODE_CLI": str(fake_code),
        "VSCODE_USER_DATA": str(fake_user),
        "VSCODE_EXTENSIONS_DIR": str(fake_ext),
    }):
        add(results, run_vscode_cli("info", None, "--Product", "auto", name="info auto with fake cli", timeout=90))
        add(results, run_vscode_cli("ext", "list", "--Product", "auto", name="ext list auto with fake cli", timeout=90))
        add(results, run_vscode_cli("settings-sync", "status", name="settings-sync status"))
        add(results, run_vscode_cli("profile", "list", name="profile list"))

    add(results, run_vscode_cli("settings", "path", "--Product", "vscode", name="settings path vscode"))
    add(results, run_vscode_cli("settings", "get", "--Product", "vscode", name="settings get vscode"))
    add(results, run_vscode_cli("settings", "path", "--Product", "codebuddy-cn", name="generic product requires configured path", expect_ok=False))

    generic_cli = scratch / ("fake-codebuddy.cmd" if os.name == "nt" else "fake-codebuddy")
    write_fake_cli(generic_cli, "Fake CodeBuddy CLI")
    generic_user = scratch / "CodeBuddy CN" / "User"
    generic_ext = scratch / ".codebuddycn" / "extensions"
    generic_user.mkdir(parents=True, exist_ok=True)
    generic_ext.mkdir(parents=True, exist_ok=True)
    generic_config = scratch / "generic-product-config.json"
    generic_config.write_text(
        json.dumps(
            {
                "product": "codebuddy-cn",
                "products": {
                    "codebuddy-cn": {
                        "cliPath": str(generic_cli),
                        "userDataPath": str(generic_user),
                        "extensionsPath": str(generic_ext),
                    }
                },
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    original_config = os.environ.get("VSCODE_SKILL_CONFIG")
    os.environ["VSCODE_SKILL_CONFIG"] = str(generic_config)
    try:
        add(results, run_vscode_cli("settings", "path", "--Product", "codebuddy-cn", name="generic product configured settings path"))
        add(results, run_vscode_cli("info", None, "--Product", "codebuddy-cn", name="generic product configured info"))
    finally:
        if original_config is None:
            os.environ.pop("VSCODE_SKILL_CONFIG", None)
        else:
            os.environ["VSCODE_SKILL_CONFIG"] = original_config

    project = scratch / "project-settings-smoke"
    project.mkdir(parents=True, exist_ok=True)
    add(
        results,
        run_vscode_cli(
            "settings",
            "smoke",
            "--Product",
            "vscode",
            "--Scope",
            "project",
            "--ProjectPath",
            str(project),
            name="project settings smoke vscode",
        ),
    )

    # New areas (v1.1): templates, extensions, settings-sync, profile, workspace.
    add(results, run_vscode_cli("tasks", "list", name="tasks list"))
    add(results, run_vscode_cli("launch", "list", name="launch list"))
    add(results, run_vscode_cli("extensions", "stacks", name="extensions stacks"))
    add(results, run_vscode_cli("extensions", "recommend", "--Stack", "polyglot-baseline", name="extensions recommend"))
    tasks_project = scratch / "tasks-init"
    tasks_project.mkdir(parents=True, exist_ok=True)
    add(
        results,
        run_vscode_cli(
            "tasks", "init",
            "--Template", "python-pytest",
            "--ProjectPath", str(tasks_project),
            "--Apply",
            name="tasks init python-pytest",
        ),
    )
    if (tasks_project / ".vscode" / "tasks.json").is_file():
        add(results, {"name": "tasks init wrote file", "command": [], "returncode": 0, "expectOk": True, "passed": True, "stdout": "", "stderr": ""})
    else:
        add(results, {"name": "tasks init wrote file", "command": [], "returncode": 1, "expectOk": True, "passed": False, "stdout": "", "stderr": "tasks.json missing"})


def optional_python_venv(results: list[dict[str, Any]], scratch: Path) -> None:
    project = scratch / "python-venv"
    add(results, run_vscode_cli("python", "make-venvs", "--ProjectPath", str(project), name="python make-venvs", timeout=180))
    add(results, run_vscode_cli("python", "set-interpreter", "--ProjectPath", str(project), "--VenvName", ".venv-a", name="python set interpreter"))
    add(results, run_vscode_cli("python", "verify", "--ProjectPath", str(project), "--ExpectedVenvName", ".venv-a", name="python verify interpreter"))


def main() -> int:
    parser = argparse.ArgumentParser(description="Run safe checks for the vscode skill.")
    parser.add_argument("--basic", action="store_true", help="Run basic safe tests. Default when no group is selected.")
    parser.add_argument("--include-python-venv", action="store_true")
    parser.add_argument("--clean", action="store_true", help="Delete old temp root before testing.")
    args = parser.parse_args()

    if args.clean and TEMP_ROOT.exists():
        shutil.rmtree(TEMP_ROOT)
    TEMP_ROOT.mkdir(parents=True, exist_ok=True)

    results: list[dict[str, Any]] = []
    if args.basic or not args.include_python_venv:
        basic_tests(results, TEMP_ROOT)
    if args.include_python_venv:
        optional_python_venv(results, TEMP_ROOT)

    passed = sum(1 for item in results if item["passed"])
    failed = len(results) - passed
    summary = {
        "ok": failed == 0,
        "passed": passed,
        "failed": failed,
        "tempRoot": str(TEMP_ROOT),
        "skillDir": str(SKILL_DIR),
        "results": results,
    }
    out_path = TEMP_ROOT / "test-summary.json"
    out_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "results"}, ensure_ascii=False, indent=2))
    if failed:
        for item in results:
            if not item["passed"]:
                print(f"FAILED: {item['name']} rc={item['returncode']}", file=sys.stderr)
                if item.get("stderr"):
                    print(item["stderr"][-1200:], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
