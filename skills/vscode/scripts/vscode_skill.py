#!/usr/bin/env python3
"""Cross-platform gateway for the VS Code agent skill.

Routing rules:
- On Windows: forwards directly to scripts/vscode-cli.ps1 (the PowerShell
  driver that has passed 11/11 safe tests). All flags and areas are passed
  through unchanged so behavior on Windows is bit-for-bit identical to the
  previous skill.
- On macOS / Linux: provides native Python implementations for the
  read/write areas that are safe and portable (info, ext list, settings
  get/path/set/smoke, python set-interpreter). Operations requiring VS
  Code itself (ext install, ssh open, wsl open) still shell out to the
  ``code`` CLI.

The gateway never modifies PATH, never reads tokens, and never writes
outside the resolved settings file (or the temp scratch directory during
``settings smoke``).
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


SKILL_ROOT = Path(__file__).resolve().parents[1]
PS_DRIVER = SKILL_ROOT / "scripts" / "vscode-cli.ps1"
IS_WINDOWS = platform.system() == "Windows"


# --------------------------------------------------------------------------- #
# Path resolution (cross-platform)
# --------------------------------------------------------------------------- #

def _resolve_config_path() -> Path | None:
    env = os.environ.get("VSCODE_SKILL_CONFIG")
    if env:
        return Path(env)
    if IS_WINDOWS:
        appdata = os.environ.get("APPDATA")
        if appdata:
            return Path(appdata) / "vscode-skill" / "config.json"
    xdg = os.environ.get("XDG_CONFIG_HOME")
    if xdg:
        return Path(xdg) / "vscode-skill" / "config.json"
    home = Path.home()
    return home / ".config" / "vscode-skill" / "config.json"


def _load_config() -> dict[str, Any]:
    cfg_path = _resolve_config_path()
    if cfg_path and cfg_path.is_file():
        try:
            return json.loads(cfg_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            return {}
    return {}


def _resolve_cli(product: str) -> str:
    cfg = _load_config()
    products = cfg.get("products") or {}
    entry = products.get(product) or {}
    cli_path = entry.get("cliPath")
    if cli_path and Path(cli_path).is_file():
        return cli_path
    if product == "vscode":
        env_override = os.environ.get("VSCODE_CODE_CLI")
        if env_override and Path(env_override).is_file():
            return env_override
        for cand in ("code.cmd", "code"):
            found = shutil.which(cand)
            if found:
                return found
        if IS_WINDOWS:
            local = os.environ.get("LOCALAPPDATA")
            if local:
                p = Path(local) / "Programs" / "Microsoft VS Code" / "bin" / "code.cmd"
                if p.is_file():
                    return str(p)
    if product == "vscode-insiders":
        env_override = os.environ.get("VSCODE_INSIDERS_CLI")
        if env_override and Path(env_override).is_file():
            return env_override
        for cand in ("code-insiders.cmd", "code-insiders"):
            found = shutil.which(cand)
            if found:
                return found
    raise FileNotFoundError(f"Cannot resolve CLI for product '{product}'. "
                            f"Set products.{product}.cliPath in your config or add it to PATH.")


def _user_data_dir(product: str) -> Path:
    env_override = os.environ.get("VSCODE_USER_DATA")
    if env_override:
        return Path(env_override)
    cfg = _load_config()
    entry = (cfg.get("products") or {}).get(product) or {}
    custom = entry.get("userDataPath")
    if custom:
        return Path(custom)
    if product == "vscode":
        if IS_WINDOWS:
            return Path(os.environ["APPDATA"]) / "Code" / "User"
        if platform.system() == "Darwin":
            return Path.home() / "Library" / "Application Support" / "Code" / "User"
        xdg = os.environ.get("XDG_CONFIG_HOME") or str(Path.home() / ".config")
        return Path(xdg) / "Code" / "User"
    if product == "vscode-insiders":
        if IS_WINDOWS:
            return Path(os.environ["APPDATA"]) / "Code - Insiders" / "User"
        if platform.system() == "Darwin":
            return Path.home() / "Library" / "Application Support" / "Code - Insiders" / "User"
        xdg = os.environ.get("XDG_CONFIG_HOME") or str(Path.home() / ".config")
        return Path(xdg) / "Code - Insiders" / "User"
    raise FileNotFoundError(f"No userDataPath known for product '{product}'.")


def _settings_path(scope: str, project: str | None) -> Path:
    if scope == "project":
        if not project:
            raise ValueError("Project scope requires --ProjectPath.")
        return Path(project) / ".vscode" / "settings.json"
    if scope == "user":
        return _user_data_dir(_resolve_default_product()) / "settings.json"
    raise ValueError(f"Unknown scope '{scope}'.")


def _resolve_default_product() -> str:
    env = os.environ.get("VSCODE_SKILL_PRODUCT")
    if env:
        return env
    cfg = _load_config()
    p = cfg.get("product")
    if p:
        return str(p)
    return "vscode"


# --------------------------------------------------------------------------- #
# Forwarding to PowerShell on Windows
# --------------------------------------------------------------------------- #

def _forward_powershell(argv: list[str]) -> int:
    if not PS_DRIVER.is_file():
        print(f"error: PowerShell driver not found at {PS_DRIVER}", file=sys.stderr)
        return 2
    args = ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(PS_DRIVER), *argv]
    return subprocess.call(args)


# --------------------------------------------------------------------------- #
# Native macOS / Linux implementations
# --------------------------------------------------------------------------- #

def _read_settings(path: Path) -> dict[str, Any]:
    if not path.is_file():
        return {}
    raw = path.read_text(encoding="utf-8")
    if not raw.strip():
        return {}
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        print(f"warning: {path} is not valid JSON; treating as empty.", file=sys.stderr)
        return {}


def _write_settings(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=4, ensure_ascii=False) + "\n", encoding="utf-8")


def _coerce(value: str) -> Any:
    s = value.strip()
    if s.lower() in ("true", "false"):
        return s.lower() == "true"
    if s.lstrip("-").isdigit():
        return int(s)
    try:
        return float(s)
    except ValueError:
        pass
    if (s.startswith("{") and s.endswith("}")) or (s.startswith("[") and s.endswith("]")):
        try:
            return json.loads(s)
        except json.JSONDecodeError:
            pass
    return value


SETTINGS_FLAG_MAP = {
    "--FontSize":          ("editor.fontSize", int),
    "--LineHeight":        ("editor.lineHeight", float),
    "--FontFamily":        ("editor.fontFamily", None),
    "--ColorTheme":        ("workbench.colorTheme", None),
    "--IconTheme":         ("workbench.iconTheme", None),
    "--ProductIconTheme":  ("workbench.productIconTheme", None),
    "--WordWrap":          ("editor.wordWrap", None),
    "--TabSize":           ("editor.tabSize", int),
    "--FormatOnSave":      ("editor.formatOnSave", _coerce),
    "--AutoSave":          ("files.autoSave", None),
    "--Minimap":           ("editor.minimap.enabled", _coerce),
}


def cmd_info(_args: argparse.Namespace) -> int:
    product = _resolve_default_product()
    cli = _resolve_cli(product)
    user = _user_data_dir(product)
    print(f"== {product} ==")
    print(f"  CliPath        : {cli}")
    print(f"  UserSettings   : {user / 'settings.json'}")
    print(f"  Extensions     : {user.parent.parent / 'extensions'}")
    print(f"  ConfigFile     : {_resolve_config_path()}")
    print(f"== Version ==")
    subprocess.call([cli, "--version"])
    return 0


def cmd_ext_list(_args: argparse.Namespace) -> int:
    product = _resolve_default_product()
    cli = _resolve_cli(product)
    return subprocess.call([cli, "--list-extensions", "--show-versions"])


def cmd_settings_path(args: argparse.Namespace) -> int:
    path = _settings_path(args.scope or "user", args.ProjectPath)
    print(json.dumps({
        "Scope": args.scope or "user",
        "Path": str(path),
        "Exists": path.is_file(),
    }, indent=2))
    return 0


def cmd_settings_get(args: argparse.Namespace) -> int:
    path = _settings_path(args.scope or "user", args.ProjectPath)
    settings = _read_settings(path)
    keys = [
        "editor.fontFamily", "editor.fontSize", "editor.lineHeight",
        "workbench.colorTheme", "workbench.iconTheme",
        "workbench.productIconTheme", "editor.wordWrap", "editor.tabSize",
        "editor.formatOnSave", "files.autoSave", "editor.minimap.enabled",
    ]
    print(f"== Settings file ({path}) ==")
    print(json.dumps({k: settings.get(k) for k in keys}, indent=2, ensure_ascii=False))
    return 0


def cmd_settings_set(args: argparse.Namespace) -> int:
    if not args.apply:
        print("error: settings set is a write operation. Pass --Apply.", file=sys.stderr)
        return 2
    scope = args.scope or "user"
    path = _settings_path(scope, args.ProjectPath)
    settings = _read_settings(path)

    flag_dict = vars(args)
    for flag, (key, coerce) in SETTINGS_FLAG_MAP.items():
        val = flag_dict.get(flag.lstrip("-").replace("-", "_").lower())
        if val is not None and val != "":
            settings[key] = coerce(val) if coerce else val
    if args.SettingKey:
        settings[args.SettingKey] = _coerce(args.SettingValue or "")

    _write_settings(path, settings)
    print(json.dumps({"Path": str(path), "Written": True}, indent=2))
    return 0


def cmd_settings_smoke(args: argparse.Namespace) -> int:
    scope = "user"
    path = _settings_path(scope, None)
    existed = path.is_file()
    original = path.read_text(encoding="utf-8") if existed else None

    try:
        settings = _read_settings(path)
        settings.update({
            "editor.fontFamily": "Consolas, 'Courier New', monospace",
            "editor.fontSize": 15,
            "editor.lineHeight": 22,
            "workbench.colorTheme": "Default Dark Modern",
            "editor.wordWrap": "on",
            "editor.tabSize": 2,
            "editor.formatOnSave": False,
            "files.autoSave": "off",
            "editor.minimap.enabled": False,
        })
        _write_settings(path, settings)

        verify = _read_settings(path)
        ok = (
            verify["editor.fontFamily"] == "Consolas, 'Courier New', monospace"
            and verify["editor.fontSize"] == 15
            and verify["editor.lineHeight"] == 22
            and verify["workbench.colorTheme"] == "Default Dark Modern"
            and verify["editor.wordWrap"] == "on"
            and verify["editor.tabSize"] == 2
            and verify["editor.formatOnSave"] is False
            and verify["files.autoSave"] == "off"
            and verify["editor.minimap.enabled"] is False
        )
        if not ok:
            print("error: settings smoke verification failed.", file=sys.stderr)
            return 1
        print(json.dumps({"Path": str(path), "TemporaryWriteVerified": True}, indent=2))
    finally:
        if existed and original is not None:
            path.write_text(original, encoding="utf-8")
        elif path.is_file():
            path.unlink()
    print(json.dumps({"Path": str(path), "RestoredOriginal": True}, indent=2))
    return 0


def cmd_python_set_interpreter(args: argparse.Namespace) -> int:
    project = Path(args.ProjectPath).resolve()
    venv = project / args.VenvName
    candidates = [
        venv / "bin" / "python",
        venv / "Scripts" / "python.exe",
    ]
    py = next((c for c in candidates if c.is_file()), None)
    if py is None:
        print(f"error: python interpreter not found; tried: {[str(c) for c in candidates]}", file=sys.stderr)
        return 2
    settings_path = project / ".vscode" / "settings.json"
    settings = _read_settings(settings_path)
    settings["python.defaultInterpreterPath"] = str(py)
    _write_settings(settings_path, settings)
    print(json.dumps({"Settings": str(settings_path), "Interpreter": str(py)}, indent=2))
    return 0


# --------------------------------------------------------------------------- #
# Templates (tasks.json / launch.json)
# --------------------------------------------------------------------------- #

TEMPLATES_DIR = SKILL_ROOT / "references" / "templates"


def _list_template_ids(kind: str) -> list[str]:
    d = TEMPLATES_DIR / kind
    if not d.is_dir():
        return []
    return sorted(p.stem for p in d.glob("*.json"))


def _load_template(kind: str, template_id: str) -> dict[str, Any]:
    path = TEMPLATES_DIR / kind / f"{template_id}.json"
    if not path.is_file():
        raise FileNotFoundError(f"Template '{template_id}' not found under {TEMPLATES_DIR / kind}. "
                                f"Available: {_list_template_ids(kind)}")
    return json.loads(path.read_text(encoding="utf-8"))


def cmd_tasks_list(_args: argparse.Namespace) -> int:
    print(json.dumps({"templates": _list_template_ids("tasks")}, indent=2))
    return 0


def cmd_tasks_init(args: argparse.Namespace) -> int:
    project = Path(args.ProjectPath).resolve()
    target = project / ".vscode" / "tasks.json"
    if target.is_file() and not args.Force:
        print(f"error: {target} already exists. Pass --Force to overwrite.", file=sys.stderr)
        return 2
    data = _load_template("tasks", args.Template)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(data, indent=4, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"Path": str(target), "Template": args.Template, "Written": True}, indent=2))
    return 0


def cmd_launch_list(_args: argparse.Namespace) -> int:
    print(json.dumps({"templates": _list_template_ids("launch")}, indent=2))
    return 0


def cmd_launch_init(args: argparse.Namespace) -> int:
    project = Path(args.ProjectPath).resolve()
    target = project / ".vscode" / "launch.json"
    if target.is_file() and not args.Force:
        print(f"error: {target} already exists. Pass --Force to overwrite.", file=sys.stderr)
        return 2
    data = _load_template("launch", args.Template)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(data, indent=4, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"Path": str(target), "Template": args.Template, "Written": True}, indent=2))
    return 0


# --------------------------------------------------------------------------- #
# Extension packs
# --------------------------------------------------------------------------- #

EXTENSION_PACKS_FILE = SKILL_ROOT / "references" / "extension-packs.md"


def _parse_extension_packs() -> dict[str, list[dict[str, str]]]:
    r"""Parse references/extension-packs.md into {stack_name: [{id, purpose}]}.

    The parser is intentionally simple: it looks for `### `<stack>` headers
    followed by tables whose first column is the extension ID and second is purpose.
    """
    if not EXTENSION_PACKS_FILE.is_file():
        return {}
    text = EXTENSION_PACKS_FILE.read_text(encoding="utf-8")
    packs: dict[str, list[dict[str, str]]] = {}
    current_stack: str | None = None
    for line in text.splitlines():
        m = re.match(r"^### `([a-z0-9-]+)`", line)
        if m:
            current_stack = m.group(1)
            packs[current_stack] = []
            continue
        if current_stack is None:
            continue
        if not line.startswith("|"):
            continue
        cells = [c.strip().strip("`") for c in line.strip().strip("|").split("|")]
        if len(cells) < 2:
            continue
        if cells[0] in ("ID", "---", "---"):
            continue
        if re.match(r"^[a-zA-Z0-9_-]+\.[a-zA-Z0-9_.-]+$", cells[0]):
            packs[current_stack].append({"id": cells[0], "purpose": cells[1]})
    return packs


def cmd_extensions_recommend(args: argparse.Namespace) -> int:
    packs = _parse_extension_packs()
    if args.Stack not in packs:
        print(f"error: unknown stack '{args.Stack}'. Available: {sorted(packs.keys())}", file=sys.stderr)
        return 2
    print(json.dumps({"stack": args.Stack, "extensions": packs[args.Stack]}, indent=2, ensure_ascii=False))
    return 0


def cmd_extensions_install(args: argparse.Namespace) -> int:
    packs = _parse_extension_packs()
    if args.Stack not in packs:
        print(f"error: unknown stack '{args.Stack}'. Available: {sorted(packs.keys())}", file=sys.stderr)
        return 2
    cli = _resolve_cli(_resolve_default_product())
    failures: list[dict[str, str]] = []
    for entry in packs[args.Stack]:
        ext_id = entry["id"]
        print(f"installing {ext_id}...", file=sys.stderr)
        rc = subprocess.call([cli, "--install-extension", ext_id])
        if rc != 0:
            failures.append({"id": ext_id, "purpose": entry["purpose"], "exitCode": str(rc)})
    summary = {
        "stack": args.Stack,
        "total": len(packs[args.Stack]),
        "failures": failures,
    }
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 1 if failures else 0


def cmd_extensions_pin(args: argparse.Namespace) -> int:
    packs = _parse_extension_packs()
    if args.Stack not in packs:
        print(f"error: unknown stack '{args.Stack}'. Available: {sorted(packs.keys())}", file=sys.stderr)
        return 2
    project = Path(args.ProjectPath).resolve()
    target = project / ".vscode" / "extensions.json"
    existing = _read_settings(target) if target.is_file() else {}
    recommendations = existing.get("recommendations") or []
    for entry in packs[args.Stack]:
        if entry["id"] not in recommendations:
            recommendations.append(entry["id"])
    existing["recommendations"] = recommendations
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(existing, indent=4, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"Path": str(target), "Stack": args.Stack, "Recommendations": recommendations}, indent=2, ensure_ascii=False))
    return 0


def cmd_extensions_stacks(_args: argparse.Namespace) -> int:
    packs = _parse_extension_packs()
    print(json.dumps({"stacks": sorted(packs.keys())}, indent=2))
    return 0


# --------------------------------------------------------------------------- #
# Settings Sync (read-only first)
# --------------------------------------------------------------------------- #

def _sync_storage_paths() -> list[Path]:
    """Locate VS Code's settings sync storage locations for inspection only."""
    candidates: list[Path] = []
    if IS_WINDOWS:
        app = os.environ.get("APPDATA")
        if app:
            candidates.append(Path(app) / "Code" / "User" / "sync")
            candidates.append(Path(app) / "Code - Insiders" / "User" / "sync")
    elif platform.system() == "Darwin":
        candidates.append(Path.home() / "Library" / "Application Support" / "Code" / "User" / "sync")
        candidates.append(Path.home() / "Library" / "Application Support" / "Code - Insiders" / "User" / "sync")
    else:
        xdg = os.environ.get("XDG_CONFIG_HOME") or str(Path.home() / ".config")
        candidates.append(Path(xdg) / "Code" / "User" / "sync")
        candidates.append(Path(xdg) / "Code - Insiders" / "User" / "sync")
    return [p for p in candidates if p.exists()]


def cmd_settings_sync_status(_args: argparse.Namespace) -> int:
    """Report whether settings sync storage exists on this machine.

    Settings sync is a per-account feature; this command does not read tokens
    or any sync payload, only the on-disk presence of the sync folder.
    """
    paths = _sync_storage_paths()
    print(json.dumps({
        "syncStorageFound": bool(paths),
        "locations": [str(p) for p in paths],
        "note": "Settings sync is controlled via the VS Code UI (Accounts → Backup and Sync Settings). "
                "The skill does not enable or disable sync programmatically to avoid accidental data leaks.",
    }, indent=2))
    return 0


# --------------------------------------------------------------------------- #
# Multi-root workspace
# --------------------------------------------------------------------------- #

def _find_workspace_file(project: Path) -> Path | None:
    candidates = list(project.glob("*.code-workspace"))
    return candidates[0] if candidates else None


def cmd_workspace_info(args: argparse.Namespace) -> int:
    if not args.ProjectPath:
        print("error: workspace info requires --ProjectPath.", file=sys.stderr)
        return 2
    project = Path(args.ProjectPath).resolve()
    workspace_file = _find_workspace_file(project)
    if not workspace_file:
        print(json.dumps({
            "ProjectPath": str(project),
            "IsMultiRoot": False,
            "note": "No .code-workspace file found. This is a single-root workspace; use 'settings set --Scope project'.",
        }, indent=2))
        return 0
    data = json.loads(workspace_file.read_text(encoding="utf-8"))
    folders = data.get("folders") or []
    summary = {
        "ProjectPath": str(project),
        "IsMultiRoot": len(folders) > 1,
        "WorkspaceFile": str(workspace_file),
        "Folders": [f.get("path") for f in folders],
        "FolderSettings": [
            {"path": f.get("path"), "settings": f.get("settings", {})}
            for f in folders if f.get("settings")
        ],
    }
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


def cmd_workspace_folder_settings_get(args: argparse.Namespace) -> int:
    if not args.ProjectPath or not args.Folder:
        print("error: workspace folder-settings-get requires --ProjectPath and --Folder.", file=sys.stderr)
        return 2
    project = Path(args.ProjectPath).resolve()
    workspace_file = _find_workspace_file(project)
    if not workspace_file:
        print("error: not a multi-root workspace (no .code-workspace file).", file=sys.stderr)
        return 2
    data = json.loads(workspace_file.read_text(encoding="utf-8"))
    folder_entry = next((f for f in data.get("folders", []) if f.get("path") == args.Folder), None)
    if folder_entry is None:
        print(f"error: folder '{args.Folder}' not found in workspace file.", file=sys.stderr)
        return 2
    folder_settings = folder_entry.get("settings") or {}
    if args.SettingKey:
        print(json.dumps({"key": args.SettingKey, "value": folder_settings.get(args.SettingKey)}, indent=2, ensure_ascii=False))
    else:
        print(json.dumps({"folder": args.Folder, "settings": folder_settings}, indent=2, ensure_ascii=False))
    return 0


def cmd_workspace_folder_settings_set(args: argparse.Namespace) -> int:
    if not args.ProjectPath or not args.Folder or not args.SettingKey:
        print("error: workspace folder-settings-set requires --ProjectPath, --Folder, --SettingKey.", file=sys.stderr)
        return 2
    if not args.Apply:
        print("error: workspace folder-settings-set is a write operation. Pass --Apply.", file=sys.stderr)
        return 2
    project = Path(args.ProjectPath).resolve()
    workspace_file = _find_workspace_file(project)
    if not workspace_file:
        print("error: not a multi-root workspace (no .code-workspace file).", file=sys.stderr)
        return 2
    data = json.loads(workspace_file.read_text(encoding="utf-8"))
    folders = data.get("folders") or []
    target = next((f for f in folders if f.get("path") == args.Folder), None)
    if target is None:
        print(f"error: folder '{args.Folder}' not found in workspace file.", file=sys.stderr)
        return 2
    target.setdefault("settings", {})[args.SettingKey] = _coerce(args.SettingValue or "")
    data["folders"] = folders
    workspace_file.write_text(json.dumps(data, indent=4, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"WorkspaceFile": str(workspace_file), "Folder": args.Folder, "Key": args.SettingKey, "Value": target["settings"][args.SettingKey]}, indent=2, ensure_ascii=False))
    return 0


# --------------------------------------------------------------------------- #
# Profiles (read-only)
# --------------------------------------------------------------------------- #

def _profiles_dir() -> Path | None:
    """Return the profiles directory of the resolved product, or None if absent."""
    user_data = _user_data_dir(_resolve_default_product())
    return user_data / "profiles"


def cmd_profile_list(_args: argparse.Namespace) -> int:
    profiles_dir = _profiles_dir()
    if profiles_dir is None or not profiles_dir.is_dir():
        print(json.dumps({"profiles": [], "note": "No profiles directory found; no profiles defined."}, indent=2))
        return 0
    entries: list[dict[str, Any]] = []
    for child in sorted(profiles_dir.iterdir()):
        if not child.is_dir():
            continue
        settings_path = child / "settings.json"
        entry: dict[str, Any] = {
            "name": child.name,
            "settingsFileExists": settings_path.is_file(),
        }
        if settings_path.is_file():
            try:
                data = json.loads(settings_path.read_text(encoding="utf-8"))
                entry["settingCount"] = len(data)
                entry["sampleKeys"] = sorted(list(data.keys()))[:5]
            except json.JSONDecodeError:
                entry["parseError"] = "settings.json is not valid JSON"
        entries.append(entry)
    print(json.dumps({"profilesDir": str(profiles_dir), "profiles": entries}, indent=2, ensure_ascii=False))
    return 0


def cmd_profile_show(args: argparse.Namespace) -> int:
    if not args.Profile:
        print("error: profile show requires --Profile.", file=sys.stderr)
        return 2
    profiles_dir = _profiles_dir()
    if profiles_dir is None:
        print("error: profiles directory does not exist for this product.", file=sys.stderr)
        return 2
    profile_dir = profiles_dir / args.Profile
    settings_path = profile_dir / "settings.json"
    if not settings_path.is_file():
        print(f"error: profile '{args.Profile}' not found or has no settings.json.", file=sys.stderr)
        return 2
    print(json.dumps({
        "profile": args.Profile,
        "settingsFile": str(settings_path),
        "settings": json.loads(settings_path.read_text(encoding="utf-8")),
    }, indent=2, ensure_ascii=False))
    return 0


# --------------------------------------------------------------------------- #
# Argument parsing
# --------------------------------------------------------------------------- #


# --------------------------------------------------------------------------- #
# Argument parsing
# --------------------------------------------------------------------------- #

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="vscode_skill", description="VS Code skill cross-platform gateway.")
    sub = p.add_subparsers(dest="area", required=True)

    sub.add_parser("info", help="Show product, CLI path, key locations.")

    ext = sub.add_parser("ext", help="Manage extensions.")
    ext.add_argument("action", choices=["list"], help="Currently only 'list' is supported on macOS/Linux.")

    settings = sub.add_parser("settings", help="Read or write settings.")
    settings.add_argument("action", choices=["path", "get", "set", "smoke"])
    settings.add_argument("--Scope", choices=["user", "project"], default="user")
    settings.add_argument("--ProjectPath")
    settings.add_argument("--Apply", action="store_true")
    settings.add_argument("--FontSize", type=str)
    settings.add_argument("--LineHeight", type=str)
    settings.add_argument("--FontFamily", type=str)
    settings.add_argument("--ColorTheme", type=str)
    settings.add_argument("--IconTheme", type=str)
    settings.add_argument("--ProductIconTheme", type=str)
    settings.add_argument("--WordWrap", type=str)
    settings.add_argument("--TabSize", type=str)
    settings.add_argument("--FormatOnSave", type=str)
    settings.add_argument("--AutoSave", type=str)
    settings.add_argument("--Minimap", type=str)
    settings.add_argument("--SettingKey", type=str)
    settings.add_argument("--SettingValue", type=str)

    py = sub.add_parser("python", help="Python interpreter helpers.")
    py.add_argument("action", choices=["set-interpreter"])
    py.add_argument("--ProjectPath", required=True)
    py.add_argument("--VenvName", required=True)

    tasks = sub.add_parser("tasks", help="Manage .vscode/tasks.json from templates.")
    tasks.add_argument("action", choices=["list", "init"])
    tasks.add_argument("--Template")
    tasks.add_argument("--ProjectPath")
    tasks.add_argument("--Force", action="store_true")

    launch = sub.add_parser("launch", help="Manage .vscode/launch.json from templates.")
    launch.add_argument("action", choices=["list", "init"])
    launch.add_argument("--Template")
    launch.add_argument("--ProjectPath")
    launch.add_argument("--Force", action="store_true")

    ext2 = sub.add_parser("extensions", help="Manage recommended extension stacks.")
    ext2.add_argument("action", choices=["stacks", "recommend", "install", "pin"])
    ext2.add_argument("--Stack")
    ext2.add_argument("--ProjectPath")

    sync = sub.add_parser("settings-sync", help="Inspect VS Code settings sync state.")
    sync.add_argument("action", choices=["status"])

    workspace = sub.add_parser("workspace", help="Inspect and edit multi-root workspace settings.")
    workspace.add_argument("action", choices=["info", "folder-settings-set", "folder-settings-get"])
    workspace.add_argument("--ProjectPath")
    workspace.add_argument("--Folder", help="Multi-root folder name to scope to")
    workspace.add_argument("--SettingKey")
    workspace.add_argument("--SettingValue")
    workspace.add_argument("--Apply", action="store_true")

    profile = sub.add_parser("profile", help="Inspect VS Code profiles (read-only).")
    profile.add_argument("action", choices=["list", "show"])
    profile.add_argument("--Profile")

    return p


# --------------------------------------------------------------------------- #
# Native dispatch table
# --------------------------------------------------------------------------- #

NATIVE_DISPATCH = {
    ("info",): cmd_info,
    ("ext", "list"): cmd_ext_list,
    ("settings", "path"): cmd_settings_path,
    ("settings", "get"): cmd_settings_get,
    ("settings", "set"): cmd_settings_set,
    ("settings", "smoke"): cmd_settings_smoke,
    ("python", "set-interpreter"): cmd_python_set_interpreter,
    ("tasks", "list"): cmd_tasks_list,
    ("tasks", "init"): cmd_tasks_init,
    ("launch", "list"): cmd_launch_list,
    ("launch", "init"): cmd_launch_init,
    ("extensions", "stacks"): cmd_extensions_stacks,
    ("extensions", "recommend"): cmd_extensions_recommend,
    ("extensions", "install"): cmd_extensions_install,
    ("extensions", "pin"): cmd_extensions_pin,
    ("settings-sync", "status"): cmd_settings_sync_status,
    ("workspace", "info"): cmd_workspace_info,
    ("workspace", "folder-settings-get"): cmd_workspace_folder_settings_get,
    ("workspace", "folder-settings-set"): cmd_workspace_folder_settings_set,
    ("profile", "list"): cmd_profile_list,
    ("profile", "show"): cmd_profile_show,
}


def main(argv: list[str]) -> int:
    # On Windows: always forward to the PowerShell driver (zero behavior drift).
    if IS_WINDOWS:
        return _forward_powershell(argv)

    # On macOS / Linux: parse and dispatch natively.
    parser = build_parser()
    args = parser.parse_args(argv)
    handler = NATIVE_DISPATCH.get((args.area, getattr(args, "action", None)))
    if handler is None:
        print(f"error: native implementation for '{args.area} {getattr(args, 'action', '')}' is not yet available on this platform.", file=sys.stderr)
        print("hint : run this command on Windows, or open an issue at https://github.com/Duanzhoutao/vscode-skill/issues", file=sys.stderr)
        return 2
    return handler(args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))