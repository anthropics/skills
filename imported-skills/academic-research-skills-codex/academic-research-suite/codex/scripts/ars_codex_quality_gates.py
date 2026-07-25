#!/usr/bin/env python3
"""Static quality gates for the ARS Codex full-runtime adapter."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Callable


SCRIPT = Path(__file__).resolve()
CODEX_ROOT = SCRIPT.parents[1]
SUITE_ROOT = SCRIPT.parents[2]
ARS_ROOT = SUITE_ROOT / "ars"
PLUGIN_ROOT_CANDIDATE = SUITE_ROOT.parents[1]
PLUGIN_ROOT = (
    PLUGIN_ROOT_CANDIDATE
    if (PLUGIN_ROOT_CANDIDATE / ".codex-plugin" / "plugin.json").is_file()
    else SUITE_ROOT.parents[1] / "plugins" / "academic-research-skills"
)
FULL_RUNTIME_MANIFEST = CODEX_ROOT / "full-runtime-manifest.json"
PACKAGE_MANIFEST = SUITE_ROOT / "manifest.json"
HOOK_PACK = CODEX_ROOT / "hooks" / "hooks.json"

FORBIDDEN_HOOK_PATTERNS = (
    r"\benv\b",
    r"\bprintenv\b",
    r"\bexport\b",
    r"\bcurl\b",
    r"\bwget\b",
    r"\brm\b",
    r"\bmv\b",
    r"\bcp\b",
    r"\bsudo\b",
    r"\bchmod\b",
    r"\bchown\b",
    r">",
    r"\|\s*sh\b",
    r"\|\s*bash\b",
    r"\.ssh",
    r"ANTHROPIC_API_KEY",
    r"OPENAI_API_KEY",
)


class GateFailure(RuntimeError):
    pass


def _json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_manifest_path(value: str) -> Path:
    path = Path(value)
    if path.parts and path.parts[0] == "skills":
        return SUITE_ROOT.parents[1] / path
    return SUITE_ROOT / path


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise GateFailure(message)


def check_manifest() -> list[str]:
    manifest = _json(FULL_RUNTIME_MANIFEST)
    messages = ["full-runtime manifest parses as JSON"]

    package = _json(PACKAGE_MANIFEST)
    adapter_version = package.get("adapter_version")
    skill_match = re.search(
        r'(?m)^\s+version:\s*"([^"]+)"\s*$',
        (SUITE_ROOT / "SKILL.md").read_text(encoding="utf-8"),
    )
    _require(bool(skill_match), "root SKILL.md metadata version is missing")
    _require(
        skill_match.group(1) == adapter_version,
        f"SKILL.md version {skill_match.group(1)!r} != adapter version {adapter_version!r}",
    )
    plugin_version = _json(PLUGIN_ROOT / ".codex-plugin" / "plugin.json").get("version")
    _require(
        plugin_version == adapter_version,
        f"Desktop plugin version {plugin_version!r} != adapter version {adapter_version!r}",
    )
    repo_version_path = SUITE_ROOT.parents[1] / "VERSION"
    if repo_version_path.is_file():
        repo_version = repo_version_path.read_text(encoding="utf-8").strip()
        _require(
            repo_version == adapter_version,
            f"repo VERSION {repo_version!r} != adapter version {adapter_version!r}",
        )
    messages.append(f"package version {adapter_version} is aligned across skill, manifest, plugin, and VERSION")

    for key, value in manifest["paths"].items():
        if key in {"adapter_root"}:
            continue
        path = _resolve_manifest_path(value)
        _require(path.exists(), f"manifest path missing for {key}: {value}")
    messages.append("declared adapter paths exist")

    aliases: set[str] = set()
    for command in manifest["commands"]:
        for alias in command["aliases"]:
            _require(alias not in aliases, f"duplicate alias: {alias}")
            aliases.add(alias)
        recipe = SUITE_ROOT / command["recipe"]
        _require(recipe.exists(), f"command recipe missing: {command['recipe']}")
    for required in (
        "ars-reviewer",
        "ars-mark-read",
        "ars-unmark-read",
        "ars-cache-invalidate",
        "ars-3w",
        "ars-rebuttal-audit",
        "ars-full",
        "ars-plan",
        "ars-lit-review",
    ):
        _require(required in aliases, f"required alias absent: {required}")
    messages.append(f"{len(manifest['commands'])} command routes have recipes")

    for name, workflow in manifest["workflows"].items():
        workflow_path = SUITE_ROOT / workflow["workflow_path"]
        _require(workflow_path.exists(), f"workflow path missing for {name}: {workflow['workflow_path']}")
        template = SUITE_ROOT / workflow["agent_template"]
        _require(template.exists(), f"agent template missing for {name}: {workflow['agent_template']}")
    messages.append(f"{len(manifest['workflows'])} workflows have templates")
    return messages


def check_single_root_skill() -> list[str]:
    root_skill = SUITE_ROOT / "SKILL.md"
    _require(root_skill.exists(), "root SKILL.md missing")
    vendored_skill_files = sorted(ARS_ROOT.rglob("SKILL.md"))
    _require(not vendored_skill_files, "vendored workflow SKILL.md files would expose duplicate Codex skills: " + ", ".join(str(p) for p in vendored_skill_files))
    workflow_files = sorted(ARS_ROOT.glob("*/WORKFLOW.md"))
    workflow_names = {path.parent.name for path in workflow_files}
    expected = {"deep-research", "academic-paper", "academic-paper-reviewer", "academic-pipeline", "experiment-agent"}
    _require(expected.issubset(workflow_names), f"missing WORKFLOW.md files: {sorted(expected - workflow_names)}")
    return ["single root skill is the only Codex-discoverable skill", f"{len(workflow_files)} vendored workflow entry files use WORKFLOW.md"]


def check_hook_safety() -> list[str]:
    pack = _json(HOOK_PACK)
    _require(pack.get("default_enabled") is False, "hook pack must be disabled by default")
    _require(pack.get("enabled_when") == "ARS_CODEX_HOOKS=1", "hook pack must require ARS_CODEX_HOOKS=1")
    hooks = pack.get("hooks", [])
    _require(isinstance(hooks, list), "hooks must be a list")
    for hook in hooks:
        _require(hook.get("mutates_files") is False, f"hook mutates files: {hook.get('id')}")
        command = hook.get("command", "")
        _require(command.startswith("python3 "), f"hook command must use python3 wrapper: {command}")
        _require("ars_codex_hook.py" in command, f"hook command must use adapter hook wrapper: {command}")
        for pattern in FORBIDDEN_HOOK_PATTERNS:
            _require(not re.search(pattern, command), f"unsafe hook command pattern {pattern!r}: {command}")
    return [f"{len(hooks)} hook command(s) are disabled-by-default and pass static safety checks"]


def check_reviewer_fixture(fixture: Path | None = None) -> list[str]:
    fixture = fixture or CODEX_ROOT / "tests" / "fixtures" / "reviewer_full_independent_sections.md"
    text = fixture.read_text(encoding="utf-8")
    required = [
        "## Independent Reviewer: Methodology",
        "## Independent Reviewer: Domain",
        "## Independent Reviewer: Interdisciplinary",
        "## Independent Reviewer: Devil's Advocate",
        "## Editorial Synthesis",
    ]
    positions = []
    for heading in required:
        position = text.find(heading)
        _require(position >= 0, f"reviewer fixture missing heading: {heading}")
        positions.append(position)
    _require(positions == sorted(positions), "editorial synthesis must appear after independent reviewer sections")
    synthesis = text[positions[-1]:]
    for marker in ("methodology concern retained", "domain concern retained", "devil's advocate dissent retained"):
        _require(marker in synthesis, f"synthesis dropped minority marker: {marker}")
    return ["paper-reviewer full-mode fixture preserves independent reviewer sections before synthesis"]


def check_upstream_lock() -> list[str]:
    package = _json(PACKAGE_MANIFEST)
    sources = {item["name"]: item for item in package["source_repositories"]}
    ars = sources.get("academic-research-skills")
    _require(bool(ars), "package manifest missing academic-research-skills source")
    commit = ars.get("commit", "")
    _require(bool(re.fullmatch(r"[0-9a-f]{40}", commit)), f"academic-research-skills lock is not a full SHA: {commit}")
    included = set(ars.get("included_paths", []))
    for path in ("commands", "hooks", "tests", "docs", "shared", "scripts"):
        _require(path in included or any(path in item for item in included), f"included_paths missing {path}")
    return [f"upstream lock pins academic-research-skills@{commit[:7]}"]


def check_desktop_plugin_bundle() -> list[str]:
    plugin_manifest = PLUGIN_ROOT / ".codex-plugin" / "plugin.json"
    plugin_skills = PLUGIN_ROOT / "skills"
    suite_entry = plugin_skills / "academic-research-suite"
    skill_md = suite_entry / "SKILL.md"
    package_manifest = suite_entry / "manifest.json"

    _require(plugin_manifest.is_file(), f"Desktop plugin manifest missing: {plugin_manifest}")
    manifest = _json(plugin_manifest)
    _require(manifest.get("skills") == "./skills/", "Desktop plugin manifest must point at ./skills/")
    _require(plugin_skills.exists(), f"Desktop plugin skills path missing: {plugin_skills}")
    _require(plugin_skills.is_dir(), "Desktop plugin skills path must be a directory")
    _require(not plugin_skills.is_symlink(), "Desktop plugin skills path must not be a symlink")
    _require(suite_entry.is_dir(), "Desktop plugin bundle must include academic-research-suite")
    _require(skill_md.is_file(), "Desktop plugin bundle academic-research-suite is missing SKILL.md")
    _require(package_manifest.is_file(), "Desktop plugin bundle academic-research-suite is missing manifest.json")

    symlinks = sorted(
        str(path.relative_to(PLUGIN_ROOT))
        for path in plugin_skills.rglob("*")
        if path.is_symlink()
    )
    _require(
        not symlinks,
        "Desktop plugin bundle must not contain symlinks: " + ", ".join(symlinks[:20]),
    )

    ignored_names = {".DS_Store", "__pycache__"}

    def materialized_files(root: Path) -> dict[str, Path]:
        return {
            path.relative_to(root).as_posix(): path
            for path in root.rglob("*")
            if path.is_file()
            and not any(part in ignored_names for part in path.relative_to(root).parts)
            and path.suffix != ".pyc"
        }

    if suite_entry.resolve() != SUITE_ROOT.resolve():
        canonical = materialized_files(SUITE_ROOT)
        bundled = materialized_files(suite_entry)
        missing = sorted(canonical.keys() - bundled.keys())
        extra = sorted(bundled.keys() - canonical.keys())
        changed = sorted(
            rel_path
            for rel_path in canonical.keys() & bundled.keys()
            if canonical[rel_path].read_bytes() != bundled[rel_path].read_bytes()
        )
        _require(
            not (missing or extra or changed),
            "Desktop plugin bundle differs from canonical skill: "
            f"missing={missing[:10]}, extra={extra[:10]}, changed={changed[:10]}",
        )
    return [
        "Desktop plugin bundle uses a materialized skills directory",
        "academic-research-suite is bundled without symlinks",
        "Desktop plugin bundle is byte-identical to the canonical skill",
    ]


GATES: dict[str, Callable[[], list[str]]] = {
    "desktop-plugin-bundle": check_desktop_plugin_bundle,
    "manifest": check_manifest,
    "single-root-skill": check_single_root_skill,
    "hook-safety": check_hook_safety,
    "reviewer-fixture": check_reviewer_fixture,
    "upstream-lock": check_upstream_lock,
}


def run_gate(name: str) -> list[str]:
    return GATES[name]()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gate", choices=sorted([*GATES, "all"]))
    parser.add_argument("--json", action="store_true", help="Emit machine-readable result")
    args = parser.parse_args()

    selected = list(GATES) if args.gate == "all" else [args.gate]
    results: dict[str, Any] = {}
    failed = False
    for name in selected:
        try:
            results[name] = {"ok": True, "messages": run_gate(name)}
        except GateFailure as exc:
            failed = True
            results[name] = {"ok": False, "error": str(exc)}

    if args.json:
        print(json.dumps(results, indent=2, sort_keys=True))
    else:
        for name, result in results.items():
            if result["ok"]:
                print(f"OK {name}: " + "; ".join(result["messages"]))
            else:
                print(f"FAIL {name}: {result['error']}", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
