"""Shared utilities for git-flow-agent-guard scripts."""
import fnmatch
import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List, cast


def run_cmd(cmd: str) -> str:
    """Run shell command and return stdout stripped."""
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"Command failed: {cmd}\n{result.stderr}")
    return result.stdout.strip()


def ensure_log_dir() -> Path:
    """Ensure .agent-guard/logs exists and return Path."""
    log_dir = Path(".agent-guard") / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    return log_dir


def load_config() -> Dict[str, Any]:
    """Load .agent-guard.json from repo root."""
    config_path = Path(".agent-guard.json")
    if not config_path.exists():
        return {}
    with open(config_path, encoding="utf-8") as f:
        return cast(Dict[str, Any], json.load(f))


def get_git_diff_stat(target_branch: str) -> str:
    """Get git diff --stat output vs target branch."""
    return run_cmd(f"git diff {target_branch} --stat")


def get_changed_files(target_branch: str) -> List[str]:
    """Get list of changed files vs target branch."""
    output = run_cmd(f"git diff {target_branch} --name-only")
    return [f for f in output.splitlines() if f]


def calculate_revert_cost(changed_files: List[str], config: Dict[str, Any]) -> str:
    """Calculate revert cost based on file patterns in config."""
    patterns = config.get("risk", {}).get("revert_cost_patterns", {})

    high_patterns = patterns.get("HIGH", [])
    medium_patterns = patterns.get("MEDIUM", [])

    for f in changed_files:
        for pattern in high_patterns:
            if fnmatch.fnmatch(f, pattern) or any(fnmatch.fnmatch(part, pattern) for part in Path(f).parts):
                return "HIGH"

    for f in changed_files:
        for pattern in medium_patterns:
            if fnmatch.fnmatch(f, pattern) or any(fnmatch.fnmatch(part, pattern) for part in Path(f).parts):
                return "MEDIUM"

    return "LOW"


def calculate_risk_scores(files_changed: int) -> tuple[int, int]:
    """Calculate dev_risk and main_risk from file count."""
    dev_risk = min(5, max(1, files_changed // 3 + 1))
    main_risk = min(5, dev_risk + 1)
    return dev_risk, main_risk


def calculate_blast_radius(files_changed: int) -> str:
    """Calculate blast radius from file count."""
    if files_changed > 10:
        return "HIGH"
    elif files_changed > 4:
        return "MEDIUM"
    return "LOW"


def auto_merge_allowed(dev_risk: int, blast_radius: str, revert_cost: str, target_branch: str) -> bool:
    """Determine if auto-merge is allowed per SKILL.md matrix."""
    # main branch never auto-merges per SKILL.md
    if target_branch == "main":
        return False

    if dev_risk <= 3:
        return True
    if dev_risk == 4 and blast_radius == "LOW" and revert_cost == "LOW":
        return True
    return False


def write_log(log_dir: Path, filename: str, content: str) -> Path:
    """Write log file and return path."""
    log_path = log_dir / filename
    with open(log_path, "w", encoding="utf-8") as f:
        f.write(content)
    return log_path


def run_verification_commands(config: Dict[str, Any]) -> Dict[str, bool]:
    """Run all configured verification commands. Returns dict of command->success."""
    verification = config.get("verification", {})
    results = {}

    for name, cmd in verification.items():
        if not cmd:
            results[name] = True  # Skip if not configured
            continue
        try:
            run_cmd(cmd)
            results[name] = True
        except RuntimeError:
            results[name] = False

    return results
