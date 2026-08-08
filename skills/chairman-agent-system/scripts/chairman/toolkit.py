"""A real toolkit: filesystem and repository tools under governance.

:mod:`chairman.enforcement` provides the mechanism; this provides tools worth
governing. Everything here does actual work — reads real files, runs real
commands — so the refusals are real refusals rather than a demonstration.

Two controls are enforced before any handler runs:

**Every path is confined to a root.** ``..`` traversal, absolute paths
outside the root, and symlinks pointing out of it are refused during
classification, before authorization is even reached. A path the caller
cannot name is a path the caller cannot read.

**Sensitivity is derived from the path.** A credentials file is RESTRICTED
whether or not the caller knew that. Classification is a property of the
data, not a claim the caller makes about it.

    box = build_repo_toolkit(Path("/srv/project"))
    session = Session(registry, box, "reviewer")
    session.invoke("fs.read", "README.md")     # INTERNAL, permitted
    session.invoke("fs.read", ".env")          # RESTRICTED, refused
    session.invoke("fs.read", "../../etc/passwd")  # refused: outside root
"""

from __future__ import annotations

import fnmatch
import subprocess
from pathlib import Path
from typing import List, Optional

from .enforcement import ToolBox
from .errors import PermissionDenied
from .models import Classification, Tool

# Paths matching these are RESTRICTED regardless of who asks. Ordered from
# most to least specific for readability; matching is any-of.
SECRET_PATTERNS = (
    ".env",
    ".env.*",
    "*.pem",
    "*.key",
    "*.p12",
    "*.pfx",
    "id_rsa*",
    "id_ed25519*",
    "*credentials*",
    "*secret*",
    "*.keystore",
    ".netrc",
    ".npmrc",
    ".pypirc",
)

# Version-control internals: not secret by nature, but they carry tokens in
# remote URLs and rewriting them corrupts history.
VCS_PATTERNS = (".git/*", ".git", ".svn/*", ".hg/*")

# Public by intent — the files a project publishes about itself.
PUBLIC_PATTERNS = ("README*", "LICENSE*", "CHANGELOG*", "CONTRIBUTING*", "*.md")


def classify_path(root: Path, raw: str) -> Classification:
    """Sensitivity of a path, and the confinement check.

    Raises :class:`~chairman.errors.PermissionDenied` for anything escaping
    ``root``. Raising here rather than returning RESTRICTED matters: an
    out-of-root path is malformed, not merely sensitive, and an agent with
    RESTRICTED clearance should still not be able to read ``/etc/shadow``.
    """
    root = root.resolve()
    candidate = (root / raw).resolve() if not Path(raw).is_absolute() else Path(raw).resolve()

    try:
        relative = candidate.relative_to(root)
    except ValueError:
        raise PermissionDenied(
            f"path escapes the governed root: {raw!r} resolves outside {root}"
        ) from None

    rel_text = str(relative)
    parts = relative.parts
    name = candidate.name

    for pattern in SECRET_PATTERNS:
        if fnmatch.fnmatch(name, pattern) or fnmatch.fnmatch(rel_text, pattern):
            return Classification.RESTRICTED

    for pattern in VCS_PATTERNS:
        if fnmatch.fnmatch(rel_text, pattern) or (parts and parts[0] == pattern.split("/")[0]):
            return Classification.CONFIDENTIAL

    for pattern in PUBLIC_PATTERNS:
        if fnmatch.fnmatch(name, pattern):
            return Classification.PUBLIC

    return Classification.INTERNAL


def _safe_path(root: Path, raw: str) -> Path:
    """Resolve inside ``root``. Classification already refused escapes, but
    handlers re-check so they are not reliant on call order."""
    classify_path(root, raw)
    root = root.resolve()
    return (root / raw).resolve() if not Path(raw).is_absolute() else Path(raw).resolve()


def build_repo_toolkit(
    root: Path,
    box: Optional[ToolBox] = None,
    *,
    test_command: Optional[List[str]] = None,
    timeout: int = 120,
) -> ToolBox:
    """Register filesystem and repository tools scoped to ``root``.

    Returns the toolbox so it can be composed with other registrations.
    ``test_command`` defaults to the stdlib unittest discovery this package
    uses; pass your own for other projects.
    """
    root = Path(root).resolve()
    if not root.is_dir():
        raise ValueError(f"root is not a directory: {root}")

    box = box or ToolBox()
    test_command = test_command or ["python3", "-m", "unittest", "discover", "-s", "tests", "-t", "."]

    def path_classifier(path: str, *_args, **_kwargs) -> Classification:
        return classify_path(root, path)

    @box.register("fs.list", Tool.DEVELOPER, path_classifier)
    def fs_list(path: str = ".") -> List[str]:
        """Names in a directory, sorted, directories marked with a slash."""
        target = _safe_path(root, path)
        if not target.is_dir():
            raise NotADirectoryError(f"not a directory: {path}")
        return sorted(
            f"{p.name}/" if p.is_dir() else p.name for p in target.iterdir()
        )

    @box.register("fs.read", Tool.DEVELOPER, path_classifier)
    def fs_read(path: str, max_bytes: int = 200_000) -> str:
        target = _safe_path(root, path)
        if not target.is_file():
            raise FileNotFoundError(f"not a file: {path}")
        data = target.read_bytes()[:max_bytes]
        return data.decode("utf-8", errors="replace")

    @box.register("fs.write", Tool.DEVELOPER, path_classifier, writes=True)
    def fs_write(path: str, content: str) -> str:
        target = _safe_path(root, path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)
        return f"wrote {len(content)} bytes to {path}"

    @box.register("repo.status", Tool.DEVELOPER, Classification.INTERNAL)
    def repo_status() -> str:
        result = subprocess.run(
            ["git", "status", "--short"],
            cwd=root, capture_output=True, text=True, timeout=timeout,
        )
        return result.stdout.strip() or "(clean)"

    @box.register("repo.diff", Tool.DEVELOPER, Classification.INTERNAL)
    def repo_diff(path: str = "") -> str:
        cmd = ["git", "diff"] + ([path] if path else [])
        result = subprocess.run(
            cmd, cwd=root, capture_output=True, text=True, timeout=timeout
        )
        return result.stdout.strip() or "(no changes)"

    @box.register("test.run", Tool.DEVELOPER, Classification.INTERNAL)
    def test_run() -> str:
        result = subprocess.run(
            test_command, cwd=root, capture_output=True, text=True, timeout=timeout
        )
        tail = (result.stderr or result.stdout).strip().splitlines()[-4:]
        return f"exit {result.returncode}\n" + "\n".join(tail)

    return box


__all__ = [
    "PUBLIC_PATTERNS",
    "SECRET_PATTERNS",
    "VCS_PATTERNS",
    "build_repo_toolkit",
    "classify_path",
]
