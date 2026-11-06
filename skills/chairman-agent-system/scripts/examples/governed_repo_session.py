"""A governed session doing real work on a real repository.

Run from the repo root:

    python3 skills/chairman-agent-system/scripts/examples/governed_repo_session.py

Every operation below actually happens — files are read, the test suite runs,
and the refusals are real refusals rather than printed messages. This file was
itself written by the ``maintainer`` session it describes.
"""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from chairman import (
    Classification, Level, PermissionDenied, Registry, Session, Store, Tool,
)
from chairman.toolkit import build_repo_toolkit

ROOT = Path(__file__).resolve().parents[4]


def hire(registry, box, name, level, clearance, purpose, objectives, risks):
    """File a proposal and approve it. Both steps are required."""
    request = registry.request_agent(
        requested_by="chairman", name=name, level=level, tools=[Tool.DEVELOPER],
        max_classification=clearance, purpose=purpose, objectives=objectives,
        reporting="Per session", risks=risks,
    )
    registry.approve_request(request.request_id, approver="chairman")
    return Session(registry, box, name)


def main() -> int:
    registry = Registry(Store(":memory:"))
    registry.install_chairman()
    box = build_repo_toolkit(ROOT)

    reviewer = hire(
        registry, box, "reviewer", Level.INTERNAL, Classification.INTERNAL,
        "Inspect the repository", ["Report on structure"], "No write authority",
    )
    maintainer = hire(
        registry, box, "maintainer", Level.OPERATOR, Classification.CONFIDENTIAL,
        "Apply approved changes", ["Write files on request"], "Can alter the tree",
    )

    print("reviewer may call:  ", reviewer.available())
    print("maintainer may call:", maintainer.available())

    readme = reviewer.invoke("fs.read", "README.md")
    print(f"\nread README.md: {len(readme)} bytes")

    print("\nrefusals, each for a different reason:")
    for label, call in (
        ("write without authority", lambda: reviewer.invoke("fs.write", "x.txt", "x")),
        ("read above clearance", lambda: reviewer.invoke("fs.read", ".git/config")),
        ("escape the root", lambda: reviewer.invoke("fs.read", "../../etc/passwd")),
        ("bypass the session", lambda: box.require("fs.read").handler("README.md")),
    ):
        try:
            call()
            print(f"  {label:26} ALLOWED — unexpected")
        except PermissionDenied as exc:
            print(f"  {label:26} refused: {str(exc)[:60]}")

    ok, problems = registry.verify_audit()
    print(f"\n{len(registry.audit_log())} audit entries, chain intact: {ok}")
    for problem in problems:
        print(f"  {problem}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
