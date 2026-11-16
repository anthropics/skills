#!/usr/bin/env python3
"""Check requirement traceability for Spec Driven Development repos.

Standalone version of harness's templates/tools/check-traceability.py, packaged
with the spec-driven-development skill. Same protocol (v1), decoupled from the
harness install layout:

  - specs live under  <specs-dir>/<feature>/  (default `.specs`, was
    `harness/specs`);
  - traceability tables are read from every `*.md` in the feature directory
    (no `feature:` attribution needed — directory scoping replaces it);
  - optional `--impl-glob GLOB` (repeatable) also folds tables from files
    outside the feature directory (e.g. `harness/progress/impl_*.md`); rows in
    those files count for a feature only when the file carries a
    `feature: <name>` attribute line.

For the selected feature(s) the script collects the R<n> identifiers from
requirements.md, merges every traceability table row
(`| R<n> | tests | impl | status |`), and verifies:
  1. every R<n> appears in at least one table row;
  2. every test identifier referenced by a row exists under the tests
     directory (file-name stem, Python function/class, or JS/TS test title;
     `path/to/test.py::name` node ids are verified in both halves).

Requirements whose table Status is not "done" are reported as unresolved
(they do not create gaps).

Usage:
  check_traceability.py --feature NAME [--json] [--root DIR] [--specs-dir DIR]
                        [--tests-dir DIR] [--impl-glob GLOB] ... [root]
  check_traceability.py --all [--json] [--root DIR] [root]

`--root DIR` and the trailing positional root are equivalent.

Exit codes: 0 covered, 1 gaps, 2 usage error.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REQ_RE = re.compile(r"\bR(\d+)\b")
ROW_RE = re.compile(r"^\|\s*(R\d+)\s*\|([^|]*)\|([^|]*)\|([^|]*)\|")
ATTR_RE = re.compile(r"(?im)^\s*feature\s*:\s*([a-z0-9_-]+)\s*$")

MD_GLOB = "*.md"
IMPL_TEST_EXTS = ("*.py", "*.js", "*.mjs", "*.cjs", "*.ts", "*.tsx", "*.mts", "*.cts")


def find_requirements(specs_dir: Path, feature: str) -> set[str]:
    req_file = specs_dir / feature / "requirements.md"
    if not req_file.is_file():
        return set()
    return {f"R{m}" for m in REQ_RE.findall(req_file.read_text(encoding="utf-8"))}


def _merge_impl_table(
    text: str,
    impl_name: str,
    feature: str | None,
    merged: dict[str, list[str]],
    statuses: dict[str, str],
) -> None:
    """Fold one externally-globbed file's rows into the merged tables (v1.1).

    Attribution: a `feature: <name>` attribute line wins; without one, a file
    named `impl_<feature>.md` is attributed to `<feature>` (harness repos that
    encode ownership in the file name). Anything else is left unattributed and
    its rows are ignored.
    """
    owner = ATTR_RE.search(text)
    if owner is not None:
        if feature is not None and owner.group(1) != feature:
            return
    elif feature is not None:
        stem = impl_name
        if stem.startswith("impl_") and stem.endswith(".md"):
            stem = stem[len("impl_") : -len(".md")]
        if stem != feature:
            statuses.setdefault("__unattributed__", impl_name)
            return
    for line in text.splitlines():
        m = ROW_RE.match(line)
        if m is None:
            continue
        req = m.group(1)
        tests = [t for t in re.split(r"[,\s]+", m.group(2).strip()) if t]
        statuses.setdefault(req, m.group(4).strip())
        merged.setdefault(req, [])
        for t in tests:
            if t not in merged[req]:
                merged[req].append(t)


def collect_tables(
    specs_dir: Path,
    feature: str,
    impl_globs: list[str],
    root: Path,
) -> tuple[dict[str, list[str]], dict[str, str]]:
    """Merge rows from the feature directory plus any --impl-glob matches."""
    merged: dict[str, list[str]] = {}
    statuses: dict[str, str] = {}
    # Feature-directory tables: every *.md belongs to this feature by scope.
    for md in sorted((specs_dir / feature).glob(MD_GLOB)):
        for line in md.read_text(encoding="utf-8").splitlines():
            m = ROW_RE.match(line)
            if m is None:
                continue
            req = m.group(1)
            tests = [t for t in re.split(r"[,\s]+", m.group(2).strip()) if t]
            statuses.setdefault(req, m.group(4).strip())
            merged.setdefault(req, [])
            for t in tests:
                if t not in merged[req]:
                    merged[req].append(t)
    # Externally globbed tables (harness-style impl_* files): attribution rule.
    for pattern in impl_globs:
        for impl in sorted(root.glob(pattern)):
            if not impl.is_file():
                continue
            _merge_impl_table(
                impl.read_text(encoding="utf-8"), impl.name, feature, merged, statuses
            )
    return merged, statuses


def _node_id_exists(root: Path, identifier: str) -> bool:
    """Exact node id `path/to/test_file.py::test_name` — verify both halves."""
    import ast

    rel, _, name = identifier.rpartition("::")
    tf = root / rel
    if not tf.is_file():
        return False
    try:
        tree = ast.parse(tf.read_text(encoding="utf-8", errors="replace"))
    except SyntaxError:
        return False
    return any(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        and node.name == name
        for node in ast.walk(tree)
    )


def _py_file_defines(tf: Path, identifier: str) -> bool:
    """Stem match, or an ast FunctionDef/AsyncFunctionDef/ClassDef named `identifier`."""
    import ast

    if tf.stem == identifier:
        return True
    try:
        tree = ast.parse(tf.read_text(encoding="utf-8", errors="replace"))
    except SyntaxError:
        return False
    return any(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        and node.name == identifier
        for node in ast.walk(tree)
    )


def _py_tests_define(tests_dir: Path, identifier: str) -> bool:
    for tf in tests_dir.rglob("*.py"):
        if _py_file_defines(tf, identifier):
            return True
    return False


def _js_tests_mention(tests_dir: Path, pat: "re.Pattern[str]") -> bool:
    for ext in IMPL_TEST_EXTS[1:]:
        for tf in tests_dir.rglob(ext):
            try:
                if pat.search(tf.read_text(encoding="utf-8", errors="replace")):
                    return True
            except OSError:
                continue
    return False


def _search_tests_dir(tests_dir: Path, identifier: str) -> bool:
    """File-name stem, python function/class, or JS/TS test title matching."""
    if not tests_dir.is_dir():
        return False
    if _py_tests_define(tests_dir, identifier):
        return True
    # JS/TS test stacks (node:test, vitest, jest): match inside a test()/it() title.
    pat = re.compile(
        rf"(?:^|[^A-Za-z0-9_])(?:test|it)\s*\(\s*['\"`][^'\"`]*{re.escape(identifier)}"
    )
    return _js_tests_mention(tests_dir, pat)


def test_identifier_exists(root: Path, tests_dir: Path, identifier: str) -> bool:
    ident = identifier.strip()
    if "::" in ident:
        return _node_id_exists(root, ident)
    return _search_tests_dir(tests_dir, ident)


def check_feature(
    root: Path, feature: str, specs_dir: Path, tests_dir: Path, impl_globs: list[str]
) -> dict:
    requirements = find_requirements(specs_dir, feature)
    tables, statuses = collect_tables(specs_dir, feature, impl_globs, root)
    gaps: list[dict[str, str]] = []
    covered = 0
    for req in sorted(requirements, key=lambda r: int(r[1:])):
        tests = tables.get(req)
        if not tests:
            gaps.append(
                {
                    "requirement": req,
                    "reason": "not present in any traceability table",
                }
            )
            continue
        missing = [t for t in tests if not test_identifier_exists(root, tests_dir, t)]
        if missing:
            gaps.append(
                {
                    "requirement": req,
                    "reason": f"test identifier(s) not found under {tests_dir}: {', '.join(missing)}",
                }
            )
            continue
        covered += 1
    unresolved = [
        req
        for req in sorted(requirements, key=lambda r: int(r[1:]))
        if req in statuses and statuses[req] != "done"
    ]
    return {
        "name": feature,
        "requirements": len(requirements),
        "covered": covered,
        "gaps": gaps,
        "unresolved": unresolved,
    }


class UsageError(Exception):
    """Raised for malformed CLI usage; main prints it and exits 2."""


KNOWN_FLAGS = ("--json", "--all", "--feature", "--root", "--specs-dir", "--tests-dir", "--impl-glob")


def _take_value(flag: str, remaining: list[str]) -> list[str]:
    """Remove every `flag <value>` occurrence; return the collected values."""
    values: list[str] = []
    while flag in remaining:
        i = remaining.index(flag)
        if i + 1 >= len(remaining):
            raise UsageError(f"{flag} requires a value")
        values.append(remaining[i + 1])
        del remaining[i : i + 2]
    return values


def parse_args(argv: list[str]) -> "tuple[bool, bool, str | None, Path, Path, Path, list[str]] | int":
    """Parse CLI flags or return exit code 2 on malformed usage."""
    try:
        as_json = "--json" in argv
        all_features = "--all" in argv
        remaining = list(argv)
        feature_values = _take_value("--feature", remaining)
        root_values = _take_value("--root", remaining)
        specs_values = _take_value("--specs-dir", remaining)
        tests_values = _take_value("--tests-dir", remaining)
        impl_globs = _take_value("--impl-glob", remaining)
        if len(feature_values) > 1 or len(root_values) > 1:
            raise UsageError("--feature/--root accept a single value")
        feature = feature_values[0] if feature_values else None
        if len(specs_values) > 1 or len(tests_values) > 1:
            raise UsageError("--specs-dir/--tests-dir accept a single value")
        unknown = [a for a in remaining if a.startswith("-") and a not in KNOWN_FLAGS]
        if unknown:
            raise UsageError(f"unknown argument: {unknown[0]}")
        positional = [a for a in remaining if not a.startswith("-")]
        if root_values:
            root = Path(root_values[0])
        elif positional:
            root = Path(positional[-1])
        else:
            root = Path.cwd()
        specs_dir = Path(specs_values[0]) if specs_values else root / ".specs"
        tests_dir = Path(tests_values[0]) if tests_values else root / "tests"
        if not all_features and feature is None:
            raise UsageError(
                "usage: check_traceability.py --all | --feature NAME [--json] [root]"
            )
    except UsageError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return as_json, all_features, feature, root, specs_dir, tests_dir, impl_globs


def _selected_features(specs_dir: Path) -> list[str]:
    """Feature directories under specs_dir that contain requirements.md."""
    if not specs_dir.is_dir():
        return []
    return sorted(
        p.name
        for p in specs_dir.iterdir()
        if p.is_dir() and (p / "requirements.md").is_file()
    )


def _validate_root(root: Path) -> int:
    """2 with an error message when `root` is not a directory; 0 otherwise."""
    if root.is_dir():
        return 0
    print(
        f"error: root is not a directory: {root}\n"
        "       (a bare file path is NOT a root; use --feature NAME or --all "
        "from the repo root)",
        file=sys.stderr,
    )
    return 2


def _feature_names(
    all_features: bool, feature: str | None, specs_dir: Path
) -> "list[str] | None":
    """Features to check, or None when the request is unusable (error printed)."""
    if all_features:
        names = _selected_features(specs_dir)
        if not names:
            print(
                f"error: no feature directories with requirements.md under {specs_dir}",
                file=sys.stderr,
            )
            return None
        return names
    if not (specs_dir / feature / "requirements.md").is_file():
        print(f"error: unknown feature (no requirements.md): {feature}", file=sys.stderr)
        return None
    return [feature]


def _emit(results: "list[dict]", verdict: str, as_json: bool) -> None:
    if as_json:
        print(
            json.dumps(
                {
                    "tool": "check-traceability",
                    "protocol": 1,
                    "verdict": verdict,
                    "features": results,
                }
            )
        )
    else:
        for r in results:
            print(f"## {r['name']}: {r['covered']}/{r['requirements']} requirements covered")
            for g in r["gaps"]:
                print(f"  [GAP] {g['requirement']}: {g['reason']}")
            for u in r["unresolved"]:
                print(f"  [UNRESOLVED] {u}: table status is not done")
        print(f"VERDICT: {verdict}")


def main(argv: list[str]) -> int:
    parsed = parse_args(argv)
    if isinstance(parsed, int):
        return parsed
    as_json, all_features, feature, root, specs_dir, tests_dir, impl_globs = parsed

    code = _validate_root(root)
    if code:
        return code
    names = _feature_names(all_features, feature, specs_dir)
    if names is None:
        return 2

    results = [
        check_feature(root, n, specs_dir, tests_dir, impl_globs) for n in names
    ]
    empty = [r["name"] for r in results if r["requirements"] == 0]
    if empty:
        print(
            f"error: no requirements parsed for: {', '.join(empty)} (nothing to verify)",
            file=sys.stderr,
        )
        return 2
    verdict = "PASS" if all(r["gaps"] == [] for r in results) else "FAIL"

    _emit(results, verdict, as_json)
    return 0 if verdict == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
