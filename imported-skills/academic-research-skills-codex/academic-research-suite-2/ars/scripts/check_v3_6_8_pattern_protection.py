#!/usr/bin/env python3
"""ARS v3.7.1 byte-equivalence SHA gate + Step 3a Two-Layer Citation Emission invariants.

Spec: docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md
      § Step 0 — Lint manifest separation (round-1 codex F-004 amend)
      § Step 3a — Two-Layer Citation Emission (uniform across all modes)

Two layers of enforcement:

1. v3.6.7 boundary SHA gate (Step 0): byte-equivalence on v3.6.7-tagged
   PATTERN PROTECTION blocks listed in scripts/v3_6_7_inversion_manifest.json.
2. v3.6.8 Step 3a invariants on the "Two-Layer Citation Emission (v3.7.1)"
   prompt block in each agent listed in scripts/v3_6_8_inversion_manifest.json:
   (i)   the block specifies the two-layer citation form using a literal
         `<!--ref:` HTML-comment marker AND `<author-year>` visible-form prose
   (ii)  the block does NOT mention "finalizer", "orchestrator", or "stage gate"
         (strict partial-inversion: agent must not know about resolver layers)
   (iii) the block does NOT instruct the agent to read frontmatter

Boundary rule (per spec):
- v3.7.1 work does NOT modify the v3.6.7-tagged PATTERN PROTECTION blocks in
  synthesis_agent.md / research_architect_agent.md / report_compiler_agent.md.
- v3.7.1 MAY add new prompt sections (e.g. "Two-Layer Citation Emission")
  OUTSIDE those v3.6.7-tagged blocks; those v3.6.8-tagged invariants ride
  this script's own manifest (scripts/v3_6_8_inversion_manifest.json).

Single source of truth (round-4 R4-002 + round-5 R5-001 + round-6 R6-002):
- The v3.6.7 frozen manifest at scripts/v3_6_7_inversion_manifest.json is the
  single source of truth for the protected file LIST.
- The v3.6.7 protected CONTENT is whatever the v3.6.7-tagged block shows at
  the v3.6.7 manifest's most recent modifying commit (derived via
  `git log -1 --format=%H scripts/v3_6_7_inversion_manifest.json`).
- v3.7.1 lint computes SHA on demand at runtime: hash(block at PR HEAD) ==
  hash(block at v3.6.7 base commit). No stored expected SHAs; no dual truth.

Shallow-clone safety (round-6 R6-002 + round-7 R7-001):
- `actions/checkout@v4` defaults to fetch-depth: 1 in CI; that would render
  `git log -1` vacuous. This lint detects shallow clones and either fetches
  --unshallow against the default branch or hard-fails with a fix-it message.

Exit codes: 0 on pass, 1 on any failure (including shallow-clone refusal).
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# Reuse v3.6.7 lint's heading-based block extractor for byte-equivalence.
# The extractor must be byte-equivalent between the two lints; the spec
# explicitly requires the SHARED function (see spec § Step 0 line ~389:
# "The extractor is the byte-equivalent function shared between v3.6.7 lint
# and v3.7.1 lint to guarantee identical results").
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_v3_6_7_pattern_protection import (  # noqa: E402
    PROTECTION_BLOCK as V3_6_7_PROTECTION_BLOCK,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
V3_6_7_MANIFEST = REPO_ROOT / "scripts" / "v3_6_7_inversion_manifest.json"
V3_6_8_MANIFEST = REPO_ROOT / "scripts" / "v3_6_8_inversion_manifest.json"
CODEX_BASELINE = REPO_ROOT / "scripts" / "codex_v3_6_7_block_baseline.json"

# Byte-order mark stripped per spec § Step 0: "the file's BOM (if any) is
# excluded; trailing whitespace of the last block line is preserved".
_BOM = b"\xef\xbb\xbf"


def _run_git(args: list[str], cwd: Path = REPO_ROOT) -> tuple[int, str, str]:
    """Run git and return (returncode, stdout, stderr) as decoded strings."""
    result = subprocess.run(
        ["git", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
    )
    return result.returncode, result.stdout.strip(), result.stderr.strip()


def _resolve_default_branch() -> tuple[str | None, str | None]:
    """Resolve the repo's default branch via the spec's three-step ladder.

    (1) `git symbolic-ref --quiet --short refs/remotes/origin/HEAD` → strip 'origin/'
    (2) `$GITHUB_DEFAULT_BRANCH` env (GitHub Actions fallback)
    (3) None — caller must hard-fail.
    """
    rc, out, _ = _run_git(["symbolic-ref", "--quiet", "--short", "refs/remotes/origin/HEAD"])
    if rc == 0 and out.startswith("origin/"):
        return out[len("origin/"):], None
    env_default = os.environ.get("GITHUB_DEFAULT_BRANCH")
    if env_default:
        return env_default, None
    return None, (
        "[ARS-V3.7.1 LINT ERROR: default branch unresolvable; clone must "
        "include origin/HEAD or set GITHUB_DEFAULT_BRANCH env]"
    )


def _ensure_full_clone() -> str | None:
    """Return None on success, error string on hard-fail.

    If the repo is a shallow clone, attempt `git fetch --unshallow origin
    <default-branch>` first; if that itself fails, hard-fail.
    """
    rc, out, _ = _run_git(["rev-parse", "--is-shallow-repository"])
    if rc != 0:
        return f"[ARS-V3.7.1 LINT ERROR: cannot determine clone depth: {out!r}]"
    if out.strip().lower() != "true":
        return None  # full clone — proceed
    default_branch, err = _resolve_default_branch()
    if err is not None:
        return err
    rc, out, stderr = _run_git(["fetch", "--unshallow", "origin", default_branch])
    if rc != 0:
        return (
            "[ARS-V3.7.1 LINT ERROR: shallow clone detected; set fetch-depth: "
            f"0 in checkout step before running v3.7.1 byte-equivalence "
            f"check (unshallow attempt failed: {stderr!r})]"
        )
    return None


def _v3_6_7_base_commit() -> tuple[str | None, str | None]:
    """Derive the v3.6.7 base commit via `git log -1` against the v3.6.7 manifest.

    This is the single source of truth derivation per spec § Step 0
    (round-4 R4-002 + round-5 R5-001 + round-6 R6-002 amend; no stored
    base_commit field, no dual truth).
    """
    rc, out, stderr = _run_git([
        "log", "-1", "--format=%H", "--",
        "scripts/v3_6_7_inversion_manifest.json",
    ])
    if rc != 0 or not out:
        return None, (
            "[ARS-V3.7.1 LINT ERROR: cannot derive v3.6.7 base commit "
            f"from `git log -1 -- scripts/v3_6_7_inversion_manifest.json`: "
            f"rc={rc} stderr={stderr!r}]"
        )
    return out.strip(), None


def _detect_pr_base_ref() -> str | None:
    """Return a ref that names the PR's base for anti-self-baseline guard.

    Order: $GITHUB_BASE_REF (CI fast path) → origin/<default-branch> (resolved
    via the same ladder as the shallow-clone safety check). Returns None when
    no remote / default branch is reachable (e.g. detached local check on a
    fork without origin); callers treat that as "skip the guard, fall back to
    derivation alone" — local-only attacks are out of scope (the user can see
    their own diff).
    """
    env_base = os.environ.get("GITHUB_BASE_REF")
    if env_base:
        return f"origin/{env_base}"
    default_branch, _ = _resolve_default_branch()
    if default_branch:
        return f"origin/{default_branch}"
    return None


def _v3_6_7_manifest_unchanged_in_pr() -> tuple[bool, str | None]:
    """Anti-self-baseline guard (round-2 + round-4 codex P2 closure).

    Without this, a PR could mutate `scripts/v3_6_7_inversion_manifest.json`
    AND a v3.6.7-tagged PATTERN PROTECTION block, causing the SHA gate to
    hash modified content against itself.

    Round-2 guard (initial): compare manifest bytes at HEAD vs at
    `merge-base <pr-base> HEAD`; refuse to run on byte-difference.

    Round-4 closure: byte-equality at HEAD is NOT sufficient. A PR with
    commit A (modify manifest + modify protected block) followed by
    commit B (revert manifest to original bytes; leave protected block
    edit) leaves HEAD-vs-base manifest BYTES equal, but `git log -1
    -- manifest` still resolves to commit B as the baseline, and
    `git show B:<protected>` returns the modified content — self-baseline
    attack reappears. Fix: also reject any commit that *touches* the
    manifest in the `merge-base..HEAD` range, regardless of final bytes.

    Returns (True, None) on success or when the guard cannot be evaluated
    (no PR base detectable — local detached state). Returns (False, msg)
    when the manifest changed in the PR or was touched by any PR commit.
    """
    pr_base = _detect_pr_base_ref()
    if pr_base is None:
        # Local-only / detached state: treat as advisory — surface a note but
        # don't block. The CI run will catch the attack.
        return True, None
    rc_mb, mb, _ = _run_git(["merge-base", pr_base, "HEAD"])
    if rc_mb != 0 or not mb:
        # Cannot compute merge-base (fork without origin?). Be conservative:
        # warn but do not block — CI on the canonical repo will catch it.
        return True, None
    mb = mb.strip()
    rel = "scripts/v3_6_7_inversion_manifest.json"

    # Round-4 closure: scan merge-base..HEAD for ANY commit that touches the
    # manifest, regardless of whether the final HEAD bytes equal the base
    # bytes. This catches the "touch and revert" pattern where a PR commit
    # modifies the manifest + a protected block, then a later PR commit
    # reverts only the manifest.
    rc_log, log_out, log_err = _run_git([
        "log", "--format=%H", f"{mb}..HEAD", "--", rel,
    ])
    if rc_log != 0:
        # Couldn't list touching commits — be loud, don't pass silently.
        return False, (
            "[ARS-V3.7.1 LINT ERROR: anti-self-baseline guard cannot list "
            f"manifest-touching commits in {mb[:12]}..HEAD: rc={rc_log} "
            f"stderr={log_err!r}]"
        )
    touching = [c for c in log_out.splitlines() if c.strip()]
    if touching:
        commits_str = ", ".join(c[:12] for c in touching[:5])
        suffix = f" (and {len(touching) - 5} more)" if len(touching) > 5 else ""
        return False, (
            "[ARS-V3.7.1 LINT ERROR: anti-self-baseline guard tripped: "
            f"v3.6.7 manifest touched by {len(touching)} commit(s) in "
            f"{mb[:12]}..HEAD: {commits_str}{suffix}. The byte-equivalence "
            "SHA gate uses the manifest's most recent modifying commit as "
            "its baseline; allowing ANY manifest touch in the PR (even one "
            "later reverted) would let the gate hash modified content "
            "against itself. Land manifest amendments in a SEPARATE PR "
            "under a v3.7+ amendment process so the next SHA gate run "
            "sees the new manifest as its baseline. "
            "(round-2 + round-4 codex P2 closure)]"
        )

    # Defense-in-depth: also verify final HEAD bytes match base bytes.
    # If `git log` somehow under-reports touches (e.g. a corrupted history
    # or a bug in the path filter), the byte comparison still catches the
    # final-state mismatch. This is the round-2 guard, kept as backstop.
    head_path = REPO_ROOT / rel
    head_bytes = head_path.read_bytes() if head_path.exists() else None
    base_bytes, err = _read_blob_at_commit(mb, rel)
    if err is not None:
        return False, (
            "[ARS-V3.7.1 LINT ERROR: anti-self-baseline guard tripped: "
            "v3.6.7 manifest does not exist at PR base commit "
            f"{mb[:12]}. Manifest creation / re-creation is not a "
            "v3.7.1-work-PR action. Land manifest changes in a separate "
            "amendment PR (round-2 codex P2 closure)]"
        )
    if head_bytes is None:
        return False, (
            "[ARS-V3.7.1 LINT ERROR: anti-self-baseline guard tripped: "
            "v3.6.7 manifest is missing at PR HEAD but present at PR base. "
            "Deletion is not a v3.7.1-work-PR action]"
        )
    if head_bytes != base_bytes:
        return False, (
            "[ARS-V3.7.1 LINT ERROR: anti-self-baseline guard tripped: "
            "v3.6.7 manifest bytes differ between HEAD and PR base, but "
            "no commit in merge-base..HEAD lists it as a path. This is a "
            "history-shape anomaly — investigate before proceeding]"
        )
    return True, None


def _strip_file_bom(file_bytes: bytes) -> bytes:
    """Strip a UTF-8 BOM at byte 0 of the FILE, if present.

    Per spec § Step 0 SHA normalization: "the FILE's BOM (if any) is
    excluded". This strips ONLY the file-level BOM, NOT BOMs that may
    appear later in the file (e.g. inserted right before a protected
    heading as a hidden mutation — round-8 codex P2 closure: spec
    exclusion is file-level only, so block-level BOMs must remain in
    the hashed range so heading-prefix attacks like inserting U+FEFF
    before `## PATTERN PROTECTION (v3.6.7)` are caught).
    """
    if file_bytes.startswith(_BOM):
        return file_bytes[len(_BOM):]
    return file_bytes


# Backward-compat alias for the old name used by the unit test that pins
# BOM-stripping behaviour (test renamed in the round-8 closure commit).
_normalize_bytes = _strip_file_bom


def _extract_block_bytes(file_bytes: bytes) -> bytes | None:
    """Extract the v3.6.7 PATTERN PROTECTION block as bytes.

    Spec § 388 canonical range: "start at the line containing
    `## PATTERN PROTECTION (v3.6.7)` heading; end at the line before the
    next H1 / H2 / H3 heading or EOF". The `## ` heading prefix is part
    of the canonical byte range.

    Spec § Step 0 SHA normalization: "bytes are read raw; the FILE's
    BOM (if any) is excluded". File-level BOM stripping happens BEFORE
    extraction (caller passes raw file bytes to this function); BOMs
    that appear later in the file (e.g. inserted before a protected
    heading) are NOT stripped — they're real content mutations the
    gate must detect (round-8 codex P2 closure).

    The v3.6.7 lint's `_extract_block` finds the marker via case-
    insensitive substring match, so it starts the returned slice at
    `PATTERN...` and silently strips the `## ` (or any other) heading
    prefix. That means a mutation of `## PATTERN...` to `### PATTERN...`
    leaves the v3.6.7 lint's extracted block byte-identical, which is
    fine for v3.6.7's invariant greps but DEFEATS the v3.7.1 byte-
    equivalence gate's heading-prefix check (round-3 codex P2 closure).

    This wrapper extends the start of the v3.6.7 extractor's range
    backward to the start of the marker's line, so the hashed bytes
    include the heading prefix exactly as the spec requires. The end
    position and termination logic are untouched, so the byte range
    stays byte-equivalent to the v3.6.7 extractor everywhere except the
    heading prefix.

    Returns None when the marker is missing.
    """
    # Strip file-level BOM (byte 0 only) per spec § Step 0. This is the
    # ONLY BOM-stripping point in the pipeline; block-level BOMs stay in
    # the hashed range (round-8 closure: BOM-before-heading mutation
    # must be caught).
    file_bytes = _strip_file_bom(file_bytes)
    text = file_bytes.decode("utf-8", errors="replace")

    # Round-10 codex P2 closure: do NOT delegate to the v3.6.7 extractor.
    # That extractor uses a substring search (`text.lower().find(marker)`),
    # so when prose before the protected block mentions
    # `PATTERN PROTECTION (v3.6.7)`, it returns the slice starting at the
    # PROSE position. Earlier rounds tried to "correct" by anchoring the
    # heading line afterward and reusing `len(block)`, but the slice
    # length still came from the prose-to-heading fragment, not the real
    # block — so the hashed range was wrong.
    #
    # Round-9 + Round-10 fix: anchor the START at the heading line, AND
    # compute the END independently by searching for the next H1/H2/H3
    # heading after the marker line (or EOF). This mirrors the v3.6.7
    # lint's heading-to-next-heading-or-EOF termination semantics, but
    # with a true heading-anchored start.
    #
    # Pattern: line start, optional indent, 1-3 `#`, whitespace, the marker
    # text. NO `\b` after the marker (ends with `)`, a non-word char).
    # `(?m)` makes `^` match line starts; `(?i)` is the v3.6.7 convention.
    heading_re = re.compile(
        r"(?im)^[ \t]*#{1,3}[ \t]+" + re.escape(V3_6_7_PROTECTION_BLOCK)
    )
    match = heading_re.search(text)
    if match is None:
        # Heading-anchored search found nothing; the marker may exist only
        # as prose (no `#` prefix). Treat as missing.
        return None
    line_start = match.start()

    # Find block end at next H1/H2/H3 heading after the marker LINE, or EOF.
    next_heading_re = re.compile(r"(?m)^[ \t]*#{1,3}[ \t]+")
    eol = text.find("\n", match.end())
    search_start = (eol + 1) if eol >= 0 else len(text)
    next_match = next_heading_re.search(text, pos=search_start)
    block_end = next_match.start() if next_match else len(text)
    block_with_prefix = text[line_start:block_end]
    return block_with_prefix.encode("utf-8")


def _read_blob_at_commit(commit: str, repo_relpath: str) -> tuple[bytes | None, str | None]:
    """Return (raw bytes, error). Uses `git show <commit>:<path>`."""
    result = subprocess.run(
        ["git", "show", f"{commit}:{repo_relpath}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        stderr = result.stderr.decode("utf-8", errors="replace").strip()
        return None, (
            f"[ARS-V3.7.1 LINT ERROR: `git show {commit}:{repo_relpath}` "
            f"failed: {stderr!r}]"
        )
    return result.stdout, None


def _sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _is_codex_distribution() -> bool:
    manifest_path = REPO_ROOT.parent / "manifest.json"
    if not manifest_path.is_file():
        return False
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return False
    return isinstance(manifest, dict) and manifest.get("generated_for") == "codex"


def _load_codex_baseline() -> tuple[dict[str, object] | None, str | None]:
    if not CODEX_BASELINE.exists():
        return None, (
            "[ARS-V3.7.1 LINT ERROR: Codex v3.6.7 block baseline missing at "
            f"{CODEX_BASELINE.relative_to(REPO_ROOT)}]"
        )
    try:
        data = json.loads(CODEX_BASELINE.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return None, f"[ARS-V3.7.1 LINT ERROR: Codex v3.6.7 block baseline unreadable: {exc}]"
    files = data.get("files")
    if not isinstance(files, dict):
        return None, "[ARS-V3.7.1 LINT ERROR: Codex baseline 'files' must be an object]"
    return data, None


def check_codex_byte_equivalence(verbose: bool = True) -> int:
    """Run the v3.6.7 block gate from a bundled baseline in Codex packages.

    The Codex distribution vendors ARS under a nested root, so it does not have
    the upstream ARS git history needed for `git log -1 -- v3_6_7_manifest`.
    The packaged JSON baseline is the explicit substitute for that history.
    """
    baseline, err = _load_codex_baseline()
    if err is not None:
        print(err)
        return 1

    expected_manifest_sha = baseline.get("manifest_sha256")
    if not isinstance(expected_manifest_sha, str):
        print("[ARS-V3.7.1 LINT ERROR: Codex baseline missing manifest_sha256]")
        return 1
    if not V3_6_7_MANIFEST.exists():
        print("[ARS-V3.7.1 LINT ERROR: v3.6.7 manifest missing at PR HEAD]")
        return 1
    current_manifest_sha = _sha256(V3_6_7_MANIFEST.read_bytes())
    if current_manifest_sha != expected_manifest_sha:
        print(
            "[ARS-V3.7.1 LINT ERROR: anti-self-baseline guard tripped: "
            "v3.6.7 manifest bytes differ from the packaged Codex baseline]"
        )
        return 1

    files_v367, err = _load_v3_6_7_manifest()
    if err is not None:
        print(err)
        return 1
    baseline_files = baseline["files"]
    if set(files_v367) != set(baseline_files):
        print(
            "[ARS-V3.7.1 LINT ERROR: Codex baseline file set does not match "
            "scripts/v3_6_7_inversion_manifest.json]"
        )
        return 1

    failures: list[str] = []
    for rel in files_v367:
        head_path = REPO_ROOT / rel
        if not head_path.exists():
            failures.append(
                f"  [{rel}] missing at PR HEAD (deletion of v3.6.7-protected "
                "file would re-open v3.6.7 convergence; restore the file)"
            )
            continue
        head_block = _extract_block_bytes(head_path.read_bytes())
        if head_block is None:
            failures.append(
                f"  [{rel}] PATTERN PROTECTION (v3.6.7) marker missing at "
                "PR HEAD (the v3.6.7-tagged block was renamed or removed; "
                "boundary rule violated — v3.7.1 must NOT mutate v3.6.7 blocks)"
            )
            continue
        expected = baseline_files[rel]
        if not isinstance(expected, dict) or not isinstance(expected.get("block_sha256"), str):
            failures.append(f"  [{rel}] Codex baseline entry is malformed")
            continue
        head_sha = _sha256(head_block)
        base_sha = expected["block_sha256"]
        if head_sha != base_sha:
            failures.append(
                f"  [{rel}] BYTE-EQUIVALENCE FAIL\n"
                f"      HEAD     SHA-256: {head_sha}\n"
                f"      v3.6.7   SHA-256: {base_sha}\n"
                f"      v3.6.7-tagged PATTERN PROTECTION block changed; "
                f"v3.7.1 boundary rule violated. Restore the block or land "
                f"a v3.6.7+ amendment manifest first."
            )
        elif verbose:
            print(f"  [{rel}] PASS (sha256={head_sha[:12]})")

    if failures:
        print("[ARS-V3.7.1 LINT ERROR: v3.6.7 PATTERN PROTECTION block byte-equivalence failures]")
        for line in failures:
            print(line)
        return 1
    if verbose:
        print(f"[v3.7.1 SHA gate] PASSED ({len(files_v367)} v3.6.7 protected file(s))")
    return 0


def _load_v3_6_7_manifest() -> tuple[list[str] | None, str | None]:
    """Read the v3.6.7 manifest and return (file_list, error)."""
    if not V3_6_7_MANIFEST.exists():
        return None, (
            "[ARS-V3.7.1 LINT ERROR: v3.6.7 manifest missing at "
            f"{V3_6_7_MANIFEST.relative_to(REPO_ROOT)}]"
        )
    try:
        data = json.loads(V3_6_7_MANIFEST.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return None, f"[ARS-V3.7.1 LINT ERROR: v3.6.7 manifest unreadable: {exc}]"
    files = data.get("files")
    if not isinstance(files, list) or not all(isinstance(p, str) for p in files):
        return None, (
            "[ARS-V3.7.1 LINT ERROR: v3.6.7 manifest 'files' must be a list "
            "of strings]"
        )
    return files, None


def _load_v3_6_8_manifest() -> tuple[dict | None, str | None]:
    """Read the v3.6.8 manifest. PR-1 ships an empty list; Step 3a populates."""
    if not V3_6_8_MANIFEST.exists():
        return None, (
            "[ARS-V3.7.1 LINT ERROR: v3.6.8 manifest missing at "
            f"{V3_6_8_MANIFEST.relative_to(REPO_ROOT)}]"
        )
    try:
        data = json.loads(V3_6_8_MANIFEST.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return None, f"[ARS-V3.7.1 LINT ERROR: v3.6.8 manifest unreadable: {exc}]"
    if data.get("scope") != "v3.6.8-only":
        return None, (
            "[ARS-V3.7.1 LINT ERROR: v3.6.8 manifest 'scope' must be "
            f"'v3.6.8-only', got {data.get('scope')!r}]"
        )
    files = data.get("files")
    if not isinstance(files, list) or not all(isinstance(p, str) for p in files):
        return None, (
            "[ARS-V3.7.1 LINT ERROR: v3.6.8 manifest 'files' must be a list "
            "of strings (may be empty until Step 3a populates)]"
        )
    return data, None


# =============================================================================
# Step 3a — Two-Layer Citation Emission invariants
# =============================================================================
#
# Spec § Step 3a (line 439): the v3.7.1 lint enforces three invariants on the
# Two-Layer Citation Emission prompt block in each manifest-listed agent:
#   (i)   two-layer form regex on emitted citations in agent test fixtures
#   (ii)  absence of "finalizer / orchestrator / stage gate" prose inside the
#         Two-Layer Citation Emission prompt blocks
#   (iii) absence of any frontmatter-read instruction in those blocks
#
# Block scope: starts at the H2 line `## Two-Layer Citation Emission (v3.7.1)`
# and ends at the next H1/H2/H3 heading or EOF.

TWO_LAYER_BLOCK_HEADING = "## Two-Layer Citation Emission (v3.7.1)"

# Invariant (ii): forbidden terms.
#
# R2 P1-B closure: Python `\b` treats `_` as a word character. That means
# `\bfinalizer\b` does NOT match `cite_provenance_finalizer_agent` (the agent
# name introduced by Step 3c). Step 3a must reject those exact identifiers
# because the spec explicitly forbids naming the downstream resolver layer.
# Use identifier-aware boundaries `(?<![A-Za-z0-9])` / `(?![A-Za-z0-9])`
# instead of `\b` so underscores DO act as a boundary; this catches both
# bare `finalizer` and `cite_provenance_finalizer_agent` substring matches.
_NON_IDENT_BEFORE = r"(?<![A-Za-z0-9])"
_NON_IDENT_AFTER = r"(?![A-Za-z0-9])"
# R3 P1-B closure: plural-aware stems. `finalizers`/`orchestrators`/
# `resolvers`/`stage gates`/`terminal gates` previously slipped past
# because the right identifier boundary rejected the plural `s`.
_FORBIDDEN_RESOLVER_TERMS = (
    re.compile(_NON_IDENT_BEFORE + r"finalizers?" + _NON_IDENT_AFTER, re.IGNORECASE),
    re.compile(_NON_IDENT_BEFORE + r"orchestrators?" + _NON_IDENT_AFTER, re.IGNORECASE),
    re.compile(_NON_IDENT_BEFORE + r"stage[\s\-_]?gates?" + _NON_IDENT_AFTER, re.IGNORECASE),
    re.compile(_NON_IDENT_BEFORE + r"terminal[\s\-_]?gates?" + _NON_IDENT_AFTER, re.IGNORECASE),
    # The block instructs the agent to NOT resolve markers; saying so is
    # legitimate self-knowledge ("emit bare; do not resolve"). It is the
    # MENTION of who DOES resolve that breaks partial-inversion. The token
    # "resolver" referring to a downstream entity is forbidden, but the verb
    # "resolve" used negatively ("never resolve") is allowed — handled by
    # forbidding only the "resolver" noun (and its plural), not the verb.
    re.compile(_NON_IDENT_BEFORE + r"resolvers?" + _NON_IDENT_AFTER, re.IGNORECASE),
)

# Invariant (iii): a frontmatter-read instruction is any imperative or
# descriptive sentence that tells the agent to read / look up / dereference /
# consult an entry's frontmatter. The agent must learn the slug ONLY from the
# corpus context already in its prompt — never from frontmatter.
#
# R1 P1-3 closure: match `frontmatter` AND its common variants (`front matter`
# two-word, `front-matter` hyphenated, and across line wraps in bullet text).
# Whitespace between verb and target spans `\s` (newline + indent) not just
# `[^.\n]`, so a wrapped bullet `read the entry\n  front matter` is caught.
#
# Negation: the block legitimately includes prohibitions like "Never read
# frontmatter" — those must NOT trigger this check. R1 P1-2 closure: bare
# same-sentence presence of any negation word is too permissive; an attacker
# could write `Never guess, read the entry frontmatter` and slip past.
# Negation must scope to the matched read-verb's neighborhood — i.e. the
# negation must appear within ~80 chars BEFORE the verb (or anywhere in the
# verb-and-target span). Implemented as a separate left-context match around
# the verb position rather than a full-sentence wildcard.
_FRONTMATTER_TARGET_RE = (
    r"front[\s\-_]?matter"  # `frontmatter` / `front matter` / `front-matter` / `front_matter`
)
# R3 P1-C closure: identifier-aware boundary on the verb side. Python `\b`
# treats `_` as a word char, so `read_frontmatter()` is one token and
# `\bread\b` does not match. Use `(?<![A-Za-z0-9])` / `(?![A-Za-z0-9])` so
# `_` IS a boundary; this catches `read_frontmatter()` style instructions.
# The target side uses the same boundary for symmetry.
_FRONTMATTER_READ_VERB_RE = re.compile(
    _NON_IDENT_BEFORE + r"(?P<verb>"
    r"read|reads?|reading|"
    r"look\s*up|looks?\s*up|looking\s*up|"
    r"dereference|dereferences?|dereferencing|"
    r"consult|consults?|consulting|"
    r"open|opens?|opening|"
    r"parse|parses?|parsing|"
    r"load|loads?|loading|"
    r"access|accesses|accessing|"
    r"query|queries|querying|"
    r"fetch|fetches|fetching"
    r")" + _NON_IDENT_AFTER + r"[\s\S]{0,80}?" + _NON_IDENT_BEFORE
    + _FRONTMATTER_TARGET_RE + _NON_IDENT_AFTER,
    re.IGNORECASE,
)
# Negation tokens that turn "read frontmatter" into a prohibition. Anchored
# explicitly to direct preposition of the read verb (≤30 chars upstream)
# rather than free-floating same-sentence presence — closes R1 P1-2.
_FRONTMATTER_NEGATION_TOKENS_RE = re.compile(
    r"\b(?:never|do\s+not|don'?t|must\s+not|mustn'?t|"
    r"cannot|can'?t|may\s+not|shall\s+not|forbidden|"
    r"NEVER|DO\s+NOT|MUST\s+NOT)\b",
    re.IGNORECASE,
)
# The negation must apply to the read verb itself, not a different clause.
# Window: 0..30 chars before the verb (covers "NEVER read", "must not read",
# "do not look up", and "never read the entry's frontmatter"). Wider windows
# leak across clauses ("Never guess; read frontmatter"); narrower windows
# fail-stop on valid prose like "NEVER read the entry frontmatter" where
# the verb is a few words after the negation.
_FRONTMATTER_NEGATION_WINDOW = 30


# R2 P1-A closure: `\n- ` (bullet boundary) is a clause boundary in
# Markdown prose. Without this, `- NEVER omit markers\n- read the entry
# frontmatter` lets `NEVER` (in the previous bullet) leak into the
# next-bullet's negation window. Treat the bullet boundary as a hard
# clause terminator alongside `.` / `;` / `!` / `?` and blank lines.
_SENTENCE_TERMINATOR_RE = re.compile(
    r"[.;!?]\s|[.;!?]$|\n\s*\n|\n[ \t]*[-*+][ \t]+|\n[ \t]*\d+\.[ \t]+"
)


def _negation_anchored_to_verb(block: str, verb_pos: int) -> bool:
    """Return True iff a negation token appears in the ≤30-char window
    immediately preceding `verb_pos` AND no sentence terminator separates
    the negation from the verb.

    R1 P1-2 closure: scope negation to the verb's left context within the
    same clause. Unrelated negation words elsewhere in the same paragraph
    (or in a preceding sentence the simple-window check would otherwise
    catch) must not bless a positive read instruction.

    Algorithm: take the ≤30-char left window; find the LAST sentence
    terminator inside it; truncate the window to start AFTER that
    terminator. Then run the negation-token regex against the truncated
    window. This keeps `NEVER read frontmatter` (no terminator between
    `NEVER` and `read`) but rejects `Never guess. Always read frontmatter`
    (terminator `.` between `Never` and `read`).
    """
    window_start = max(0, verb_pos - _FRONTMATTER_NEGATION_WINDOW)
    window = block[window_start:verb_pos]
    # Find the rightmost sentence terminator in the window, truncate after it.
    last_term = None
    for m in _SENTENCE_TERMINATOR_RE.finditer(window):
        last_term = m
    if last_term is not None:
        window = window[last_term.end():]
    return _FRONTMATTER_NEGATION_TOKENS_RE.search(window) is not None


_TWO_LAYER_TITLE_EXACT_RE = re.compile(
    r"(?m)^[ \t]*(?P<level>#{1,6})[ \t]+Two-Layer Citation Emission \(v3\.7\.1\)[ \t]*$"
)
# R3 P1-A closure: heading-DRIFT detector. Any heading at any level whose
# title STARTS with `Two-Layer Citation Emission (v3.7.1)` but has trailing
# non-whitespace (e.g., `### Two-Layer Citation Emission (v3.7.1) — extended`)
# is a drift duplicate. Pre-R3 only exact-title headings counted; a drift
# heading slipped past AND its body sat outside the scanned block range
# (since `_extract_two_layer_block` stops at the next H1/H2/H3), so
# forbidden text under it was invisible to per-block invariants.
_TWO_LAYER_TITLE_DRIFT_RE = re.compile(
    r"(?m)^[ \t]*(?P<level>#{1,6})[ \t]+Two-Layer Citation Emission \(v3\.7\.1\)"
    r"(?P<trailing>[^\n]*)$"
)


def _find_all_two_layer_block_positions(text: str) -> list[int]:
    """Return positions of every heading whose title is or BEGINS WITH
    `Two-Layer Citation Emission (v3.7.1)`.

    R1 P2 + R2 P2 + R3 P1-A closure: counts H1–H6 exact AND drift
    (trailing-text-bearing) titles as duplicates. The canonical form is
    H2 (`## Two-Layer Citation Emission (v3.7.1)`); any other heading
    that begins the same title but at a different level or with extra
    trailing text is a contradiction-vector.

    The canonical-block-presence check (`_extract_two_layer_block`) still
    requires the FIRST canonical EXACT-title H2 — see that function's
    docstring.
    """
    positions: list[int] = []
    for m in _TWO_LAYER_TITLE_DRIFT_RE.finditer(text):
        # Trailing text after the title must be stripped; a string of
        # whitespace is fine, but anything else marks a drift heading.
        trailing = m.group("trailing")
        if trailing.strip() == "":
            positions.append(m.start())
        else:
            # Drift heading: report the position too. `_check_block_count`
            # relies on the count comparison; presence of drift implies >1.
            positions.append(m.start())
    return positions


def _find_drift_titles(text: str) -> list[tuple[int, str]]:
    """Return (position, full_heading_line) of headings that begin with the
    canonical title but carry trailing non-whitespace text (e.g.
    `## Two-Layer Citation Emission (v3.7.1) — extended`).

    Used by the duplicate check to emit a more specific failure message
    when a drift heading is detected (R3 P1-A closure).
    """
    drifts: list[tuple[int, str]] = []
    for m in _TWO_LAYER_TITLE_DRIFT_RE.finditer(text):
        trailing = m.group("trailing")
        if trailing.strip() != "":
            line = text[m.start(): m.end()]
            drifts.append((m.start(), line))
    return drifts


def _find_canonical_h2_position(text: str) -> int | None:
    """Return the position of the FIRST canonical EXACT-title H2
    (`## Two-Layer Citation Emission (v3.7.1)`), or None if no exact-H2
    match exists.

    Used by `_extract_two_layer_block` so the per-block invariants run
    against the canonical (H2 EXACT) instance even when same-title
    duplicates of other heading levels or drift trailing text exist.
    """
    for m in _TWO_LAYER_TITLE_EXACT_RE.finditer(text):
        if m.group("level") == "##":
            return m.start()
    return None


def _extract_two_layer_block(text: str) -> tuple[str | None, int | None, int | None]:
    """Return (block_text, start_offset, end_offset) for the FIRST canonical
    H2 Two-Layer block in the file, or (None, None, None) if no canonical
    H2 instance exists.

    Block start: line containing the canonical H2 heading. Block end: next
    H1/H2/H3 heading line, or EOF. The returned text INCLUDES the heading
    line and ends just before the terminator.

    Same-title duplicates at other heading levels (H3, H4, etc.) are
    enumerated separately via `_find_all_two_layer_block_positions` and
    flagged by the duplicate-count check.
    """
    line_start = _find_canonical_h2_position(text)
    if line_start is None:
        return None, None, None
    next_h_re = re.compile(r"(?m)^[ \t]*#{1,3}[ \t]+")
    # Find heading text length so search starts after it.
    head_eol = text.find("\n", line_start + len(TWO_LAYER_BLOCK_HEADING))
    search_start = (head_eol + 1) if head_eol >= 0 else len(text)
    next_match = next_h_re.search(text, pos=search_start)
    block_end = next_match.start() if next_match else len(text)
    return text[line_start:block_end], line_start, block_end


def _split_into_sentences(block: str) -> list[str]:
    """Crude sentence splitter for invariant-(iii) negation-aware scanning.

    Splits on `. ` / `.\n` / `;` / list-item line breaks. Does not handle
    abbreviation edge cases — the block prose is short and authored, so the
    splitter is good enough for grep-class enforcement.
    """
    # Replace bullet-list `\n- ` boundaries with sentence terminators so each
    # bullet counts as its own sentence (each bullet is an independent
    # obligation in the canonical block).
    normalized = re.sub(r"\n[ \t]*[-*+][ \t]+", ". ", block)
    # Split on sentence-end punctuation followed by whitespace, or on a hard
    # line break that ends a paragraph.
    parts = re.split(r"(?:[.;!?]\s+)|(?:\n\n)", normalized)
    return [p.strip() for p in parts if p.strip()]


def check_step3a_invariants(verbose: bool = True) -> int:
    """Enforce Step 3a's three invariants on each manifest-listed agent.

    Returns 0 on PASS, 1 on FAIL.
    """
    data, err = _load_v3_6_8_manifest()
    if err is not None:
        print(err)
        return 1
    files: list[str] = data["files"]
    if not files:
        # PR-1 ships an empty list; Step 3a populates. Empty list is fine —
        # invariants vacuously hold (no agents to check).
        if verbose:
            print(
                "[v3.7.1 Step 3a invariants] manifest 'files' empty — Step 3a "
                "has not populated yet (vacuous PASS)"
            )
        return 0

    failures: list[str] = []
    for rel in files:
        agent_path = REPO_ROOT / rel
        if not agent_path.exists():
            failures.append(
                f"  [{rel}] manifest references missing file"
            )
            continue
        text = agent_path.read_text(encoding="utf-8")
        # R1 P2 + R2 P2 + R3 P1-A closure: require exactly one canonical
        # block per manifest file. Counts EXACT and DRIFT (trailing-text)
        # titles at any heading level; drift titles get a dedicated
        # diagnostic so contributors don't waste time looking for "what
        # got duplicated".
        positions = _find_all_two_layer_block_positions(text)
        drifts = _find_drift_titles(text)
        # R4 P3-A closure: emit BOTH drift diagnostics AND exact-duplicate
        # count when both conditions hold, so contributors see every problem
        # at once (was: drift suppressed exact-duplicate report).
        for _, drift_line in drifts:
            failures.append(
                f"  [{rel}] FAIL: heading-drift detected: "
                f"{drift_line.strip()!r}. Any heading whose title begins "
                f"with 'Two-Layer Citation Emission (v3.7.1)' but carries "
                f"trailing text is a duplicate-by-drift — its body sits "
                f"outside the canonical block scan range and could carry "
                f"contradictory instructions. Rename or remove."
            )
        # `positions` includes BOTH exact and drift entries (drift regex
        # subsumes exact). Subtract drift count to get exact-title count.
        exact_count = len(positions) - len(drifts)
        if exact_count > 1:
            failures.append(
                f"  [{rel}] FAIL: {exact_count} exact-title "
                f"'{TWO_LAYER_BLOCK_HEADING}' headings found; exactly one "
                f"is required per Step 3a (duplicates risk contradictory "
                f"instructions silently passing per-block invariants)"
            )
            # Continue to the per-block invariants on the first occurrence so
            # the operator gets a complete failure list, not just the count.
        block, _, _ = _extract_two_layer_block(text)
        if block is None:
            failures.append(
                f"  [{rel}] Two-Layer Citation Emission block missing "
                f"(expected H2 heading '{TWO_LAYER_BLOCK_HEADING}')"
            )
            continue

        # Invariant (i): two-layer form. Block must contain BOTH the
        # `<!--ref:` HTML-comment literal AND `author-year` visible-form
        # token. We grep for the literal `<!--ref:` (anchors the hidden
        # layer) and for `author-year` or `author, year` (anchors the
        # visible layer). The combination is the two-layer contract.
        has_ref_marker = "<!--ref:" in block
        has_author_year = bool(
            re.search(r"author[\s-]year|author,\s*year", block, re.IGNORECASE)
        )
        if not has_ref_marker:
            failures.append(
                f"  [{rel}] invariant (i) FAIL: two-layer form missing "
                f"hidden-layer marker `<!--ref:slug-->`. The block must "
                f"specify the HTML-comment literal `<!--ref:` so agents emit "
                f"the hidden-layer marker."
            )
        if not has_author_year:
            failures.append(
                f"  [{rel}] invariant (i) FAIL: two-layer form missing "
                f"visible-layer anchor (author-year / author, year). The "
                f"block must name the visible-layer form."
            )

        # Invariant (ii): forbidden resolver-layer mentions.
        for pattern in _FORBIDDEN_RESOLVER_TERMS:
            m = pattern.search(block)
            if m is not None:
                failures.append(
                    f"  [{rel}] invariant (ii) FAIL: block mentions "
                    f"'{m.group(0)}' (strict partial-inversion: agent must "
                    f"NOT name the resolver layer / finalizer / orchestrator "
                    f"/ stage gate / terminal gate / resolver)"
                )

        # Invariant (iii): no frontmatter-read instruction.
        # R1 P1-2 closure: scan the ENTIRE block (not pre-split sentences),
        # then for each verb-target match, check negation in the ≤30-char
        # window preceding the verb. This eliminates false-pass on sentences
        # like "Never guess, read the entry frontmatter" where the negation
        # word doesn't apply to the read verb.
        for verb_match in _FRONTMATTER_READ_VERB_RE.finditer(block):
            verb_pos = verb_match.start("verb")
            if _negation_anchored_to_verb(block, verb_pos):
                continue
            # Diagnostic excerpt: 60 chars centered on the match.
            excerpt_start = max(0, verb_pos - 30)
            excerpt_end = min(len(block), verb_match.end() + 30)
            excerpt = block[excerpt_start:excerpt_end].replace("\n", " ")
            failures.append(
                f"  [{rel}] invariant (iii) FAIL: block instructs agent to "
                f"'{verb_match.group(0).strip()}' frontmatter without "
                f"a directly anchored negation. Agent must learn slug ONLY "
                f"from corpus context in its prompt; frontmatter access is "
                f"forbidden in this block. Excerpt: {excerpt!r}"
            )

        if verbose and not any(rel in f for f in failures):
            print(f"  [{rel}] Step 3a invariants PASS")

    if failures:
        print("[ARS-V3.7.1 LINT ERROR: Step 3a Two-Layer Citation Emission invariants]")
        for line in failures:
            print(line)
        return 1
    if verbose:
        print(
            f"[v3.7.1 Step 3a invariants] PASSED ({len(files)} manifest agent(s))"
        )
    return 0


def check_byte_equivalence(verbose: bool = True) -> int:
    """Run the SHA byte-equivalence gate.

    Returns 0 on PASS, 1 on FAIL. Side effect: prints diagnostic lines to stdout.
    """
    if _is_codex_distribution():
        return check_codex_byte_equivalence(verbose=verbose)

    # 1. Shallow-clone gate (CI safety)
    err = _ensure_full_clone()
    if err is not None:
        print(err)
        return 1

    # 2. Anti-self-baseline guard (round-2 codex P2 closure):
    #    Refuse to run on PRs that mutate the v3.6.7 manifest. Without this,
    #    `git log -1 -- v3_6_7_inversion_manifest.json` would resolve to the
    #    PR's own commit and the SHA comparison would hash modified content
    #    against itself.
    ok, err = _v3_6_7_manifest_unchanged_in_pr()
    if not ok:
        print(err)
        return 1

    # 3. v3.6.7 base commit derivation (single source of truth)
    base_commit, err = _v3_6_7_base_commit()
    if err is not None:
        print(err)
        return 1
    if verbose:
        print(f"[v3.7.1 SHA gate] v3.6.7 base commit: {base_commit[:12]}")

    # 3. Load v3.6.7 manifest (file list = single source of truth)
    files_v367, err = _load_v3_6_7_manifest()
    if err is not None:
        print(err)
        return 1
    if not files_v367:
        # An empty v3.6.7 manifest would be a contract violation; fail loud.
        print(
            "[ARS-V3.7.1 LINT ERROR: v3.6.7 manifest carries empty file list; "
            "expected the three v3.6.7-frozen agent files]"
        )
        return 1

    # 4. Load v3.6.8 manifest (just for shape validation; entries unused here)
    _, err = _load_v3_6_8_manifest()
    if err is not None:
        print(err)
        return 1

    # 5. For each v3.6.7 protected file: extract block at HEAD and at base
    # commit, hash both, assert equality.
    failures: list[str] = []
    for rel in files_v367:
        head_path = REPO_ROOT / rel
        if not head_path.exists():
            failures.append(
                f"  [{rel}] missing at PR HEAD (deletion of v3.6.7-protected "
                "file would re-open v3.6.7 convergence; restore the file)"
            )
            continue
        head_bytes_full = head_path.read_bytes()
        head_block = _extract_block_bytes(head_bytes_full)
        if head_block is None:
            failures.append(
                f"  [{rel}] PATTERN PROTECTION (v3.6.7) marker missing at "
                "PR HEAD (the v3.6.7-tagged block was renamed or removed; "
                "boundary rule violated — v3.7.1 must NOT mutate v3.6.7 blocks)"
            )
            continue
        base_bytes_full, err = _read_blob_at_commit(base_commit, rel)
        if err is not None:
            failures.append(f"  [{rel}] {err}")
            continue
        base_block = _extract_block_bytes(base_bytes_full)
        if base_block is None:
            failures.append(
                f"  [{rel}] PATTERN PROTECTION (v3.6.7) marker missing at "
                f"v3.6.7 base commit {base_commit[:12]} — manifest "
                "derivation produced an inconsistent base"
            )
            continue
        head_sha = _sha256(head_block)
        base_sha = _sha256(base_block)
        if head_sha != base_sha:
            failures.append(
                f"  [{rel}] BYTE-EQUIVALENCE FAIL\n"
                f"      HEAD     SHA-256: {head_sha}\n"
                f"      v3.6.7   SHA-256: {base_sha}\n"
                f"      v3.6.7-tagged PATTERN PROTECTION block changed; "
                f"v3.7.1 boundary rule violated. Restore the block or land "
                f"a v3.6.7+ amendment manifest first."
            )
        elif verbose:
            print(f"  [{rel}] PASS (sha256={head_sha[:12]})")

    if failures:
        print("[ARS-V3.7.1 LINT ERROR: v3.6.7 PATTERN PROTECTION block byte-equivalence failures]")
        for line in failures:
            print(line)
        return 1
    if verbose:
        print(f"[v3.7.1 SHA gate] PASSED ({len(files_v367)} v3.6.7 protected file(s))")
    return 0


def main() -> int:
    rc_sha = check_byte_equivalence()
    rc_invariants = check_step3a_invariants()
    # Both must pass; report combined exit code.
    return 1 if (rc_sha or rc_invariants) else 0


if __name__ == "__main__":
    sys.exit(main())
