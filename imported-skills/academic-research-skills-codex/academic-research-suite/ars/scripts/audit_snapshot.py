#!/usr/bin/env python3
"""audit_snapshot.py — ARS v3.6.7 Step 6 Phase 6.1 byte-exact snapshot helper.

Reads bundle files (primary deliverable + supporting context + audit template +
optional previous-findings), validates them as text-only (rejects NUL bytes),
computes SHA-256 from in-memory bytes (single read per file — no TOCTOU window),
emits the canonical bundle manifest, and writes a JSON summary on stdout for
the wrapper to consume.

This script REPLACES the Bash-side `_snapshot_file` helper. The Bash version
had three structural issues (codex review rounds 1-5 surfaced these):

  F-004 (P1, 5 rounds partial): Bash command substitution runs the helper in a
    subshell. Variable assignments (e.g., `_LAST_SNAPSHOT_SHA`) made inside the
    subshell don't propagate to the parent. The wrapper saw empty SHAs.

  F-018 (P1): `grep -q $'\\0'` in Bash treats `$'\\0'` as an empty pattern,
    matching every non-empty file. Every text file was rejected as binary.

  F-020 (P1): `$(cat file)` strips trailing newlines and drops NUL bytes.
    Manifest SHA (computed from in-memory content) drifted from `sha256sum file`
    (computed from disk bytes). Step 3a always reported false mutation.

The Python implementation reads bytes verbatim, hashes from those exact bytes,
and emits both manifest and SHAs to the wrapper via JSON — no subshell, no
trailing-newline drift, binary-safe NUL detection. The wrapper consumes the
JSON via `python3 audit_snapshot.py ... | jq` or by reading from a tmp file.

CLI modes:

  --snapshot
    Compute snapshot for a bundle. Writes:
      - <output-dir>/<run_id>.manifest.txt (per spec §3.6)
      - <output-dir>/<run_id>.prompt.txt (rendered audit prompt)
      - JSON summary to stdout: {primary_shas, supporting_shas, template_sha,
        manifest_sha, bundle_files, prompt_path}

  --verify
    Recompute SHAs of bundle files and compare against manifest. Used by Step 3a
    of the wrapper to detect post-snapshot disk mutation. Exits 0 if no
    mutation, exits 1 with mutated paths on stdout otherwise.

Exit codes:
  0   success
  64  EX_USAGE — bad arguments or NUL-containing input
  1   verify mode: mutation detected (paths printed to stdout, one per line)
  2   internal error (file not found, JSON serialization failure, etc.)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Optional


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def read_bytes_or_die(path: str) -> bytes:
    """Read a file's exact bytes. Exits 2 on missing/unreadable file."""
    try:
        with open(path, "rb") as f:
            return f.read()
    except FileNotFoundError:
        print(f"audit_snapshot: file not found: {path}", file=sys.stderr)
        sys.exit(2)
    except PermissionError:
        print(f"audit_snapshot: permission denied: {path}", file=sys.stderr)
        sys.exit(2)


def reject_if_binary(path: str, content: bytes) -> None:
    """Reject NUL-containing input (F-018 closure).

    Phase 6.1 audits are UTF-8 text deliverables (markdown, JSON, YAML).
    Bash command-substitution would silently strip NUL bytes; Python's
    binary-safe `b"\\0" in content` test catches them cleanly.
    """
    if b"\0" in content:
        print(
            f"audit_snapshot: file contains NUL bytes (binary not supported): {path}",
            file=sys.stderr,
        )
        sys.exit(64)


def sha256_hex(content: bytes) -> str:
    """SHA-256 hex digest from in-memory bytes."""
    return hashlib.sha256(content).hexdigest()


def _extract_template_sections(template_str: str, section_numbers: list[int]) -> str:
    """Extract specified Section blocks from the audit template.

    The template uses `## Section N — Title` headers with `---` separators.
    F-023 (P1, R6): we substitute Sections 1/2/4/5 with real round metadata
    above; the template's placeholder versions of those sections must not be
    embedded too, or codex sees `{N}` / `{git_sha}` literals in the prompt.

    F-026 (P2, R7): the LAST extracted section must terminate at the next
    top-level `## ` heading (e.g. `## Worked example`, `## Cross-references`),
    not at end-of-file. Without this guard, Section 7's extraction would pull
    the appendix worked example — which embeds a synthesis_agent 4(f) clause —
    into prompts dispatched for non-synthesis agents, contradicting the real
    Section 4(f) we substituted above.

    PR #78 codex round-1 P1: heading detection must skip headings inside
    fenced code blocks (```/~~~). The v3.7.1 Section 0 Scope Report contains
    a fenced sub-block whose first line starts with `## Codex Audit Round N
    — Scope Report`; without fence-awareness, that line was treated as the
    next H2 boundary and Section 0 was truncated mid-fence.

    Returns concatenated section text (with the leading `## Section N` header
    intact and the appendix excluded).
    """
    import re as _re

    # Mask fenced code blocks (```...``` and ~~~...~~~) with whitespace so
    # ## headings inside them don't count as section boundaries. Length is
    # preserved so match offsets stay aligned with the original string.
    def _mask_fences(s: str) -> str:
        fence_re = _re.compile(
            r"^([ \t]*)(```|~~~)[^\n]*\n.*?^\1\2[ \t]*$",
            _re.DOTALL | _re.MULTILINE,
        )
        def _repl(m: _re.Match[str]) -> str:
            return "".join(" " if ch != "\n" else "\n" for ch in m.group(0))
        return fence_re.sub(_repl, s)

    masked = _mask_fences(template_str)

    # Match either Section heading or any other top-level `## ` heading
    # (e.g. "## Worked example", "## Cross-references"); the latter terminate
    # the last extracted section.
    boundary_re = _re.compile(r"^## (?:Section (\d+)( —|$)|.+)", _re.MULTILINE)
    matches = list(boundary_re.finditer(masked))
    if not matches:
        return template_str  # no headings found — fall back to verbatim

    # Identify which matches are real Section N starts (group(1) populated)
    section_starts: list[tuple[int, int]] = []  # (section_num, match_index)
    for i, m in enumerate(matches):
        if m.group(1) is not None:
            section_starts.append((int(m.group(1)), i))

    requested = set(section_numbers)
    if not requested.issubset({n for n, _ in section_starts}):
        missing = requested - {n for n, _ in section_starts}
        raise ValueError(
            f"audit_snapshot: requested template sections {sorted(missing)} not found "
            f"(template has Sections {sorted({n for n, _ in section_starts})})"
        )

    parts: list[str] = []
    for sec_num, match_idx in section_starts:
        if sec_num not in requested:
            continue
        start = matches[match_idx].start()
        # End at the next `## ` heading of any kind (Section or appendix),
        # not just the next Section. This catches the post-Section-7 appendix.
        end = (
            matches[match_idx + 1].start()
            if match_idx + 1 < len(matches)
            else len(template_str)
        )
        parts.append(template_str[start:end].rstrip() + "\n\n")
    return "".join(parts)


_SECTION_4F_BY_AGENT = {
    "synthesis_agent": (
        "(f) Cross-section consistency check: for every source cited in 2+ "
        "sections of the primary deliverable, verify the source's "
        "characterization is compatible across sections; flag any pair of "
        "sections that pull the source's effect in incompatible directions "
        "(Pattern A1)."
    ),
    "research_architect_agent": (
        "(f) Construct-equivalence test: for every survey item labelled "
        "'reverse-coded', verify it meets the construct-equivalence "
        "definition in `shared/references/psychometric_terminology_glossary.md`."
    ),
    "report_compiler_agent": (
        "(f) Mandatory three-part check: (i) word count = "
        "`len(body.split())` <= publisher cap minus 3-5% buffer per "
        "`shared/references/word_count_conventions.md`; (ii) every entry of "
        "the upstream `protected_hedges` block per "
        "`shared/references/protected_hedging_phrases.md` appears verbatim "
        "in the abstract; (iii) no claim in the abstract is less hedged than "
        "its anchor in the body. Failure of any sub-check is a P1 finding."
    ),
}


def render_prompt(
    audit_template: bytes,
    primary_paths: list[str],
    primary_contents: list[bytes],
    supporting_paths: list[str],
    supporting_contents: list[bytes],
    round_n: int,
    target_rounds: int,
    git_sha: str,
    stage: int,
    agent: str,
    prior_findings: Optional[bytes],
) -> bytes:
    """Render the audit prompt sent to codex stdin.

    The prompt embeds the AT-SNAPSHOT-TIME bytes of every bundle file. Codex
    sees exactly the bytes whose SHA-256 went into the manifest — there is
    no second file read, no TOCTOU window.

    F-023 (P1, R6): the audit template at
    shared/templates/codex_audit_multifile_template.md contains placeholders
    in {curly_braces} that the orchestrator fills before sending to codex
    (Section 1 round metadata, Section 2 git_sha, Section 4(f) bundle-specific
    check). Round 5 redesign initially embedded the template verbatim,
    leaving placeholders unsubstituted — codex would see literal `{N}` in
    the prompt and either omit Section 4(f) entirely or produce an
    unparsable Section 6 verdict. This implementation now does explicit
    bundle-specific substitution and rebuilds Section 1, 2, and 4 around
    real values, while preserving Section 3 / 5 / 6 / 7 verbatim from the
    template (they describe codex's expected output, not the bundle).

    Returns bytes (not str) to preserve binary fidelity.
    """
    section_4f = _SECTION_4F_BY_AGENT.get(
        agent,
        f"(f) Bundle-specific check (no agent-specific clause registered for {agent}; "
        "treat 4(f) as N/A and run only (a)-(e)).",
    )

    if round_n <= 1:
        prior_summary = "none (first round, baseline audit)"
    elif prior_findings is not None:
        prior_summary = (
            "(prior findings attached as supporting context — see file listing "
            "below; verify each carries-forward / closes per (a) and (e))"
        )
    else:
        prior_summary = "(no previous-findings file provided)"

    primary_listing = "\n".join(f"- {p}" for p in primary_paths) or "- (none)"
    supporting_listing = (
        "\n".join(f"- {p}" for p in supporting_paths) if supporting_paths else "- (none)"
    )

    # Extract audit template Sections 0, 3, 6, 7 (verbatim — Section 0 is the
    # v3.7.1 D2 Scope Report block riding verbatim every round per spec §3.2;
    # Sections 3 / 6 / 7 describe codex's expected output / dimensions /
    # anti-fake guard). Sections 1, 2, 4, 5 are rendered below with real
    # values, so we skip the template's placeholder versions to avoid showing
    # codex two copies of the same section (one with placeholders, one
    # substituted) — F-023 closure also requires the placeholder text not
    # appear. Section 0 contains a `<N_total>` etc. placeholder set that codex
    # is expected to fill from bundle inventory at audit time, so it rides
    # verbatim alongside Sections 3 / 6 / 7 (codex round-1 PR #78 P1 closure).
    template_str = audit_template.decode("utf-8", errors="replace")
    section_0 = _extract_template_sections(template_str, [0])
    section_3_to_7 = _extract_template_sections(template_str, [3, 6, 7])

    rendered_intro = (
        f"# ARS v3.6.7 cross-model audit — round {round_n} of {target_rounds}\n"
        f"# Stage: {stage} | Agent: {agent}\n"
        f"# Git SHA at audit start: {git_sha}\n\n"
        f"{section_0}"
        f"## Section 1 — Round metadata\n\n"
        f"Audit round: {round_n} of {target_rounds}\n"
        f"Previous rounds: {prior_summary}\n"
        f"Bundle scope: Stage {stage} deliverable for {agent}\n\n"
        f"## Section 2 — Bundle inventory\n\n"
        f"Authoritative context (commit {git_sha}):\n\n"
        f"Primary deliverables (audit target):\n{primary_listing}\n\n"
        f"Supporting context (do not audit; reference only):\n{supporting_listing}\n\n"
        f"## Section 4 — Round {round_n} job\n\n"
        f"(a) Verify each round-{round_n - 1} finding closed correctly. List by ID.\n"
        f"(b) Audit for new issues introduced by round-{round_n - 1} corrections (cascade audit).\n"
        f"(c) Run the 7 audit dimensions (§3.1-§3.7) plus the bundle-specific Section 4(f) check on the primary deliverables. Report each finding with the dimension or `4(f)` that surfaced it.\n"
        f"(d) Anchoring-bias residual check on closed findings.\n"
        f"(e) PARTIAL-vs-CLOSED check.\n"
        f"{section_4f}\n\n"
        f"## Section 5 — Convergence target\n\n"
        f"Convergence target: ZERO findings of ANY severity in one round.\n\n"
    )

    parts: list[bytes] = []
    parts.append(rendered_intro.encode("utf-8"))
    parts.append(section_3_to_7.encode("utf-8"))
    parts.append(b"\n\n## Primary deliverables (audit target)\n\n")
    for path, content in zip(primary_paths, primary_contents):
        parts.append(f"--- PRIMARY: {path} ---\n".encode("utf-8"))
        parts.append(content)
        parts.append(b"\n")
    if supporting_paths:
        parts.append(b"\n## Supporting context (reference only)\n\n")
        for path, content in zip(supporting_paths, supporting_contents):
            parts.append(f"--- SUPPORTING: {path} ---\n".encode("utf-8"))
            parts.append(content)
            parts.append(b"\n")
    return b"".join(parts)


def write_manifest(
    out_path: str,
    primary_shas: list[tuple[str, str]],
    supporting_shas: list[tuple[str, str]],
    audit_template_path: str,
    audit_template_sha: str,
) -> str:
    """Write the canonical bundle manifest per §3.6.

    Format: <role>:<repo-relative-path>:<sha256-hex>, one line per file,
    sorted by (role, path) via the equivalent of `LC_ALL=C sort`.
    Returns the manifest's own SHA-256 (== `bundle_manifest_sha`).
    """
    lines: list[str] = []
    for path, sha in primary_shas:
        lines.append(f"primary:{path}:{sha}")
    for path, sha in supporting_shas:
        lines.append(f"supporting:{path}:{sha}")
    lines.append(f"template:{audit_template_path}:{audit_template_sha}")
    lines.sort()
    manifest_text = "\n".join(lines) + "\n"
    manifest_bytes = manifest_text.encode("utf-8")
    try:
        with open(out_path, "wb") as f:
            f.write(manifest_bytes)
    except OSError as e:
        print(f"audit_snapshot: manifest write failed: {e}", file=sys.stderr)
        sys.exit(2)
    return sha256_hex(manifest_bytes)


def write_prompt(out_path: str, prompt_bytes: bytes) -> None:
    """Write the rendered prompt to a file the wrapper feeds to codex stdin."""
    try:
        with open(out_path, "wb") as f:
            f.write(prompt_bytes)
    except OSError as e:
        print(f"audit_snapshot: prompt write failed: {e}", file=sys.stderr)
        sys.exit(2)


def dedupe_preserving_order(items: list[str]) -> list[str]:
    """Remove duplicates while preserving first occurrence order (F-021)."""
    seen: set[str] = set()
    out: list[str] = []
    for x in items:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


# ---------------------------------------------------------------------------
# CLI modes
# ---------------------------------------------------------------------------


def cmd_snapshot(args: argparse.Namespace) -> int:
    """Snapshot bundle files, write manifest + prompt, emit JSON summary."""
    primary = list(args.primary or [])
    supporting = list(args.supporting or [])
    if args.previous_findings:
        # Inject --previous-findings into supporting (preserves §3.6 3-role enum).
        # Dedup happens AFTER normalization (which the wrapper does upstream).
        supporting.append(args.previous_findings)
    supporting = dedupe_preserving_order(supporting)

    if not primary:
        print("audit_snapshot: --primary is required", file=sys.stderr)
        return 64
    if not args.audit_template:
        print("audit_snapshot: --audit-template is required", file=sys.stderr)
        return 64
    if not args.output_dir or not args.run_id:
        print("audit_snapshot: --output-dir and --run-id are required", file=sys.stderr)
        return 64

    audit_template_bytes = read_bytes_or_die(args.audit_template)
    reject_if_binary(args.audit_template, audit_template_bytes)
    audit_template_sha = sha256_hex(audit_template_bytes)

    primary_contents: list[bytes] = []
    primary_shas: list[tuple[str, str]] = []
    for p in primary:
        content = read_bytes_or_die(p)
        reject_if_binary(p, content)
        primary_contents.append(content)
        primary_shas.append((p, sha256_hex(content)))

    supporting_contents: list[bytes] = []
    supporting_shas: list[tuple[str, str]] = []
    for s in supporting:
        content = read_bytes_or_die(s)
        reject_if_binary(s, content)
        supporting_contents.append(content)
        supporting_shas.append((s, sha256_hex(content)))

    # F-029 (P3, R8): render the prompt BEFORE writing manifest/prompt to disk.
    # If _extract_template_sections raises ValueError (requested sections not
    # found in template), no partial artifact is left in --output-dir.
    # F-023 (P1, R6): pass stage/agent/prior_findings so render_prompt can
    # substitute audit-template placeholders and select the agent-specific
    # Section 4(f) clause.
    prior_findings_bytes: Optional[bytes] = None
    if args.previous_findings:
        # PREV_FINDINGS was just snapshotted as part of supporting; locate its content.
        for path, content in zip([s for s, _ in supporting_shas], supporting_contents):
            if path == args.previous_findings:
                prior_findings_bytes = content
                break

    try:
        prompt_bytes = render_prompt(
            audit_template_bytes,
            [p for p, _ in primary_shas],
            primary_contents,
            [s for s, _ in supporting_shas],
            supporting_contents,
            args.round,
            args.target_rounds,
            args.git_sha or "unknown",
            args.stage,
            args.agent,
            prior_findings_bytes,
        )
    except ValueError as e:
        # F-029: clean exit 64 with no partial artifact left behind.
        print(f"audit_snapshot: prompt render failed: {e}", file=sys.stderr)
        return 64

    # Now safe to write — render succeeded, no traceback path.
    manifest_path = os.path.join(args.output_dir, f"{args.run_id}.manifest.txt")
    bundle_manifest_sha = write_manifest(
        manifest_path,
        primary_shas,
        supporting_shas,
        args.audit_template,
        audit_template_sha,
    )
    prompt_path = os.path.join(args.output_dir, f"{args.run_id}.prompt.txt")
    write_prompt(prompt_path, prompt_bytes)

    summary = {
        "manifest_path": manifest_path,
        "manifest_sha": bundle_manifest_sha,
        "prompt_path": prompt_path,
        "audit_template_path": args.audit_template,
        "audit_template_sha": audit_template_sha,
        "primary_files": [{"path": p, "sha": sha} for p, sha in primary_shas],
        "supporting_files": [{"path": s, "sha": sha} for s, sha in supporting_shas],
    }
    json.dump(summary, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    """Verify bundle files against the snapshot manifest.

    Reads the manifest file written by --snapshot mode, recomputes each
    referenced file's SHA-256 from current disk content, and reports any
    mismatches. Used by the wrapper's Step 3a (post-codex mutation detection).
    """
    if not args.manifest:
        print("audit_snapshot: --manifest is required for --verify", file=sys.stderr)
        return 64

    try:
        with open(args.manifest, encoding="utf-8") as f:
            manifest_text = f.read()
    except OSError as e:
        print(f"audit_snapshot: manifest read failed: {e}", file=sys.stderr)
        return 2

    mutated_paths: list[str] = []
    for line in manifest_text.splitlines():
        line = line.strip()
        if not line:
            continue
        # Format: <role>:<path>:<sha>
        # The path may contain colons (POSIX paths can include them, though
        # rare); split into 3 parts maximum from the left (role + path + sha)
        # but the SHA is always the LAST 64 hex chars after a colon.
        if ":" not in line:
            continue
        # Find the SHA suffix: last colon, then 64 hex chars.
        if len(line) < 65 or line[-65] != ":":
            continue
        path_with_role = line[:-65]
        expected_sha = line[-64:]
        # Split role:path
        role_sep = path_with_role.find(":")
        if role_sep == -1:
            continue
        # role = path_with_role[:role_sep]  # not needed for verify
        path = path_with_role[role_sep + 1 :]

        # Recompute SHA from current disk content
        try:
            with open(path, "rb") as f:
                actual_sha = sha256_hex(f.read())
        except FileNotFoundError:
            mutated_paths.append(path)
            continue
        if actual_sha != expected_sha:
            mutated_paths.append(path)

    if mutated_paths:
        for p in mutated_paths:
            print(p)
        return 1
    return 0


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="ARS v3.6.7 audit bundle snapshot helper. "
        "Modes: --snapshot (initial) or --verify (post-codex)."
    )
    sub = p.add_subparsers(dest="mode", required=True)

    snap = sub.add_parser("snapshot", help="Snapshot bundle, write manifest + prompt")
    snap.add_argument("--primary", action="append", required=True, help="Primary deliverable path (repeatable)")
    snap.add_argument("--supporting", action="append", default=[], help="Supporting context path (repeatable)")
    snap.add_argument("--previous-findings", help="Optional --previous-findings path (auto-injected into supporting with dedup)")
    snap.add_argument("--audit-template", required=True, help="Audit template path (single)")
    snap.add_argument("--output-dir", required=True, help="Where to write manifest.txt and prompt.txt")
    snap.add_argument("--run-id", required=True, help="Audit run identifier")
    snap.add_argument("--round", type=int, required=True, help="Current audit round")
    snap.add_argument("--target-rounds", type=int, required=True, help="Total target rounds")
    snap.add_argument("--git-sha", help="Repo HEAD short SHA (informational, embedded in prompt)")
    snap.add_argument("--stage", type=int, required=True, help="Stage transition (1-6) the audit gates")
    snap.add_argument(
        "--agent",
        required=True,
        choices=["synthesis_agent", "research_architect_agent", "report_compiler_agent"],
        help="Which v3.6.7 downstream agent produced the deliverable (selects Section 4(f) clause)",
    )

    ver = sub.add_parser("verify", help="Verify bundle files against snapshot manifest")
    ver.add_argument("--manifest", required=True, help="Path to <run_id>.manifest.txt")

    return p


def main(argv: Optional[list[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.mode == "snapshot":
        return cmd_snapshot(args)
    elif args.mode == "verify":
        return cmd_verify(args)
    return 2


if __name__ == "__main__":
    sys.exit(main())
