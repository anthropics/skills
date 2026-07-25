#!/usr/bin/env python3
"""Apply a revision patch to an anchored draft — two-phase, fail-closed.

#89 Item 7 Slice A. Normative source:
`docs/design/2026-06-10-390-diff-patch-revision-mode-spec.md` §3.3
(deterministic apply), §3.2 (patch document constraints).

**Phase 1 — validate everything, touch nothing.** Schema-validate the
patch; verify `base_draft_hash` against the base file's raw bytes; parse
the base with the shared parser; check every op (target exists,
`old_hash` matches the current normalized block text, each block ID in
at most one op in any role — the `DOC-BODY-START` sentinel included,
no `<!--block:` in `new_text`, `new_text` segments cleanly). ANY failure
rejects the whole patch with a structured report and no output artifact:
a stale-base or hallucinated-target patch cannot half-land.

**Phase 2 — apply all, by byte-span splicing.** The original byte stream
is spliced at the validated spans; every byte outside them — untouched
blocks' marker lines and inter-block separator bytes included — is
copied verbatim from the base. Hash normalization is read-side only and
never appears in the output. Fresh IDs are assigned by this script alone
(`max(existing) + 1`, base-document encounter order). Output is written
to a temp file and atomically renamed; a post-write self-check re-parses
the result and asserts marker uniqueness + grammar.

**Structural-shape triggers** (§3.3, deterministic): heading-block ops,
net section-count change, and `blocks_touched / blocks_total` strictly
above `--touched-ratio-threshold` (default 0.6 — the #424 Slice B ship
decision; pass 1.0 to disable, since the ratio never exceeds 1.0 and the
comparator is strict per the spec's "above a threshold"). The ratio is
computed and recorded in every report regardless. Any raised flag
refuses the apply unless `--acknowledge-structural` is set (the §3.6
escalation checkpoint owns that decision; this script only enforces it).
`blocks_touched` counts replace/delete targets; an `insert_after`
anchor's content is not touched, so it does not count. Heading-anchor
exemption (#424): an `insert_after` whose anchor is a heading raises NO
heading flag when its segmented `new_text` contains no heading blocks —
inserting body text after a section heading leaves every heading byte
untouched; heading-bearing `new_text` still flags via its segments.

**Pure-move check** (§3.3): an inserted segment whose normalized-text
hash equals a same-patch deleted block's `old_hash` is recorded as a
machine-verified `pure_move` pair. No similarity heuristics for
moved-and-reworded text — that lands as ordinary touched-block exposure.

Exit codes: 0 = applied; 2 = Phase 1 rejection (structured report on
stdout); 3 = structural-shape refusal (unacknowledged); 4 = post-write
self-check failure (bug, not user error).

Usage:
    python scripts/ars_apply_revision_patch.py base.md patch.json \
        --output base.rev2.md [--report-out R.json] \
        [--acknowledge-structural] [--touched-ratio-threshold 0.6]
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import jsonschema

if __package__ in (None, ""):  # pragma: no cover - direct CLI invocation
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts._block_parser import (
    BLOCK_ID_FORMAT,
    MARKER_PREFIX,
    Block,
    BlockParseError,
    ParsedDocument,
    atomic_write_bytes,
    base_draft_hash,
    parse_document,
    segment_fragment,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
PATCH_SCHEMA_PATH = REPO_ROOT / "shared" / "contracts" / "patch" / "revision_patch.schema.json"
DOC_BODY_START = "DOC-BODY-START"
REPORT_FORMAT_VERSION = "1.0"
# #424 Slice B ship decision (spec §3.3 required it; recorded in the spec's
# amendment log). Strict `>` comparator per the spec's "above a threshold":
# 1.0 disables the trigger because touched/total never exceeds 1.0.
DEFAULT_TOUCHED_RATIO_THRESHOLD = 0.6


def _ratio_threshold(raw: str) -> float:
    """argparse type for --touched-ratio-threshold: a finite value in
    [0.0, 1.0]. Rejects NaN (which makes `touched_ratio > NaN` silently
    False, disabling the trigger off the documented 1.0 path), inf, and
    out-of-range values."""
    try:
        value = float(raw)
    except ValueError:
        raise argparse.ArgumentTypeError(f"{raw!r} is not a number")
    import math
    if not math.isfinite(value) or not (0.0 <= value <= 1.0):
        raise argparse.ArgumentTypeError(
            f"{raw!r} must be a finite ratio in [0.0, 1.0] "
            "(1.0 disables the trigger; NaN/inf/negative are rejected)"
        )
    return value


class ApplyRejection(Exception):
    """Phase 1 rejection carrying the structured failure list."""

    def __init__(self, failures: list[dict]):
        self.failures = failures
        super().__init__(f"{len(failures)} validation failure(s)")


class StructuralRefusal(Exception):
    """Unacknowledged structural-shape flags (§3.3 / §3.6)."""

    def __init__(self, flags: dict):
        self.flags = flags
        super().__init__("structural-shape flags raised without acknowledgement")


def _fail(failures: list[dict], op_index: int | None, kind: str, message: str, **extra) -> None:
    entry = {"op_index": op_index, "kind": kind, "message": message}
    entry.update(extra)
    failures.append(entry)


def _load_patch_schema() -> dict:
    return json.loads(PATCH_SCHEMA_PATH.read_text(encoding="utf-8"))


def validate_patch(
    patch: dict,
    base_raw: bytes,
    base: ParsedDocument,
    *,
    touched_ratio_threshold: float | None,
) -> dict:
    """Phase 1. Returns the analysis dict Phase 2 consumes, or raises."""
    failures: list[dict] = []

    validator = jsonschema.Draft202012Validator(_load_patch_schema())
    schema_errors = sorted(validator.iter_errors(patch), key=lambda e: list(e.absolute_path))
    for err in schema_errors:
        path = "/".join(str(p) for p in err.absolute_path) or "(root)"
        _fail(failures, None, "schema_invalid", f"{path}: {err.message}")
    if schema_errors:
        raise ApplyRejection(failures)

    actual_base_hash = base_draft_hash(base_raw)
    if patch["base_draft_hash"] != actual_base_hash:
        _fail(
            failures,
            None,
            "base_hash_mismatch",
            "patch was generated against a different base (stale-base rejection)",
            expected=patch["base_draft_hash"],
            actual=actual_base_hash,
        )

    by_id = base.block_by_id()
    seen_targets: dict[str, int] = {}
    analyses: list[dict] = []

    for idx, op in enumerate(patch["ops"]):
        block_id = op["block_id"]
        analysis: dict = {"op": op, "op_index": idx, "segments": None, "target": None}

        if block_id in seen_targets:
            _fail(
                failures,
                idx,
                "duplicate_target",
                f"block {block_id} already named by op {seen_targets[block_id]} "
                "(each block ID appears in at most one op, in any role)",
            )
        else:
            seen_targets[block_id] = idx

        if block_id == DOC_BODY_START:
            pass  # position sentinel, no anchor block to precondition on
        elif block_id not in by_id:
            _fail(failures, idx, "unknown_block_id", f"block {block_id} does not exist in the base")
        else:
            target = by_id[block_id]
            analysis["target"] = target
            if op["old_hash"] != target.norm_hash:
                _fail(
                    failures,
                    idx,
                    "hash_mismatch",
                    f"block {block_id} content is not what the patch preconditions on",
                    expected=op["old_hash"],
                    actual=target.norm_hash,
                )

        new_text = op.get("new_text")
        if new_text is not None:
            if MARKER_PREFIX in new_text:
                _fail(
                    failures,
                    idx,
                    "marker_in_new_text",
                    "new_text must not contain <!--block: markers "
                    "(ID assignment is the apply script's exclusive authority)",
                )
            else:
                try:
                    analysis["segments"] = segment_fragment(new_text)
                except BlockParseError as exc:
                    _fail(failures, idx, f"new_text_invalid:{exc.kind}", str(exc))

        analyses.append(analysis)

    if failures:
        raise ApplyRejection(failures)

    # Structural-shape flags (§3.3) — deterministic, computed on the
    # validated patch only.
    heading_op_indexes: list[int] = []
    headings_before = sum(1 for b in base.blocks if b.kind == "heading")
    headings_delta = 0
    touched = 0
    for analysis in analyses:
        op = analysis["op"]
        target: Block | None = analysis["target"]
        segments: list[Block] | None = analysis["segments"]
        seg_headings = sum(1 for s in (segments or []) if s.kind == "heading")
        target_is_heading = target is not None and target.kind == "heading"
        # §3.3 heading rule with the #424 heading-anchor exemption: an op
        # that REWRITES or DELETES a heading block, or whose segmented
        # new_text CONTAINS a heading, flags. An insert_after merely
        # ANCHORED on a heading does not — the heading's bytes are
        # untouched, and "insert body text after a section heading" is the
        # most common legitimate insertion; flagging it daily would erode
        # the checkpoint (alarm fatigue). Heading-bearing new_text still
        # flags via seg_headings whatever the anchor is.
        if op["op"] == "replace_block":
            touched += 1
            headings_delta += seg_headings - (1 if target_is_heading else 0)
            flags_heading = target_is_heading or bool(seg_headings)
        elif op["op"] == "delete_block":
            touched += 1
            headings_delta -= 1 if target_is_heading else 0
            flags_heading = target_is_heading
        else:  # insert_after
            headings_delta += seg_headings
            flags_heading = bool(seg_headings)
        if flags_heading:
            heading_op_indexes.append(analysis["op_index"])

    blocks_total = len(base.blocks)
    touched_ratio = (touched / blocks_total) if blocks_total else 0.0
    ratio_exceeded = (
        touched_ratio_threshold is not None and touched_ratio > touched_ratio_threshold
    )
    structural_flags = {
        "heading_op_indexes": heading_op_indexes,
        "section_count_delta": headings_delta,
        "touched_ratio": round(touched_ratio, 4),
        "touched_ratio_threshold": touched_ratio_threshold,
        "touched_ratio_exceeded": ratio_exceeded,
        "any": bool(heading_op_indexes) or headings_delta != 0 or ratio_exceeded,
    }

    # Pure-move pairs (§3.3): inserted segment hash == deleted block hash.
    deleted_hashes = {
        a["op"]["old_hash"]: a["op"]["block_id"]
        for a in analyses
        if a["op"]["op"] == "delete_block"
    }
    pure_move_seeds = []
    for analysis in analyses:
        if analysis["op"]["op"] not in ("replace_block", "insert_after"):
            continue
        for seg_idx, seg in enumerate(analysis["segments"] or []):
            if seg.norm_hash in deleted_hashes:
                pure_move_seeds.append(
                    {
                        "from_block_id": deleted_hashes[seg.norm_hash],
                        "op_index": analysis["op_index"],
                        "segment_index": seg_idx,
                    }
                )

    return {
        "analyses": analyses,
        "structural_flags": structural_flags,
        "pure_move_seeds": pure_move_seeds,
        "counters_base": {"blocks_total": blocks_total, "blocks_touched": touched},
    }


def _render_segments(
    new_text: str,
    segments: list[Block],
    *,
    first_keeps_marker: bool,
    fresh_ids: list[str],
) -> str:
    """Render fragment segments with marker lines, joined by blank lines.

    ``fresh_ids`` supplies the IDs for every segment that needs one
    (all of them, except the first when ``first_keeps_marker``). Each
    rendered segment ends with exactly one newline.
    """
    rendered: list[str] = []
    fresh_iter = iter(fresh_ids)
    for seg_idx, seg in enumerate(segments):
        seg_text = new_text[seg.span[0] : seg.span[1]]
        if not seg_text.endswith("\n"):
            seg_text += "\n"
        if seg_idx == 0 and first_keeps_marker:
            rendered.append(seg_text)
        else:
            rendered.append(f"<!--block:{next(fresh_iter)}-->\n{seg_text}")
    return "\n".join(rendered)


def apply_patch(base_text: str, base: ParsedDocument, analysis: dict) -> tuple[str, dict]:
    """Phase 2: splice. Returns (output_text, phase2_report_fields)."""
    blocks = base.blocks
    n = len(blocks)
    text = base_text

    ops_by_target: dict[str, dict] = {}
    doc_body_start_op: dict | None = None
    for a in analysis["analyses"]:
        if a["op"]["block_id"] == DOC_BODY_START:
            doc_body_start_op = a
        else:
            ops_by_target[a["op"]["block_id"]] = a

    next_num = base.next_fresh_id_num()
    fresh_assigned: list[str] = []
    seg_id_map: dict[tuple[int, int], str] = {}  # (op_index, seg_index) -> fresh id
    ops_applied: list[dict] = []

    def _take_fresh(op_index: int, seg_indexes: list[int]) -> list[str]:
        nonlocal next_num
        ids = []
        for seg_idx in seg_indexes:
            fid = BLOCK_ID_FORMAT.format(next_num)
            next_num += 1
            ids.append(fid)
            fresh_assigned.append(fid)
            seg_id_map[(op_index, seg_idx)] = fid
        return ids

    # Splicing model: a block's unit is [full_start, next.full_start); the
    # "gap" is the separator bytes between its content end and the next
    # block's full_start, copied verbatim (§3.3 byte-span splicing). The
    # gap must be RECOMPUTED instead of copied only where its boundary
    # disappears (everything after it deleted) or never existed (an
    # insertion lands where the base had zero inter-block bytes).
    deleted = {
        a["op"]["block_id"]
        for a in analysis["analyses"]
        if a["op"]["op"] == "delete_block"
    }
    # Highest index that survives the patch; `i >= last_kept` ⇔ every
    # block after i is deleted (O(1) per block instead of a tail scan).
    last_kept = max(
        (j for j in range(n) if blocks[j].block_id not in deleted),
        default=-1,
    )

    out: list[str] = []
    head_end = blocks[0].full_start if n else len(text)
    out.append(text[0:head_end])

    if doc_body_start_op is not None:
        a = doc_body_start_op
        segments = a["segments"]
        ids = _take_fresh(a["op_index"], list(range(len(segments))))
        rendered = _render_segments(
            a["op"]["new_text"], segments, first_keeps_marker=False, fresh_ids=ids
        )
        out.append(rendered)
        if n:
            out.append("\n")
        ops_applied.append(
            {
                "op_index": a["op_index"],
                "op": "insert_after",
                "block_id": DOC_BODY_START,
                "roadmap_item_ids": a["op"]["roadmap_item_ids"],
                "new_block_ids": ids,
            }
        )

    for i, block in enumerate(blocks):
        unit_end = blocks[i + 1].full_start if i + 1 < n else len(text)
        content_end = block.span[1]
        gap = text[content_end:unit_end]
        a = ops_by_target.get(block.block_id) if block.block_id else None

        if a is not None and a["op"]["op"] == "delete_block":
            ops_applied.append(
                {
                    "op_index": a["op_index"],
                    "op": "delete_block",
                    "block_id": block.block_id,
                    "roadmap_item_ids": a["op"]["roadmap_item_ids"],
                    "new_block_ids": [],
                }
            )
            continue  # marker, content, and following separator all dropped

        # Suppress the separator when everything after this block is
        # deleted (a last-block delete must not leave trailing blanks).
        rest_all_deleted = i + 1 < n and i >= last_kept

        if a is None:
            out.append(text[block.full_start : content_end])
            out.append("" if rest_all_deleted else gap)
            continue

        op = a["op"]
        if op["op"] == "replace_block":
            segments = a["segments"]
            ids = _take_fresh(a["op_index"], list(range(1, len(segments))))
            if block.marker_span is not None:
                out.append(text[block.marker_span[0] : block.marker_span[1]])
            rendered = _render_segments(
                op["new_text"], segments, first_keeps_marker=True, fresh_ids=ids
            )
            content = text[block.span[0] : block.span[1]]
            if not content.endswith("\n") and rendered.endswith("\n"):
                rendered = rendered[:-1]  # final block without EOL stays EOL-less
            out.append(rendered)
            out.append("" if rest_all_deleted else gap)
            ops_applied.append(
                {
                    "op_index": a["op_index"],
                    "op": "replace_block",
                    "block_id": block.block_id,
                    "roadmap_item_ids": op["roadmap_item_ids"],
                    "new_block_ids": ids,
                }
            )
        else:  # insert_after
            segments = a["segments"]
            ids = _take_fresh(a["op_index"], list(range(len(segments))))
            out.append(text[block.full_start : content_end])
            content = text[block.span[0] : block.span[1]]
            prefix = "\n" if content.endswith("\n") else "\n\n"
            rendered = _render_segments(
                op["new_text"], segments, first_keeps_marker=False, fresh_ids=ids
            )
            out.append(prefix + rendered)
            if gap == "" and i + 1 < n and not rest_all_deleted:
                out.append("\n")  # keep a blank line before an adjacent next block
            out.append("" if rest_all_deleted else gap)
            ops_applied.append(
                {
                    "op_index": a["op_index"],
                    "op": "insert_after",
                    "block_id": block.block_id,
                    "roadmap_item_ids": op["roadmap_item_ids"],
                    "new_block_ids": ids,
                }
            )

    output_text = "".join(out)

    target_id_by_op_index = {
        a["op_index"]: a["op"]["block_id"]
        for a in analysis["analyses"]
        if a["op"]["op"] == "replace_block"
    }
    pure_move_pairs = []
    for seed in analysis["pure_move_seeds"]:
        to_id = seg_id_map.get((seed["op_index"], seed["segment_index"]))
        if to_id is None and seed["segment_index"] == 0:
            # replace_block keeps the target's ID on the head segment.
            to_id = target_id_by_op_index.get(seed["op_index"])
        pure_move_pairs.append(
            {
                "from_block_id": seed["from_block_id"],
                "to_block_id": to_id,
                "op_index": seed["op_index"],
            }
        )
    ops_applied.sort(key=lambda entry: entry["op_index"])
    return output_text, {
        "ops_applied": ops_applied,
        "fresh_block_ids": fresh_assigned,
        "pure_move_pairs": pure_move_pairs,
    }


def run(
    base_path: Path,
    patch_path: Path,
    output_path: Path,
    report_path: Path,
    *,
    acknowledge_structural: bool,
    touched_ratio_threshold: float | None,
) -> dict:
    """Full two-phase apply. Raises ApplyRejection / StructuralRefusal /
    BlockParseError; returns the success report dict.

    `touched_ratio_threshold`: the CLI defaults this to
    DEFAULT_TOUCHED_RATIO_THRESHOLD (0.6, the #424 ship decision); a
    programmatic caller may pass `None` for record-only mode — the ratio is
    still computed and recorded in the report, but never triggers a
    structural refusal (for callers that own their own escalation policy).
    """
    resolved = {
        "base": base_path.resolve(),
        "output": output_path.resolve(),
        "report": report_path.resolve(),
    }
    collisions = []
    if resolved["output"] == resolved["base"]:
        collisions.append("--output must not name the base draft (the base is never modified)")
    if resolved["report"] in (resolved["base"], resolved["output"]):
        collisions.append("--report-out must not name the base draft or the output draft")
    if collisions:
        raise ApplyRejection(
            [
                {"op_index": None, "kind": "artifact_path_collision", "message": msg}
                for msg in collisions
            ]
        )

    # The output is a NEW versioned artifact (§3.3 supersession): refusing
    # to overwrite an existing file is what makes the report-failure
    # cleanup below safe — any file at output_path is one this run created.
    exists = [
        {"op_index": None, "kind": "artifact_already_exists", "message": msg}
        for p, msg in (
            (output_path, "--output already exists; the revised draft must be a new versioned artifact"),
            (report_path, "--report-out already exists; each apply emits its own report"),
        )
        if p.exists()
    ]
    if exists:
        raise ApplyRejection(exists)

    base_raw = base_path.read_bytes()
    base_text = base_raw.decode("utf-8")

    try:
        patch = json.loads(patch_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ApplyRejection(
            [{"op_index": None, "kind": "patch_json_invalid", "message": str(exc)}]
        ) from exc

    try:
        base = parse_document(base_text)
    except BlockParseError as exc:
        raise ApplyRejection(
            [{"op_index": None, "kind": f"base_parse_rejected:{exc.kind}", "message": str(exc)}]
        ) from exc

    analysis = validate_patch(
        patch, base_raw, base, touched_ratio_threshold=touched_ratio_threshold
    )

    flags = analysis["structural_flags"]
    flags["acknowledged"] = acknowledge_structural
    if flags["any"] and not acknowledge_structural:
        raise StructuralRefusal(flags)

    output_text, phase2 = apply_patch(base_text, base, analysis)

    # Post-write self-check (marker uniqueness + grammar): a failure here
    # is a splicer bug — no artifact may land.
    reparsed = parse_document(output_text)
    ids = [b.block_id for b in reparsed.blocks if b.block_id is not None]
    if len(ids) != len(set(ids)):  # pragma: no cover - parser already rejects
        raise AssertionError("self-check: duplicate markers in apply output")

    atomic_write_bytes(output_path, output_text.encode("utf-8"))

    counters_base = analysis["counters_base"]
    blocks_total = counters_base["blocks_total"]
    touched = counters_base["blocks_touched"]
    preserved = blocks_total - touched
    report = {
        "report_format_version": REPORT_FORMAT_VERSION,
        "mode": "patch",
        "base_path": str(base_path),
        "output_path": str(output_path),
        "base_draft_hash": patch["base_draft_hash"],
        "revision_round": patch["revision_round"],
        "ops_applied": phase2["ops_applied"],
        "fresh_block_ids": phase2["fresh_block_ids"],
        "pure_move_pairs": phase2["pure_move_pairs"],
        "structural_flags": flags,
        "counters": {
            "blocks_total": blocks_total,
            "blocks_touched": touched,
            "blocks_preserved_byte_identical": preserved,
            "preserved_ratio": round(preserved / blocks_total, 4) if blocks_total else 0.0,
        },
    }
    try:
        # allow_nan=False: a non-finite counter would serialize as bare
        # `NaN`/`Infinity` (invalid JSON for strict readers). The threshold
        # is range-validated upstream, so this is belt-and-suspenders.
        atomic_write_bytes(
            report_path,
            (json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False)
             + "\n").encode("utf-8"),
        )
    except BaseException:
        # The output and its apply report land as a pair: a report-write
        # failure must not leave a revised draft with no provenance record.
        output_path.unlink(missing_ok=True)
        raise
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("base", type=Path, help="anchored base draft (never modified)")
    parser.add_argument("patch", type=Path, help="revision patch JSON")
    parser.add_argument("--output", type=Path, required=True, help="revised draft output path")
    parser.add_argument(
        "--report-out",
        type=Path,
        default=None,
        help="apply report path (default: <output>.apply-report.json)",
    )
    parser.add_argument(
        "--acknowledge-structural",
        action="store_true",
        help="proceed despite structural-shape flags (set only after the §3.6 escalation checkpoint)",
    )
    parser.add_argument(
        "--touched-ratio-threshold",
        type=_ratio_threshold,
        default=DEFAULT_TOUCHED_RATIO_THRESHOLD,
        help="touched-ratio trigger threshold, a finite ratio in [0.0, 1.0] "
        "(default %(default)s, the #424 ship decision; fires when "
        "blocks_touched/blocks_total is strictly above it; pass 1.0 to disable)",
    )
    args = parser.parse_args(argv)
    report_path = args.report_out or Path(str(args.output) + ".apply-report.json")

    try:
        report = run(
            args.base,
            args.patch,
            args.output,
            report_path,
            acknowledge_structural=args.acknowledge_structural,
            touched_ratio_threshold=args.touched_ratio_threshold,
        )
    except ApplyRejection as exc:
        print(json.dumps({"result": "rejected", "phase": 1, "failures": exc.failures}, indent=2))
        return 2
    except StructuralRefusal as exc:
        print(
            json.dumps(
                {
                    "result": "refused_structural",
                    "structural_flags": exc.flags,
                    "hint": "re-run with --acknowledge-structural only after the "
                    "escalation checkpoint (spec §3.6)",
                },
                indent=2,
            )
        )
        return 3
    except AssertionError as exc:  # pragma: no cover - self-check path
        print(f"SELF-CHECK FAILED (bug, no artifact written): {exc}", file=sys.stderr)
        return 4

    counters = report["counters"]
    print(
        "apply ok: {applied} op(s); {preserved}/{total} blocks preserved byte-identical "
        "(ratio {ratio}); report {rpath}".format(
            applied=len(report["ops_applied"]),
            preserved=counters["blocks_preserved_byte_identical"],
            total=counters["blocks_total"],
            ratio=counters["preserved_ratio"],
            rpath=report_path,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
