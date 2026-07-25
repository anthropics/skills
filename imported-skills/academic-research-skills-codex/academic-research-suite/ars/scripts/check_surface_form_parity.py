#!/usr/bin/env python3
"""Integrity + provenance validator for the #216 surface-form parity gold set.

Issue: #216 (reviewer-type / surface-form asymmetry, Kim et al. 2026 arXiv:2605.20668v1 §F.3.6).

This gold set is a MIXED-PROVENANCE REGRESSION FIXTURE, not a detector calibration set.
There is no deterministic predictor for the §F.3.6 surface-form bias (a judge applying two
standards keyed off prose style), n is tiny, and the paper's 29-FN-human / 10-FP-AI split is
DIRECTIONAL. So this validator deliberately does NOT compute FNR/FPR (that would be
fluent-wrongness: a calibration ritual with no predictor behind it). It enforces:

  * structural completeness of every case,
  * PROVENANCE HONESTY — paper_verbatim items carry a real verbatim_anchor; maintainer-authored
    items (counterfactual_rewrite, maintainer_boundary) are labelled as such and never claim
    paper-verbatim provenance,
  * PAIR INVARIANTS — paired items share canonical_claim + expected_correctness and differ only
    in framing_style, so the "framing must not flip the verdict" discipline has valid test material,
  * NO pdftotext line-number anchors (those rot),
  * gold_set <-> manifest agreement (sample_n, provenance distribution, pair membership).

Usage:
    python -m scripts.check_surface_form_parity [gold_set.json]

Exit 0 = clean, 1 = violations (printed one per line to stderr).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
GOLD_DIR = REPO_ROOT / "evals/gold/surface_form_parity"
DEFAULT_GOLD_SET = GOLD_DIR / "gold_set.json"
DEFAULT_MANIFEST = GOLD_DIR / "manifest.yaml"

REQUIRED_TASK_TYPE = "regression-fixture"
VALID_FRAMING_STYLES = {"informal_vague", "technical_precise"}
VALID_PROVENANCE_TYPES = {"paper_verbatim", "counterfactual_rewrite", "maintainer_boundary"}
VALID_CORRECTNESS = {"Correct", "Not Correct", "Ambiguous"}
VALID_ASYMMETRY = {"stricter-on-human", "lenient-on-ai"}
EXCEPTION_ID_SUFFIX = "-ambiguous"
# A line-number anchor (e.g. "L4753", "line 4753", "lines 4753-4756") is a rotting pdftotext
# anchor and is forbidden — provenance must be section/example IDs, not session-scoped extract
# lines. Matches singular/plural "line(s)" and a bare "L" prefix, with optional ranges (codex P2:
# the plural+range form "lines 4753-4756" is the most common pdftotext citation and must be caught).
PDFTOTEXT_LINE_RE = re.compile(r"\b(?:[Ll]ines?|L)\s*\.?\s*\d{3,}(?:\s*[-–]\s*\d{3,})?\b")
# Fields every item must carry (verdict-relevant + traceability).
REQUIRED_ITEM_KEYS = (
    "id",
    "provenance_type",
    "framing_style",
    "asymmetry_direction",
    "canonical_claim",
    "review_item_text",
    "expected_correctness",
)
# The set that MUST be blinded from a judge at evaluation time (#216 decision #2). This is the
# complete answer/manipulated-variable inventory — NOT a minimum — because the serializer-strip
# test reads metadata.judge_blind_fields, so a field dropped from the declaration would silently
# stop being checked there too (codex P2). expected_correctness + the verdict labels + the
# asymmetry direction leak the answer/failure direction; pair_id/framing_style/provenance_type
# leak the manipulated variable.
REQUIRED_JUDGE_BLIND = {
    "pair_id",
    "framing_style",
    "provenance_type",
    "expected_correctness",
    "expert_verdict",
    "meta_reviewer_verdict",
    "asymmetry_direction",
}


def _has_pdftotext_line_anchor(prov: dict[str, Any]) -> bool:
    for val in prov.values():
        if isinstance(val, str) and PDFTOTEXT_LINE_RE.search(val):
            return True
    return False


def validate(data: dict[str, Any], manifest: dict[str, Any] | None = None) -> list[str]:
    """Return a list of violation messages. Empty list = clean."""
    errors: list[str] = []

    metadata = data.get("metadata")
    if not isinstance(metadata, dict):
        errors.append("metadata: missing or not an object")
        metadata = {}

    if metadata.get("task_type") != REQUIRED_TASK_TYPE:
        errors.append(
            f"metadata.task_type={metadata.get('task_type')!r} must be {REQUIRED_TASK_TYPE!r} "
            f"(mixed-provenance regression fixture, not a calibrated threshold set)"
        )

    # judge_blind_fields must exist and cover the minimum leak-prevention set. This is the
    # data-side half of the #216 'invisible at judgment time' decision; the serializer-strip
    # test is the enforcement half.
    blind = metadata.get("judge_blind_fields")
    if not isinstance(blind, list):
        errors.append("metadata.judge_blind_fields: missing or not a list")
    else:
        missing_blind = REQUIRED_JUDGE_BLIND - set(blind)
        if missing_blind:
            errors.append(
                f"metadata.judge_blind_fields missing required entries {sorted(missing_blind)} "
                f"(these would leak the answer or the manipulated variable to a judge)"
            )

    items = data.get("items")
    if not isinstance(items, list) or not items:
        errors.append("items: missing or empty list")
        return errors

    seen_ids: set[str] = set()
    by_id: dict[str, dict[str, Any]] = {}
    pairs: dict[str, list[dict[str, Any]]] = {}

    for idx, item in enumerate(items):
        item_id = item.get("id")
        where = item_id if isinstance(item_id, str) and item_id.strip() else f"<index {idx}>"

        if not isinstance(item_id, str) or not item_id.strip():
            errors.append(f"{where}: missing non-empty id")
        elif item_id in seen_ids:
            errors.append(f"{where}: duplicate id {item_id!r}")
        else:
            seen_ids.add(item_id)
            by_id[item_id] = item

        for key in REQUIRED_ITEM_KEYS:
            val = item.get(key)
            if not isinstance(val, str) or not val.strip():
                errors.append(f"{where}: missing non-empty {key}")

        framing = item.get("framing_style")
        if framing not in VALID_FRAMING_STYLES:
            errors.append(f"{where}: framing_style={framing!r} not in {sorted(VALID_FRAMING_STYLES)}")

        ptype = item.get("provenance_type")
        if ptype not in VALID_PROVENANCE_TYPES:
            errors.append(f"{where}: provenance_type={ptype!r} not in {sorted(VALID_PROVENANCE_TYPES)}")

        if item.get("expected_correctness") not in VALID_CORRECTNESS:
            errors.append(
                f"{where}: expected_correctness={item.get('expected_correctness')!r} "
                f"not in {sorted(VALID_CORRECTNESS)}"
            )

        if item.get("asymmetry_direction") not in VALID_ASYMMETRY:
            errors.append(
                f"{where}: asymmetry_direction={item.get('asymmetry_direction')!r} "
                f"not in {sorted(VALID_ASYMMETRY)}"
            )

        prov = item.get("provenance")
        if not isinstance(prov, dict):
            errors.append(f"{where}: missing provenance object")
            prov = {}
        else:
            for key in ("section", "paper_citation"):
                if not isinstance(prov.get(key), str) or not prov[key].strip():
                    errors.append(f"{where}: provenance.{key} missing or empty")
            if _has_pdftotext_line_anchor(prov):
                errors.append(
                    f"{where}: provenance carries a pdftotext line-number anchor "
                    f"(forbidden — use section/example IDs, line numbers rot)"
                )

        # --- PROVENANCE HONESTY (codex P1.5) ---
        # paper_verbatim MUST carry a real verbatim_anchor; the maintainer-authored kinds MUST
        # NOT claim a verbatim_anchor and MUST carry their honesty markers.
        if ptype == "paper_verbatim":
            anchor = prov.get("verbatim_anchor")
            if not isinstance(anchor, str) or not anchor.strip():
                errors.append(
                    f"{where}: provenance_type=paper_verbatim but verbatim_anchor missing/empty "
                    f"(a first-party case must quote the paper)"
                )
            else:
                # The anchor must actually appear in the review_item_text being judged (codex P2):
                # otherwise the judged text could be paraphrased/maintainer-authored while a stale
                # anchor still labels it paper-verbatim — the exact provenance laundering this guards.
                rit = item.get("review_item_text")
                if isinstance(rit, str) and anchor.strip() not in rit:
                    errors.append(
                        f"{where}: paper_verbatim verbatim_anchor is not a substring of "
                        f"review_item_text (judged text must contain the quoted paper anchor)"
                    )
            # Symmetric honesty guard (codex P2 round 11): a paper_verbatim item must NOT carry the
            # maintainer-authored markers. Otherwise a `-cf` rewrite that keeps derived_from +
            # reviewer_source=maintainer_rewrite could be relabeled paper_verbatim and pass while
            # certifying maintainer text as first-party. A real first-party case has a human/AI
            # reviewer source and no derived_from.
            if item.get("derived_from") is not None:
                errors.append(
                    f"{where}: provenance_type=paper_verbatim must NOT carry derived_from "
                    f"(that is a maintainer-authored marker — a first-party case is not derived)"
                )
            rsrc = prov.get("reviewer_source")
            if rsrc not in ("human", "ai"):
                errors.append(
                    f"{where}: paper_verbatim provenance.reviewer_source={rsrc!r} must be 'human' "
                    f"or 'ai' (a maintainer source means it is not first-party)"
                )
        elif ptype == "counterfactual_rewrite":
            if prov.get("verbatim_anchor") not in (None, ""):
                errors.append(
                    f"{where}: counterfactual_rewrite must NOT carry a verbatim_anchor "
                    f"(it is maintainer-authored, not paper-verbatim)"
                )
            # derived_from must be a non-empty STRING (codex P2 round 9): a null/false/non-string
            # value would pass a str()-coerced presence check but then be skipped by the later
            # isinstance(df, str) source-invariant loop, letting the rewrite escape the
            # paper_verbatim-source + claim/verdict/framing checks entirely.
            df_val = item.get("derived_from")
            if not isinstance(df_val, str) or not df_val.strip():
                errors.append(f"{where}: counterfactual_rewrite missing a non-empty string derived_from")
            ser = item.get("semantic_equivalence_rationale")
            if not isinstance(ser, str) or not ser.strip():
                errors.append(f"{where}: counterfactual_rewrite missing semantic_equivalence_rationale")
            # Symmetric source honesty (codex P2 round 12): a maintainer-authored item must carry a
            # maintainer source, never human/ai — else a synthetic rewrite could be labelled
            # source-authored once the manifest is updated.
            if prov.get("reviewer_source") != "maintainer_rewrite":
                errors.append(
                    f"{where}: counterfactual_rewrite provenance.reviewer_source="
                    f"{prov.get('reviewer_source')!r} must be 'maintainer_rewrite' (it is maintainer-authored)"
                )
        elif ptype == "maintainer_boundary":
            if prov.get("verbatim_anchor") not in (None, ""):
                errors.append(
                    f"{where}: maintainer_boundary must NOT carry a verbatim_anchor "
                    f"(its review_item_text is synthetic)"
                )
            # mechanism_anchor must be a non-empty STRING (codex P2 round 12): a null/false value
            # would pass a str()-coerced check as 'None'/'False'.
            mech = prov.get("mechanism_anchor")
            if not isinstance(mech, str) or not mech.strip():
                errors.append(
                    f"{where}: maintainer_boundary missing a non-empty string provenance.mechanism_anchor "
                    f"(must anchor to the paper's mechanism sentence)"
                )
            if prov.get("reviewer_source") != "maintainer_synthetic":
                errors.append(
                    f"{where}: maintainer_boundary provenance.reviewer_source="
                    f"{prov.get('reviewer_source')!r} must be 'maintainer_synthetic' (it is maintainer-authored)"
                )

        # --- exception <-> reason pairing (both ways) ---
        # has_reason must require a real non-empty STRING (codex P2 round 12): str(None) is the
        # non-empty 'None', so a null exception_reason would otherwise read as present.
        is_exception = item.get("exception") is True
        reason_val = item.get("exception_reason")
        has_reason = isinstance(reason_val, str) and bool(reason_val.strip())
        if is_exception and not has_reason:
            errors.append(f"{where}: exception=true but exception_reason missing/empty")
        if not is_exception and has_reason:
            errors.append(f"{where}: exception_reason present but exception is not true")
        # An id declaring itself ambiguous MUST stay flagged, else it silently reverts to a
        # clean case (mirrors the #215 -exception guard).
        if isinstance(item_id, str) and item_id.endswith(EXCEPTION_ID_SUFFIX) and not is_exception:
            errors.append(
                f"{where}: id ends in {EXCEPTION_ID_SUFFIX!r} but exception is not true "
                f"(a declared boundary case must stay marked)"
            )

        pid = item.get("pair_id")
        if isinstance(pid, str) and pid.strip():
            pairs.setdefault(pid, []).append(item)

    # --- PAIR INVARIANTS (codex P1.3) ---
    # A pair (2 members) MUST share canonical_claim + expected_correctness and differ in
    # framing_style. Without this, "paired" items could silently drift to different claims or
    # the same style, and the framing-flip discipline would have no valid material.
    for pid, members in pairs.items():
        if len(members) != 2:
            errors.append(
                f"pair {pid!r}: has {len(members)} member(s); a pair must have exactly 2 "
                f"(one per framing_style)"
            )
            continue
        a, b = members
        if a.get("canonical_claim") != b.get("canonical_claim"):
            errors.append(f"pair {pid!r}: members have different canonical_claim (pair must hold claim constant)")
        if a.get("expected_correctness") != b.get("expected_correctness"):
            errors.append(
                f"pair {pid!r}: members have different expected_correctness "
                f"(framing must NOT change the expected verdict)"
            )
        if a.get("framing_style") == b.get("framing_style"):
            errors.append(
                f"pair {pid!r}: members share framing_style={a.get('framing_style')!r} "
                f"(a pair must contrast the two framing styles)"
            )

    # derived_from must point at a real item AND the counterfactual must hold the source's
    # invariants directly — same canonical_claim + expected_correctness, opposite framing_style
    # (codex P2). This is checked against the SOURCE, not via pair_id, so a rewrite that loses its
    # pair_id (and whose manifest pair is dropped with it) still cannot silently drift away from
    # the paper-verbatim case it claims to mirror — the pair-invariant loop alone would miss it.
    for item in items:
        df = item.get("derived_from")
        if not (isinstance(df, str) and df.strip()):
            continue
        where = item.get("id", "<no id>")
        source = by_id.get(df)
        if source is None:
            errors.append(f"{where!r}: derived_from={df!r} does not match any item id")
            continue
        # A rewrite must trace to a first-party paper_verbatim source — not another maintainer
        # item (codex P2). Otherwise the "traceable variant of a real example" contract breaks
        # and a non-paper source could pass provenance-honesty once the distribution is updated.
        if source.get("provenance_type") != "paper_verbatim":
            errors.append(
                f"{where!r}: derived_from={df!r} is provenance_type="
                f"{source.get('provenance_type')!r}; a rewrite must derive from a paper_verbatim item"
            )
        if item.get("canonical_claim") != source.get("canonical_claim"):
            errors.append(
                f"{where!r}: counterfactual canonical_claim differs from its derived_from source "
                f"{df!r} (a rewrite must hold the claim constant)"
            )
        if item.get("expected_correctness") != source.get("expected_correctness"):
            errors.append(
                f"{where!r}: counterfactual expected_correctness differs from its derived_from "
                f"source {df!r} (framing must NOT change the expected verdict)"
            )
        if item.get("framing_style") == source.get("framing_style"):
            errors.append(
                f"{where!r}: counterfactual shares framing_style with its derived_from source "
                f"{df!r} (a rewrite must contrast the framing style)"
            )

    # --- gold_set <-> manifest agreement ---
    if manifest is not None:
        if manifest.get("sample_n") != len(items):
            errors.append(
                f"manifest.sample_n={manifest.get('sample_n')} != item count {len(items)}"
            )
        actual_dist = Counter(i.get("provenance_type") for i in items)
        declared = {d.get("provenance_type"): d.get("n") for d in manifest.get("provenance_distribution", [])}
        if dict(actual_dist) != declared:
            errors.append(
                f"manifest.provenance_distribution {declared} != actual {dict(actual_dist)}"
            )
        man_pairs = {p.get("pair_id"): sorted(p.get("members", [])) for p in manifest.get("pairs", [])}
        gold_pairs = {pid: sorted(i.get("id") for i in m) for pid, m in pairs.items() if len(m) == 2}
        if man_pairs != gold_pairs:
            errors.append(f"manifest.pairs {man_pairs} != gold pairs {gold_pairs}")

    return errors


# The ONLY content key a judge may see for a gold item: the review item text to evaluate.
# WHITELIST, not blacklist — a blacklist would silently leak any field added later (e.g. the
# nested provenance.reviewer_source author label). The item's own `id` is NOT visible: the
# fixture IDs encode blind information (`sfp-001-cf` reveals counterfactual/provenance status,
# `sfp-005-ambiguous` reveals the expected boundary verdict — codex review P2), so the judge
# gets an OPAQUE handle DERIVED INTERNALLY from a position index, and the real id stays internal.
JUDGE_VISIBLE_CONTENT_KEY = "review_item_text"


def render_judge_view(item: dict[str, Any], index: int) -> dict[str, Any]:
    """Return the ONLY content a judge may see for a gold item: an opaque handle + the review
    text. This helper is the runtime enforcement point for id blinding, so it DERIVES the handle
    itself from a position `index` (e.g. ``item-0``) rather than accepting a caller-controlled
    string — a caller passing ``item["id"]`` could otherwise leak the answer-encoding suffix
    (codex review P2). The real fixture id is never copied.

    The index must be a real int (codex P2 round 10): if a caller passes a string — e.g. the
    fixture id or pair id — it would be interpolated into the supposedly opaque handle and leak
    an answer-encoding suffix. This is enforced at RUNTIME (a raise, not an assert) so it holds
    under ``python -O`` and does not depend on the per-item id check.

    This is the runtime-side enforcement of the #216 'invisible at judgment time' decision —
    framing_style, provenance_type, the verdict labels, the nested authorship signal
    (provenance.reviewer_source), AND the answer-encoding fixture id are all absent.
    """
    # bool is an int subclass; reject it too so True/False can't masquerade as an index.
    if not isinstance(index, int) or isinstance(index, bool):
        raise TypeError(
            f"render_judge_view index must be an int (position), got {type(index).__name__}: "
            f"{index!r} — a caller-controlled string handle would leak the answer-encoding id"
        )
    return {"handle": f"item-{index}", JUDGE_VISIBLE_CONTENT_KEY: item[JUDGE_VISIBLE_CONTENT_KEY]}


def _load_manifest(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    try:
        import yaml  # type: ignore
    except ImportError:
        return None
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("gold_set", nargs="?", type=Path, default=DEFAULT_GOLD_SET)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    args = parser.parse_args(argv)

    data = json.loads(args.gold_set.read_text(encoding="utf-8"))
    manifest = _load_manifest(args.manifest)

    # Guard the manifest shape BEFORE validate() (codex P3 round 9): a YAML scalar/list makes
    # _load_manifest return a non-dict, and passing it to validate() would call manifest.get and
    # raise AttributeError (a traceback) instead of the intended lint error. A missing manifest
    # (round 7) and a present-but-non-mapping manifest (round 8) both fail; only pass a real dict
    # — or None for a missing file — into validate().
    manifest_error: str | None = None
    if not args.manifest.exists():
        manifest_error = (
            f"manifest not found at {args.manifest} — the fixture would be undiscoverable by "
            f"run_evals and the gold<->manifest agreement checks cannot run"
        )
        manifest = None
    elif not isinstance(manifest, dict):
        manifest_error = (
            f"manifest at {args.manifest} is present but empty / null / non-mapping — the "
            f"gold<->manifest agreement checks cannot run and run_evals would crash on it"
        )
        manifest = None  # do not hand a non-dict to validate()

    errors = validate(data, manifest)
    if manifest_error:
        errors.append(manifest_error)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    n = len(data.get("items", []))
    print(f"surface_form_parity: {n} cases, all integrity/provenance/pair invariants pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
