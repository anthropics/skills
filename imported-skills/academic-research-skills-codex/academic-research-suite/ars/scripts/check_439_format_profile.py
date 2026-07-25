#!/usr/bin/env python3
"""#439 format_profile contract lint (spec docs/design/2026-06-15-439-format-profile-design.md).

Guards the scholar-declared layout profile schema (Slice A). The schema is a
RENDERER input, kept standalone from venue_profile (decision B). This lint pins
the load-bearing properties so they cannot be silently broken:

  1. The schema is a valid Draft 2020-12 schema, standalone (Invariant 11), and
     locks unknown keys (additionalProperties:false) at the root.
  2. The line_spacing.fixed_pt conditional is intact (required iff mode==fixed_pt,
     forbidden otherwise) — the rule that makes a mis-declared spacing a hard error
     rather than a silently-ignored field.
  3. NO provenance machinery leaked in from venue_profile (no declared_by, no
     *_inferred / *_provenance / *_source fields) — the downgraded declared-only
     rule (§3) is documentation, not an apparatus, and this asserts it stays that way.
  4. The cut fields stay cut (profile_name / heading_font / caption.bold) — the
     no-unrequested-abstraction discipline, enforced.
  5. The committed synthetic example fixture exists and validates against the
     schema (design §6/§8) — keeps the boundary-note artifact from drifting.
  6. The formatter's Format Profile section carries its load-bearing prose rules
     (byte-equivalence guard, fail-closed, no-inference, venue precedence,
     best-effort) — Slice C wiring, guarded by literal-presence like #394.
  7. The intake Step 5 follow-up carries the write-nothing-when-declined rule
     (Invariant 7 byte-equivalence) and the PCR row omission note.
  8. POSITIONING.md records the ship-contract-not-content boundary (#439 §6) —
     the mechanism ships, no specific school's/journal's profile content does.

Mutation discipline: scripts/test_check_439_format_profile.py proves each check
fires when its guarded property is broken.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

import yaml
from jsonschema import Draft202012Validator

if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
from _skill_lint import check_section_literals  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = ROOT / "shared" / "contracts" / "submission" / "format_profile.schema.json"
EXAMPLE = ROOT / "shared" / "contracts" / "submission" / "format_profile.example.yaml"
FORMATTER = ROOT / "academic-paper" / "agents" / "formatter_agent.md"
INTAKE = ROOT / "academic-paper" / "agents" / "intake_agent.md"
POSITIONING = ROOT / "POSITIONING.md"
FMT_HEADING = "## Format Profile (#439) — declared layout, NOT-DECLARED → current default"

# Fields that were deliberately cut (design §4) — must NOT reappear.
CUT_ROOT_FIELDS = ("profile_name", "heading_font")
CUT_CAPTION_FIELDS = ("bold",)
# venue_profile provenance machinery that must NOT carry over (design §3).
PROVENANCE_MARKERS = ("declared_by", "_inferred", "_provenance", "_source")


def check_schema_valid(schema: dict) -> list[str]:
    """Invariant 1: valid Draft 2020-12 schema, root locks unknown keys."""
    errors: list[str] = []
    try:
        Draft202012Validator.check_schema(schema)
    except Exception as exc:  # noqa: BLE001 - surface any schema-meta failure
        errors.append(f"format_profile schema is not a valid Draft 2020-12 schema: {exc}")
    if schema.get("additionalProperties") is not False:
        errors.append("format_profile root must set additionalProperties:false")
    if schema.get("type") != "object":
        errors.append("format_profile root type must be 'object'")
    return errors


def check_fixed_pt_conditional(schema: dict) -> list[str]:
    """Invariant 2: line_spacing.fixed_pt required iff mode==fixed_pt, else forbidden.

    Verified behaviorally (the conditional must actually reject the bad shapes),
    not by string-matching the allOf — a structural rename would slip past a grep.
    """
    errors: list[str] = []
    validator = Draft202012Validator(schema)

    def valid(inst: dict) -> bool:
        return not list(validator.iter_errors(inst))

    if not valid({"line_spacing": {"mode": "fixed_pt", "fixed_pt": 20}}):
        errors.append("line_spacing fixed_pt+fixed_pt should be VALID but is rejected")
    if not valid({"line_spacing": {"mode": "double"}}):
        errors.append("line_spacing double (no fixed_pt) should be VALID but is rejected")
    if valid({"line_spacing": {"mode": "double", "fixed_pt": 20}}):
        errors.append("line_spacing double WITH fixed_pt must be INVALID (fixed_pt only with mode==fixed_pt)")
    if valid({"line_spacing": {"mode": "fixed_pt"}}):
        errors.append("line_spacing fixed_pt WITHOUT fixed_pt must be INVALID (fixed_pt required when mode==fixed_pt)")
    if valid({"line_spacing": {"fixed_pt": 20}}):
        errors.append("line_spacing WITHOUT mode must be INVALID (mode is required) — guards against dropping required:[mode]")
    return errors


def _all_property_names(schema: dict) -> set[str]:
    """Recursively collect every declared property NAME in the schema.

    Structural only — descriptions are NOT walked, so the schema may *mention*
    'declared_by' in prose explaining that it carries no such field without the
    check false-firing on its own documentation.

    Walks only the applicators this schema actually uses (`properties`, `allOf`,
    `if`/`then`/`else`). If a future edit introduces `anyOf`/`oneOf`/`items`, that
    edit extends this walker in the same change — carrying dead branches now would
    be unrequested generality.
    """
    names: set[str] = set()
    props = schema.get("properties")
    if isinstance(props, dict):
        for name, subschema in props.items():
            names.add(name)
            if isinstance(subschema, dict):
                names |= _all_property_names(subschema)
    for branch in schema.get("allOf", []):
        if isinstance(branch, dict):
            names |= _all_property_names(branch)
    for key in ("if", "then", "else"):
        branch = schema.get(key)
        if isinstance(branch, dict):
            names |= _all_property_names(branch)
    return names


def check_no_provenance(schema: dict) -> list[str]:
    """Invariant 3: no venue_profile provenance machinery leaked in (§3 downgrade).

    Checks property NAMES only (not descriptions): a field whose name is or ends
    with a provenance marker. This catches `declared_by`, `body_font_provenance`,
    `venue_source`, `family_inferred`, while ignoring prose mentions.
    """
    errors: list[str] = []
    for name in _all_property_names(schema):
        # endswith subsumes exact-equality (declared_by) and catches the realistic
        # suffix leak (body_font_provenance ends with _provenance). The tested cases
        # are exactly these two shapes; an infix-marker rule would be untested scope.
        for marker in PROVENANCE_MARKERS:
            if name.endswith(marker):
                errors.append(
                    f"format_profile must NOT carry provenance machinery (field '{name}' "
                    f"matches '{marker}') — declared-only is downgraded to documentation, "
                    f"not an apparatus (design §3)"
                )
                break
    return errors


def check_cut_fields_stay_cut(schema: dict) -> list[str]:
    """Invariant 4: deliberately-cut fields must not reappear (design §4)."""
    errors: list[str] = []
    props = schema.get("properties", {})
    for field in CUT_ROOT_FIELDS:
        if field in props:
            errors.append(f"cut field '{field}' reappeared at root (design §4 — no concrete use case)")
    caption_props = props.get("caption", {}).get("properties", {})
    for field in CUT_CAPTION_FIELDS:
        if field in caption_props:
            errors.append(f"cut field 'caption.{field}' reappeared (design §4 — no #436 requirement)")
    return errors


def check_example_fixture(schema: dict) -> list[str]:
    """Invariant 5: the committed synthetic example validates against the schema (design §6/§8).

    Pins that the documentation artifact exists and stays schema-valid, so the
    boundary-note fixture (§6: must be synthetic, ships no real school profile)
    cannot silently drift out of contract.
    """
    if not EXAMPLE.exists():
        return [f"format_profile example fixture not found at {EXAMPLE} (design §6/§8)"]
    try:
        example = yaml.safe_load(EXAMPLE.read_text(encoding="utf-8"))
    except yaml.YAMLError as exc:
        return [f"format_profile example fixture is not valid YAML: {exc}"]
    schema_errors = list(Draft202012Validator(schema).iter_errors(example))
    return [
        f"format_profile example fixture violates the schema: {e.message}"
        for e in schema_errors
    ]


def check_formatter_wiring(text: str) -> list[str]:
    """Invariant 6: the formatter's Format Profile section carries its load-bearing rules.

    Slice C wiring is prose (LLM-agent behavior), so it is guarded by literal-presence
    the way the #394 formatter advisories are — a refactor that drops the byte-equivalence
    guard, the fail-closed STOP, or the venue-precedence rule fails loudly.
    """
    return check_section_literals(6, text, FMT_HEADING, "formatter format-profile", {
        "byte-equivalence guard (skip when no row)": "skip this entire section",
        "fail-closed before formatting": "fail closed BEFORE formatting",
        "no-inference rule": "Never infer a missing layout field",
        "venue precedence": "venue compliance wins",
        "best-effort per target": "best-effort per output target",
    })


STEP5_HEADING = "### Step 5: Output Format"
# The production Paper Configuration Record H2 — matched exactly so the Plan Mode PCR
# ("## Paper Configuration Record (Plan Mode)", which is exempt and carries no row) and
# the "### Paper Configuration Record" intro sub-heading are both excluded.
PCR_HEADING_RE = re.compile(r"^## Paper Configuration Record\s*$", re.MULTILINE)
# Structural table-row match for the PCR Format Profile row (mirrors check_392's PCR_ROW_RE).
PCR_FORMAT_ROW_RE = re.compile(r"^\|\s*\*\*Format Profile\*\*\s*\|", re.MULTILINE)


def _h2_block(text: str, heading_re: "re.Pattern[str]") -> str | None:
    """The block from an H2 heading (located by regex) to the next `## ` heading.

    Used to scope the production PCR table, matched exactly so the Plan Mode PCR variant
    and the intro sub-heading are excluded.
    """
    m = heading_re.search(text)
    if m is None:
        return None
    nxt = re.compile(r"^## \S", re.MULTILINE).search(text, m.end())
    return text[m.start() : nxt.start()] if nxt else text[m.start():]


def _step_block(text: str, heading: str) -> str | None:
    """The block from `heading` to the next heading of <= its level (None if absent).

    Scopes literal checks to the intake step rather than the whole 330-line file, so a
    rule moved out of Step 5 fails the lint instead of passing on a stray match elsewhere.
    """
    start = text.find(heading)
    if start < 0:
        return None
    level = heading.split(" ")[0]  # e.g. '###'
    pattern = re.compile(rf"^#{{2,{len(level)}}}\s", re.MULTILINE)
    m = pattern.search(text, start + len(heading))
    return text[start : m.start()] if m else text[start:]


def check_intake_wiring(text: str) -> list[str]:
    """Invariant 7: the intake Step 5 follow-up carries the write-nothing-when-declined rule.

    Scoped to the Step 5 block (not whole-file substring), so the byte-equivalence rule
    cannot pass the lint after being moved out of the follow-up; the PCR row is asserted
    structurally (a real table row), not by a prose fragment.
    """
    errors: list[str] = []
    step5 = _step_block(text, STEP5_HEADING)
    if step5 is None or "Format-profile follow-up (#439" not in step5:
        errors.append("intake_agent.md missing the #439 Format-profile follow-up under Step 5")
        return errors
    # the byte-equivalence discipline (declined => no PCR row at all) is load-bearing, in-step
    if "no PCR `Format Profile` row at all" not in step5:
        errors.append(
            "Step 5 follow-up must state a declined run writes NO PCR Format Profile row "
            "(Invariant 7 byte-equivalence — an explicit `absent` would perturb)"
        )
    # the PCR row exists as a real table row, scoped to the production PCR block
    # (not the Plan Mode PCR, and not a stray row elsewhere in the file)
    pcr_block = _h2_block(text, PCR_HEADING_RE)
    if pcr_block is None or not PCR_FORMAT_ROW_RE.search(pcr_block):
        errors.append("production PCR block must carry a structural `| **Format Profile** |` row")
    elif "ROW OMITTED ENTIRELY" not in pcr_block:
        errors.append("PCR Format Profile row must document that it is omitted when declined")
    return errors


def check_positioning_boundary(text: str) -> list[str]:
    """Invariant 8: POSITIONING.md records the #439 ship-contract-not-content boundary.

    The boundary (ARS ships the format_profile mechanism, never a specific school's/
    journal's profile content) is otherwise prose-only and unguarded — this pins that it
    stays recorded with its review criterion (design §6 acceptance).
    """
    errors: list[str] = []
    if "format-profile content" not in text.lower():
        errors.append("POSITIONING.md missing the #439 institutional/journal format-profile boundary note")
        return errors
    if "Review criterion:" not in text or "out-of-tree" not in text:
        errors.append("POSITIONING.md #439 boundary must keep its Review criterion + out-of-tree rule")
    return errors


def main() -> int:
    if not SCHEMA.exists():
        print(f"FAIL: schema not found at {SCHEMA}", file=sys.stderr)
        return 1
    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    errors: list[str] = []
    errors += check_schema_valid(schema)
    errors += check_fixed_pt_conditional(schema)
    errors += check_no_provenance(schema)
    errors += check_cut_fields_stay_cut(schema)
    errors += check_example_fixture(schema)
    errors += check_formatter_wiring(FORMATTER.read_text(encoding="utf-8"))
    errors += check_intake_wiring(INTAKE.read_text(encoding="utf-8"))
    errors += check_positioning_boundary(POSITIONING.read_text(encoding="utf-8"))

    if errors:
        print("#439 format_profile lint FAILED:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1
    print("#439 format_profile lint passed (8 invariants).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
