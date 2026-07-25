#!/usr/bin/env python3
"""verify_submission_package CLI — deterministic submission-package verifier
(#394; slices 1-2 shipped: Family C reference integrity + Family B venue
limits).

    python scripts/verify_submission_package.py <package_dir> \
        [--passport passport.yaml] [--join-map map.yaml] \
        [--venue-profile profile.yaml] [--report-out path]

Reads the files in an output package and runs the Family C two-way reference
integrity check (in-text citation keys <-> reference-list entries) plus the
Family B venue-limits checks (B1-B5, against a scholar-declared venue profile —
without one they report NOT-CHECKED, never a guess from the journal name),
writing `submission_verification_report.json` (validating against
shared/contracts/submission/submission_verification_report.schema.json) plus a
human-readable summary to stdout.

Design contract (spec docs/design/2026-06-10-394-submission-package-verifier-spec.md):

- Detection is unconditional; terminality is the policy evaluator's job. This
  script NEVER reads `terminal_policies` (§5.3) — `policy_slug` is emitted null.
- The joined marker path is deterministic; it needs a real prose-reference join
  (§3.3): the run's `citation_verification_summary[]` (via --passport), an
  explicit scholar-supplied join map (--join-map), or a package `.bib` whose
  keys map to slugs by the documented identity relation (draft_writer_agent.md:
  the slug IS the corpus `citation_key`). Markers with NO join source report
  `not_checked(missing prose-reference join)` — never a guessed comparison,
  and a slug an explicit join source does not cover is reported as unjoined,
  never identity-guessed.
- Fallback extraction (`\\cite{}` for LaTeX, author-year regex for Markdown
  text) is heuristic-classed: advisory-only, `strict_eligible: false`, header
  `extraction_path: best_effort` (§3.3).
- Every check reports pass | fail | warn | not_checked; `not_checked` is
  surfaced in the header count, never folded into pass (§1.4).
- `package_fingerprint` reuses the audit-snapshot manifest convention
  (scripts/audit_snapshot.py; spec §10 open item 3, adjudicated at slice 1):
  `<relative-path>:<sha256>` lines, byte-sorted, trailing newline, fingerprint
  = SHA-256 of the manifest text. The report file itself is excluded.

Exit codes: 0 = no fail (warns allowed) and everything checked; 1 = >=1 fail;
2 = usage/IO error; 3 = no fail but >=1 not_checked ("passed what was
checkable", §8).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import xml.etree.ElementTree as ET
import zipfile
from pathlib import Path
from typing import Any, Iterator, Optional

import yaml

try:
    from audit_snapshot import sha256_hex
except ImportError:  # pragma: no cover - dual-path import
    from scripts.audit_snapshot import sha256_hex

try:
    import pypdf
except ImportError:  # the A1 PDF scan reports NOT-CHECKED without it (§1.4)
    pypdf = None

try:
    # Hardened XML parsing (XML-bomb/XXE protection) when available; the
    # stdlib fallback does not fetch external entities but is exposed to
    # entity-expansion DoS — acceptable only because the input is the
    # scholar's own package, and requirements-dev installs the hardened path.
    from defusedxml.ElementTree import fromstring as _xml_fromstring
    from defusedxml.common import DefusedXmlException as _DefusedXmlException
except ImportError:
    _xml_fromstring = ET.fromstring

    class _DefusedXmlException(Exception):
        """Placeholder when defusedxml is absent — never raised."""


# A hardened-parser rejection (entity/DOCTYPE tricks) is an unreadable
# artifact, reported as NOT-CHECKED — it must not crash the scan.
_XML_READ_ERRORS = (zipfile.BadZipFile, ET.ParseError, OSError, KeyError,
                    ValueError, _DefusedXmlException)

# Zip-bomb guards for the raw DOCX part reads (read-only scan, no extraction
# — path traversal is not exposed, memory is).
_MAX_XML_PART_BYTES = 50 * 1024 * 1024
_MAX_ZIP_ENTRIES = 10_000

REPORT_BASENAME = "submission_verification_report.json"

# Files scanned for in-text citations. provenance_summary.md is an advisory
# carrier that legitimately repeats ref_slugs / citation_keys (#333) — scanning
# it would manufacture false in-text hits.
_MANUSCRIPT_SUFFIXES = {".md", ".tex", ".txt"}
_SCAN_EXCLUDED_NAMES = {"provenance_summary.md", REPORT_BASENAME}

# Files excluded from the package fingerprint (slice 4). Same two names as
# _SCAN_EXCLUDED_NAMES today, but DELIBERATELY a separate constant — the two
# sets answer different questions (scan: "is this manuscript prose?";
# fingerprint: "can this file change without invalidating the report?") and a
# future entry in one does not automatically belong in the other. The report
# cannot fingerprint its own bytes; provenance_summary.md is appended to by
# the formatter AFTER the report is stamped (the advisories section), so
# fingerprinting it would self-stale every evaluated report.
_FINGERPRINT_EXCLUDED_NAMES = frozenset({REPORT_BASENAME,
                                         "provenance_summary.md"})

# v3.7.1+ marker grammar with the canonical slug charset (the lint-side
# REF_PATTERN in check_v3_7_3_three_layer_citation.py). The suffix handling is
# deliberately broader than REF_PATTERN's `[^-]*?` status group: a finalized
# package carries `LOW-WARN` / `CONTAMINATED-*` suffix tokens (formatter
# pass-through allowlist) that REF_PATTERN does not match, and missing those
# markers here would fabricate orphans. Anchor markers (`<!--anchor:...-->`)
# are a different grammar and never match.
_REF_MARKER_RE = re.compile(r"<!--ref:([A-Za-z][A-Za-z0-9_:-]*)(?:\s[^>]*)?-->")

# BibTeX entry heads after an `^@` split: `article{key,`. @comment/@preamble/
# @string carry no citation key and are excluded.
_BIB_ENTRY_HEAD_RE = re.compile(
    r"(?!comment|preamble|string)[A-Za-z]+\s*\{\s*([^,\s}]+)\s*,",
    re.IGNORECASE,
)

_LOCATION_CAP = 5  # findings listed per check detail before truncation

# Check registry mirroring the spec §3 family tables: id -> (family,
# fail_capable, fixed_signal_class). strict_eligible = fail_capable AND
# deterministic signal (§3.1 separate axes; a warn-only check is never
# policy-promotable, §5.3). fixed_signal_class None = path-dependent (Family
# C: deterministic on the joined marker path, heuristic on the fallback); a
# non-None class is bound HERE and wins over the call site, so a
# structurally-heuristic check (slice 3's A5/A6) is excluded from strict by
# CLASS, never "defaulted out of it" (§3.1) — a forgotten kwarg cannot
# fail open. build_report enforces the roster: a runner that silently omits
# a registered check cannot emit a report (the §1.4/#349 fail-open guard).
_CHECK_REGISTRY = {
    "A1": ("blind_review_residue", True, "deterministic"),  # PDF metadata authors
    "A2": ("blind_review_residue", True, "deterministic"),  # DOCX metadata authors
    "A3": ("blind_review_residue", True, "deterministic"),  # DOCX revision/comment authors
    "A4": ("blind_review_residue", True, "deterministic"),  # acknowledgments in blind variant (strict only by profile declaration, §3.1)
    "A5": ("blind_review_residue", True, "heuristic"),      # self-citation phrasing
    "A6": ("blind_review_residue", True, "heuristic"),      # filename leakage
    "A7": ("blind_review_residue", True, "deterministic"),  # blind variant missing under declared double-blind
    "B1": ("venue_limits", True, "deterministic"),   # manuscript word count
    "B2": ("venue_limits", True, "deterministic"),   # abstract word count
    "B3": ("venue_limits", True, "deterministic"),   # keyword count range
    "B4": ("venue_limits", True, "deterministic"),   # required sections
    "B5": ("venue_limits", True, "deterministic"),   # reference count ceiling
    "C1": ("reference_integrity", True, None),
    "C2": ("reference_integrity", False, None),
}

# --- Fallback (best-effort) extraction grammar (§3.3, heuristic-classed) -----

# \cite / \citep / \citet / \citealp / starred forms, up to two optional args.
_LATEX_CITE_RE = re.compile(r"\\cite[a-zA-Z]*\*?(?:\[[^\]]*\]){0,2}\{([^}]*)\}")

# Reference-list section titles — the single source for BOTH the fallback
# prose-scan boundary (Family C) and the B1 body_only word-count scope; one
# list so the two checks can never disagree about where the references start.
_REFS_TITLES = ("references", "bibliography", "參考文獻")
_REFS_HEADING_RE = re.compile(
    r"^#{0,6}\s*(?:" + "|".join(_REFS_TITLES) + r")\s*$",
    re.IGNORECASE | re.MULTILINE,
)

_NAME = r"[A-Z][\w'’-]+"
# Narrative: `Smith (2024)`, `Smith et al. (2024)`, `Smith and Chen (2024)`,
# with an optional page-locator tail: `Smith (2024, p. 12)`.
_NARRATIVE_CITE_RE = re.compile(
    r"(" + _NAME + r")(?:\s+et al\.?|\s+(?:and|&)\s+" + _NAME + r")?"
    r"\s+\((\d{4})[a-z]?(?:\s*,\s*pp?\.?[^)]*)?\)")
# Parenthetical group content is split on `;` and each segment matched:
# `(Smith, 2024)`, `(Chen & Lee, 2023)`, `(Smith et al., 2024a)`,
# `(Chen & Lee, 2023, pp. 45–67)`.
_PAREN_GROUP_RE = re.compile(r"\(([^()]+)\)")
_PAREN_SEGMENT_RE = re.compile(
    r"^\s*(" + _NAME + r")[^\d]*?(\d{4})[a-z]?(?:\s*,\s*pp?\.?[^;]*)?\s*$")


def compute_package_fingerprint(package_dir: Path,
                                report_relpath: Optional[str] = None) -> str:
    """Audit-snapshot manifest convention over the package files (§10 item 3):
    one `<package-relative-path>:<sha256>` line per file, LC_ALL=C byte-sorted,
    trailing newline; fingerprint = SHA-256 of the manifest text. The report
    file is excluded — the report cannot fingerprint its own bytes — including
    a custom --report-out path inside the package (report_relpath, as a
    package-relative posix path), or reruns would self-reference.
    provenance_summary.md is excluded too (slice 4): it is the pipeline's own
    advisory carrier — the formatter appends the Submission Package Advisories
    section AFTER the report is stamped, which would otherwise immediately
    stale the very report whose findings it carries. The freshness guard's
    threat model is manuscript/package drift, not the advisory carrier."""
    excluded = _FINGERPRINT_EXCLUDED_NAMES | {report_relpath}
    lines = []
    for path in package_dir.rglob("*"):
        if not path.is_file():
            continue
        rel = path.relative_to(package_dir).as_posix()
        if rel in excluded:
            continue
        lines.append(f"{rel}:{sha256_hex(path.read_bytes())}")
    lines.sort()  # byte sort over the composed line, matching audit_snapshot
    manifest_text = "\n".join(lines) + "\n"
    return sha256_hex(manifest_text.encode("utf-8"))


def compute_inputs_fingerprint(venue_profile_path: Optional[str],
                               join_map_path: Optional[str],
                               passport_path: Optional[str]) -> str:
    """SHA-256 over the external-inputs manifest (gate-2 review P1): one
    `<name>:<sha256-of-file-bytes|absent>` line per input, sorted by name,
    trailing newline. Family B/C verdicts depend on these inputs, so the
    freshness guard must see them — the package fingerprint alone cannot
    (the inputs live outside the package). An absent input hashes as the
    literal token `absent`, so declared→absent is a visible change."""
    lines = []
    for name, raw in (("join_map", join_map_path),
                      ("passport", passport_path),
                      ("venue_profile", venue_profile_path)):
        digest = sha256_hex(Path(raw).read_bytes()) if raw else "absent"
        lines.append(f"{name}:{digest}")
    manifest_text = "\n".join(sorted(lines)) + "\n"
    return sha256_hex(manifest_text.encode("utf-8"))


def _collect_package_texts(package_dir: Path
                           ) -> tuple[dict[str, str], dict[str, str]]:
    """One walk, one read per file: ({manuscript rel: text}, {bib rel: text})."""
    manuscripts: dict[str, str] = {}
    bibs: dict[str, str] = {}
    for path in sorted(package_dir.rglob("*")):
        if not path.is_file() or path.name in _SCAN_EXCLUDED_NAMES:
            continue
        suffix = path.suffix.lower()
        if suffix not in _MANUSCRIPT_SUFFIXES and suffix != ".bib":
            continue
        rel = path.relative_to(package_dir).as_posix()
        text = path.read_text(encoding="utf-8", errors="replace")
        (bibs if suffix == ".bib" else manuscripts)[rel] = text
    return manuscripts, bibs


def extract_ref_markers(manuscripts: dict[str, str]) -> dict[str, str]:
    """{slug: first-seen package-relative location} from <!--ref:slug--> markers."""
    found: dict[str, str] = {}
    for rel in sorted(manuscripts):
        for m in _REF_MARKER_RE.finditer(manuscripts[rel]):
            found.setdefault(m.group(1), rel)
    return found


def _iter_bib_entries(bibs: dict[str, str]) -> Iterator[tuple[str, str]]:
    """Yield (citation_key, raw entry body) per BibTeX entry across the
    package's .bib files — the single entry-head grammar both the key set and
    the author-year metadata derive from, so they cannot drift."""
    for rel in sorted(bibs):
        for chunk in re.split(r"(?m)^\s*@", bibs[rel])[1:]:
            head = _BIB_ENTRY_HEAD_RE.match(chunk)
            if head:
                yield head.group(1), chunk


def parse_bib_keys(bibs: dict[str, str]) -> set[str]:
    return {key for key, _body in _iter_bib_entries(bibs)}


def _parse_bib_metadata(bibs: dict[str, str]) -> dict[tuple, set]:
    """{(first-author-surname-lower, year): {citation_key, ...}} from package
    .bib entries, for author-year fallback matching. Best-effort field parsing
    — the whole fallback path is heuristic-classed anyway (§3.3)."""
    metadata: dict[tuple, set] = {}
    for key, body in _iter_bib_entries(bibs):
        author = re.search(r"author\s*=\s*[{\"]([^}\"]+)", body, re.IGNORECASE)
        year = re.search(r"year\s*=\s*[{\"]?(\d{4})", body, re.IGNORECASE)
        if not (author and year):
            continue
        surname = _first_author_surname(author.group(1))
        if surname:
            metadata.setdefault(
                (surname.lower(), year.group(1)), set()).add(key)
    return metadata


def _first_author_surname(author_field: str) -> str:
    first = author_field.split(" and ")[0].strip()
    if "," in first:
        return first.split(",")[0].strip()
    parts = first.split()
    return parts[-1] if parts else ""


def _corpus_metadata(passport: dict[str, Any]) -> dict[tuple, set]:
    metadata: dict[tuple, set] = {}
    for e in passport.get("literature_corpus") or []:
        key = e.get("citation_key")
        year = e.get("year")
        authors = e.get("authors") or []
        family = authors[0].get("family") if (
            authors and isinstance(authors[0], dict)) else None
        if isinstance(key, str) and family and year is not None:
            metadata.setdefault((str(family).lower(), str(year)), set()).add(key)
    return metadata


def _strip_reference_section(text: str) -> str:
    m = _REFS_HEADING_RE.search(text)
    return text[: m.start()] if m else text


def _extract_fallback(manuscripts: dict[str, str],
                      metadata: dict[tuple, set]
                      ) -> tuple[dict[str, str], dict[str, str]]:
    """Best-effort in-text extraction (§3.3 fallback path): \\cite{} keys from
    .tex, author-year hits from .md/.txt matched against reference metadata.
    Returns (in_text {citation_key: location}, unresolved {display token:
    location}) — unresolved hits stay out of the citation-key namespace so a
    key that textually equals the token never silently merges."""
    in_text: dict[str, str] = {}
    unresolved: dict[str, str] = {}
    for rel in sorted(manuscripts):
        text = manuscripts[rel]
        if rel.lower().endswith(".tex"):
            for m in _LATEX_CITE_RE.finditer(text):
                for key in m.group(1).split(","):
                    key = key.strip()
                    if key:
                        in_text.setdefault(key, rel)
            continue
        prose = _strip_reference_section(text)
        hits = [(m.group(1), m.group(2))
                for m in _NARRATIVE_CITE_RE.finditer(prose)]
        for g in _PAREN_GROUP_RE.finditer(prose):
            for segment in g.group(1).split(";"):
                m = _PAREN_SEGMENT_RE.match(segment)
                if m:
                    hits.append((m.group(1), m.group(2)))
        for surname, year in hits:
            keys = metadata.get((surname.lower(), year))
            if keys:
                for key in keys:
                    in_text.setdefault(key, rel)
            else:
                unresolved.setdefault(f"{surname} ({year})", rel)
    return in_text, unresolved


def _check(check_id: str, status: str, detail: str, *,
           signal_class: str = "deterministic",
           location: Optional[str] = None,
           strict_eligible: Optional[bool] = None) -> dict[str, Any]:
    family, fail_capable, fixed_class = _CHECK_REGISTRY[check_id]
    if fixed_class is not None:
        signal_class = fixed_class  # registry-bound class wins (§3.1)
    eligible = fail_capable and signal_class == "deterministic"
    if strict_eligible is not None:
        # Downward-only override: a call site can RESTRICT eligibility (A4 is
        # advisory unless the venue profile declares acknowledgments must be
        # removed, §3.1) but can never promote past the class rule above.
        eligible = eligible and strict_eligible
    return {
        "id": check_id,
        "family": family,
        "signal_class": signal_class,
        "strict_eligible": eligible,
        "status": status,
        "detail": detail,
        "location": location,
    }


def _not_checked_pair(reason: str) -> list[dict[str, Any]]:
    return [
        _check("C1", "not_checked", reason),
        _check("C2", "not_checked", reason),
    ]


def _listed(keys: set[str]) -> str:
    shown = sorted(keys)[:_LOCATION_CAP]
    extra = len(keys) - len(shown)
    listing = ", ".join(shown)
    if extra > 0:
        listing += f", … (+{extra} more)"
    return listing


def _compare_sets(in_text: dict[str, str], reference_keys: set[str],
                  *, signal_class: str, in_text_label: str,
                  reference_label: str,
                  unjoined: Optional[dict[str, str]] = None,
                  unjoined_label: str = ("with no join entry in the supplied "
                                         "join source")
                  ) -> list[dict[str, Any]]:
    """Two-way set check (§3.3): orphan in-text citation = fail (C1); uncited
    reference entry = warn (C2 — some venues allow further-reading entries).
    `unjoined` carries in-text hits that cannot be placed in the citation-key
    namespace (marker slugs the join source does not cover; fallback hits with
    no metadata match): they are a C1 fail in their own right — NEVER compared
    via an identity guess (§3.3), which would silently pass a slug that
    coincidentally equals a citation_key."""
    unjoined = unjoined or {}
    orphans = {k for k in in_text if k not in reference_keys}
    uncited = reference_keys - set(in_text)
    checks = []
    if orphans or unjoined:
        parts = []
        if orphans:
            parts.append(
                f"{len(orphans)} in-text citation(s) absent from "
                f"{reference_label}: {_listed(orphans)}")
        if unjoined:
            parts.append(
                f"{len(unjoined)} in-text citation(s) {unjoined_label}: "
                f"{_listed(set(unjoined))}")
        first_loc = min(
            [in_text[k] for k in orphans] + list(unjoined.values()))
        checks.append(_check(
            "C1", "fail",
            "; ".join(parts) + f" [{in_text_label}]",
            signal_class=signal_class, location=first_loc))
    else:
        checks.append(_check(
            "C1", "pass",
            f"all {len(in_text)} in-text citation(s) present in "
            f"{reference_label} [{in_text_label}]",
            signal_class=signal_class))
    if uncited:
        checks.append(_check(
            "C2", "warn",
            f"{len(uncited)} reference entr(ies) never cited in text: "
            f"{_listed(uncited)} [{in_text_label}]",
            signal_class=signal_class))
    else:
        checks.append(_check(
            "C2", "pass",
            f"all {len(reference_keys)} reference entr(ies) cited in text "
            f"[{in_text_label}]",
            signal_class=signal_class))
    return checks


def _load_yaml(path: Path) -> dict[str, Any]:
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"expected a YAML mapping in {path}")
    return data


def _join_from_passport(passport: dict[str, Any]) -> dict[str, str]:
    """{ref_slug: citation_key} from the passport's
    citation_verification_summary[] rows (the per-citation prose join the
    Stage 4->5 run already established, §3.3)."""
    join: dict[str, str] = {}
    for row in passport.get("citation_verification_summary") or []:
        slug = row.get("ref_slug")
        key = row.get("citation_key")
        if isinstance(slug, str) and slug and isinstance(key, str) and key:
            join[slug] = key
    return join


def _corpus_keys(passport: dict[str, Any]) -> set[str]:
    return {
        e.get("citation_key")
        for e in passport.get("literature_corpus") or []
        if isinstance(e.get("citation_key"), str)
    }


_NO_REFERENCE_LIST_REASON = (
    "no machine-readable reference list (no package .bib and no "
    "passport literature_corpus[])")
_NO_MANUSCRIPT_REASON = (
    "no manuscript found (no .md/.tex/.txt file in the package)")


def _reference_list(bib_keys: set[str],
                    passport: Optional[dict[str, Any]]
                    ) -> tuple[set[str], str]:
    """The machine-readable reference list both Family C and B5 compare
    against: package .bib keys, or the passport's declared
    literature_corpus[] keys. Empty set + empty label = no source."""
    if bib_keys:
        return bib_keys, "the package .bib reference list"
    corpus_keys = _corpus_keys(passport) if passport else set()
    if corpus_keys:
        return corpus_keys, "the passport literature_corpus reference list"
    return set(), ""


def run_family_c(manuscripts: dict[str, str], bibs: dict[str, str],
                 bib_keys: set[str],
                 reference_keys: set[str], reference_label: str,
                 passport: Optional[dict[str, Any]] = None,
                 join_map: Optional[dict[str, str]] = None
                 ) -> tuple[list[dict[str, Any]], str]:
    """Run Family C over the collected package texts.
    Returns (checks, extraction_path)."""
    if not manuscripts:
        return _not_checked_pair(_NO_MANUSCRIPT_REASON), "none"

    markers = extract_ref_markers(manuscripts)
    summary_join = _join_from_passport(passport) if passport else {}

    if not reference_keys:
        return _not_checked_pair(_NO_REFERENCE_LIST_REASON), "none"

    if markers:
        # Joined marker path (deterministic). Join precedence: explicit
        # scholar-supplied map > the run's citation_verification_summary[] >
        # .bib identity relation.
        if join_map is not None:
            join: Optional[dict[str, str]] = dict(join_map)
        elif summary_join:
            join = summary_join
        elif bib_keys:
            # Documented identity relation (draft_writer_agent.md: the slug IS
            # the corpus citation_key): every marker slug joins to itself, so
            # a slug that is not a .bib key is simply an orphan.
            join = None
        else:
            return _not_checked_pair(
                "missing prose-reference join: <!--ref:slug--> markers found "
                "but no citation_verification_summary, --join-map, or package "
                ".bib supplies the slug->citation_key join (§3.3 — never a "
                "guessed comparison)"), "none"
        if join is None:  # .bib identity relation
            in_text, unjoined = dict(markers), {}
        else:
            # An explicit join source (summary / --join-map) must cover every
            # cited slug; a slug it does not cover is reported as such — NEVER
            # compared via an identity guess, which would silently pass a slug
            # that coincidentally equals a citation_key (§3.3).
            in_text, unjoined = {}, {}
            for slug, loc in markers.items():
                if slug in join:
                    in_text.setdefault(join[slug], loc)
                else:
                    unjoined.setdefault(slug, loc)
        return _compare_sets(
            in_text, reference_keys, signal_class="deterministic",
            in_text_label="joined marker path",
            reference_label=reference_label, unjoined=unjoined), "joined_marker"

    # Fallback path (§3.3): no markers — non-ARS or post-converted source.
    # Format-aware best-effort extraction, heuristic-classed (advisory-only).
    metadata = _parse_bib_metadata(bibs)
    if passport:
        for k, v in _corpus_metadata(passport).items():
            metadata.setdefault(k, set()).update(v)
    in_text, unresolved = _extract_fallback(manuscripts, metadata)
    return _compare_sets(
        in_text, reference_keys, signal_class="heuristic",
        in_text_label="best-effort extraction",
        reference_label=reference_label, unjoined=unresolved,
        unjoined_label="unmatched against any reference metadata"
        ), "best_effort"


_FAMILY_B_IDS = tuple(
    cid for cid, (fam, _fc, _sc) in sorted(_CHECK_REGISTRY.items())
    if fam == "venue_limits")

_WORD_COUNT_TOLERANCE = 1.02  # §3.2: ±2% before fail (format-conversion noise)

_MD_HEADING_RE = re.compile(r"^(#{1,6})\s+(.+?)\s*#*\s*$", re.MULTILINE)
_KEYWORDS_LINE_RE = re.compile(
    r"^\s*(?:\*\*|__)?\s*keywords?\s*(?:\*\*|__)?\s*[:：]\s*(.+?)\s*$",
    re.IGNORECASE | re.MULTILINE)
_TEX_KEYWORDS_RE = re.compile(r"\\keywords\s*\{([^}]*)\}", re.IGNORECASE)
_TEX_SECTION_RE = re.compile(r"\\(?:sub)*section\*?\s*\{([^}]*)\}")
_TEX_ABSTRACT_RE = re.compile(
    r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.DOTALL)
_TEX_BIBLIO_RE = re.compile(
    r"\\begin\{thebibliography\}.*?\\end\{thebibliography\}|\\bibliography\s*\{[^}]*\}",
    re.DOTALL)
_HTML_COMMENT_RE = re.compile(r"<!--.*?-->", re.DOTALL)


def _word_count(text: str) -> int:
    """Canonical whitespace-split (shared/references/word_count_conventions.md)."""
    return len(text.split())


def _md_sections(text: str) -> list[tuple[str, int, int]]:
    """[(heading title, content start, content end)] per markdown section."""
    heads = list(_MD_HEADING_RE.finditer(text))
    return [(m.group(2).strip(),
             m.end(),
             heads[i + 1].start() if i + 1 < len(heads) else len(text))
            for i, m in enumerate(heads)]


def _is_abstract_title(title: str) -> bool:
    return title.lower().strip("*_ ").startswith("abstract")


def _is_refs_title(title: str) -> bool:
    return title.lower().strip("*_ ") in _REFS_TITLES


def _md_drop_sections(text: str, title_predicates) -> str:
    """Remove every section (heading included) whose title matches any
    predicate."""
    heads = list(_MD_HEADING_RE.finditer(text))
    keep, cursor = [], 0
    for i, m in enumerate(heads):
        end = heads[i + 1].start() if i + 1 < len(heads) else len(text)
        if any(p(m.group(2).strip()) for p in title_predicates):
            keep.append(text[cursor:m.start()])
            cursor = end
    keep.append(text[cursor:])
    return "".join(keep)


def _detex(text: str) -> str:
    """Naive detex (§10 item 4, adjudicated at slice 2: naive detex +
    whitespace-split, the method is DECLARED in the report and never promised
    venue-exact): drop comments and \\commands, unwrap braces/brackets."""
    text = re.sub(r"(?<!\\)%.*", " ", text)
    text = re.sub(r"\\[a-zA-Z]+\*?", " ", text)
    return re.sub(r"[{}\[\]]", " ", text)


def _countable_body(rel: str, text: str, scope: str) -> tuple[str, str]:
    """(countable text, human description of what was counted) for B1."""
    if rel.lower().endswith(".tex"):
        if scope == "body_only":
            return (_detex(_TEX_BIBLIO_RE.sub(
                        " ", _TEX_ABSTRACT_RE.sub(" ", text))),
                    "naive detex; abstract + bibliography excluded")
        if scope == "body_plus_references":
            return (_detex(_TEX_ABSTRACT_RE.sub(" ", text)),
                    "naive detex; abstract excluded")
        return _detex(text), "naive detex; everything counted"
    text = _HTML_COMMENT_RE.sub(" ", text)
    if scope == "body_only":
        return (_md_drop_sections(_KEYWORDS_LINE_RE.sub(" ", text),
                                  (_is_abstract_title, _is_refs_title)),
                "abstract + references + keywords line excluded")
    if scope == "body_plus_references":
        return (_md_drop_sections(_KEYWORDS_LINE_RE.sub(" ", text),
                                  (_is_abstract_title,)),
                "abstract + keywords line excluded")
    # `all` counts everything the author wrote — only the ARS tool markers
    # (HTML comments) are stripped, and that is declared.
    return text, "everything counted (tool markers stripped)"


def _abstract_text(rel: str, text: str) -> Optional[str]:
    if rel.lower().endswith(".tex"):
        m = _TEX_ABSTRACT_RE.search(text)
        return _detex(m.group(1)) if m else None
    for title, start, end in _md_sections(text):
        if _is_abstract_title(title):
            body = _HTML_COMMENT_RE.sub(" ", text[start:end])
            return _KEYWORDS_LINE_RE.sub(" ", body)
    return None


def _keyword_list(text: str) -> Optional[list[str]]:
    m = _KEYWORDS_LINE_RE.search(text) or _TEX_KEYWORDS_RE.search(text)
    if not m:
        return None
    return [k for k in re.split(r"[,;、；]", m.group(1)) if k.strip()]


def _headings(rel: str, text: str) -> list[str]:
    if rel.lower().endswith(".tex"):
        return [m.group(1).strip() for m in _TEX_SECTION_RE.finditer(text)]
    return [t for t, _s, _e in _md_sections(text)]


_CANONICAL_MANUSCRIPT_STEMS = frozenset({"paper", "manuscript", "main"})
_NON_MANUSCRIPT_PREFIXES = (
    "cover_letter", "cover-letter", "response", "rebuttal", "readme")


def _primary_manuscript(manuscripts: dict[str, str]
                        ) -> tuple[Optional[str], Optional[str], Optional[str]]:
    """(rel, text, blocked_reason) — the manuscript the limits are checked
    against; rel/text are None iff blocked_reason says why. Canonical
    filenames (paper/manuscript/main) win; known package-document names
    (cover letters, response letters, READMEs) are excluded; with several
    remaining non-canonical candidates the verifier reports ambiguity instead
    of silently picking the wordiest (it could be an appendix or a response
    letter). Which file was counted is declared in every detail string."""
    if not manuscripts:
        return None, None, _NO_MANUSCRIPT_REASON
    candidates = {
        rel: t for rel, t in manuscripts.items()
        if not Path(rel).name.lower().startswith(_NON_MANUSCRIPT_PREFIXES)}
    candidates = candidates or manuscripts
    canonical = {rel: t for rel, t in candidates.items()
                 if Path(rel).stem.lower() in _CANONICAL_MANUSCRIPT_STEMS}
    pool = canonical or candidates
    if not canonical and len(candidates) > 1:
        return None, None, (
            "ambiguous manuscript: several candidates and none carries a "
            f"canonical name (paper/manuscript/main): "
            f"{', '.join(sorted(candidates))} — rename the manuscript or "
            "remove the extras")
    rel = max(sorted(pool), key=lambda r: _word_count(pool[r]))
    return rel, pool[rel], None


def _ceiling_check(check_id: str, count: int, limit: int, what: str,
                   location: Optional[str] = None,
                   tolerance: float = 1.0) -> dict[str, Any]:
    tol_note = " (±2% tolerance)" if tolerance > 1.0 else ""
    status = "pass" if count <= limit * tolerance else "fail"
    return _check(check_id, status,
                  f"{what}: {count} vs declared limit {limit}{tol_note}",
                  location=location)


def run_family_b(manuscripts: dict[str, str],
                 reference_keys: set[str], reference_label: str,
                 profile: Optional[dict[str, Any]]
                 ) -> list[dict[str, Any]]:
    """Family B: venue-declared limits vs actuals (§3.2). Without a profile,
    every check is NOT-CHECKED — limits are never guessed from the journal
    name (R-L3-2-D mirror). A partially-declared profile runs the checks it
    can and NOT-CHECKEDs the rest (§4)."""
    if profile is None:
        return [_check(i, "not_checked",
                       "no venue profile declared — limits are never guessed "
                       "from the journal name (R-L3-2-D mirror)")
                for i in _FAMILY_B_IDS]

    checks: list[dict[str, Any]] = []
    rel, text, no_manuscript_reason = _primary_manuscript(manuscripts)

    def not_declared(check_id: str, field: str) -> dict[str, Any]:
        return _check(check_id, "not_checked",
                      f"{field} not declared in venue profile")

    # B1 — manuscript word count vs word_limit (±2%, §3.2)
    word_limit = profile.get("word_limit")
    if word_limit is None:
        checks.append(not_declared("B1", "word_limit"))
    elif rel is None:
        checks.append(_check("B1", "not_checked", no_manuscript_reason))
    else:
        scope = profile.get("word_count_scope")
        scope_decl = scope or "body_only (default — scope not declared)"
        body, counted_desc = _countable_body(rel, text, scope or "body_only")
        checks.append(_ceiling_check(
            "B1", _word_count(body), word_limit,
            f"manuscript word count of {rel}, scope {scope_decl} "
            f"({counted_desc}; whitespace-split per "
            f"shared/references/word_count_conventions.md)",
            location=rel, tolerance=_WORD_COUNT_TOLERANCE))

    # B2 — abstract word count vs abstract_word_limit (±2%)
    abstract_limit = profile.get("abstract_word_limit")
    if abstract_limit is None:
        checks.append(not_declared("B2", "abstract_word_limit"))
    elif rel is None:
        checks.append(_check("B2", "not_checked", no_manuscript_reason))
    else:
        abstract = _abstract_text(rel, text)
        if abstract is None:
            checks.append(_check(
                "B2", "not_checked",
                f"no abstract section found in {rel}", location=rel))
        else:
            checks.append(_ceiling_check(
                "B2", _word_count(abstract), abstract_limit,
                f"abstract word count of {rel} (whitespace-split)",
                location=rel, tolerance=_WORD_COUNT_TOLERANCE))

    # B3 — keyword count vs keyword_range (exact)
    keyword_range = profile.get("keyword_range")
    if keyword_range is None:
        checks.append(not_declared("B3", "keyword_range"))
    elif rel is None:
        checks.append(_check("B3", "not_checked", no_manuscript_reason))
    else:
        keywords = _keyword_list(text)
        if keywords is None:
            checks.append(_check(
                "B3", "not_checked",
                f"no keywords line found in {rel}", location=rel))
        else:
            lo, hi = keyword_range["min"], keyword_range["max"]
            ok = lo <= len(keywords) <= hi
            checks.append(_check(
                "B3", "pass" if ok else "fail",
                f"keyword count of {rel}: {len(keywords)} vs declared range "
                f"{lo}–{hi}", location=rel))

    # B4 — required sections present (set comparison)
    required = profile.get("required_sections")
    if required is None:
        checks.append(not_declared("B4", "required_sections"))
    elif rel is None:
        checks.append(_check("B4", "not_checked", no_manuscript_reason))
    else:
        headings = [h.lower() for h in _headings(rel, text)]
        missing = [s for s in required
                   if not any(s.lower() in h for h in headings)]
        if missing:
            checks.append(_check(
                "B4", "fail",
                f"required section(s) missing from {rel} (case-insensitive "
                f"heading containment): {', '.join(missing)}", location=rel))
        else:
            checks.append(_check(
                "B4", "pass",
                f"all {len(required)} required section(s) present in {rel}",
                location=rel))

    # B5 — reference count vs reference_limit (exact)
    reference_limit = profile.get("reference_limit")
    if reference_limit is None:
        checks.append(not_declared("B5", "reference_limit"))
    elif not reference_keys:
        checks.append(_check("B5", "not_checked", _NO_REFERENCE_LIST_REASON))
    else:
        checks.append(_ceiling_check(
            "B5", len(reference_keys), reference_limit,
            f"reference entries in {reference_label}"))

    return checks


_PROFILE_SCHEMA_PATH = (
    Path(__file__).resolve().parent.parent / "shared" / "contracts"
    / "submission" / "venue_profile.schema.json")
_profile_schema_cache: Optional[dict[str, Any]] = None


def _profile_schema() -> dict[str, Any]:
    """The formal venue-profile contract, loaded once. The validator derives
    its allowed-field set and enums FROM the schema file so the contract has
    one source of truth (a schema edit cannot silently desync the CLI gate)."""
    global _profile_schema_cache
    if _profile_schema_cache is None:
        _profile_schema_cache = json.loads(
            _PROFILE_SCHEMA_PATH.read_text(encoding="utf-8"))
    return _profile_schema_cache


def _schema_enum(field: str) -> tuple:
    return tuple(v for v in _profile_schema()["properties"][field]["enum"]
                 if v is not None)


def _is_int(v: Any) -> bool:
    """A real integer — bool is an int subclass and must not pass as one."""
    return isinstance(v, int) and not isinstance(v, bool)


def _validate_venue_profile(raw: dict[str, Any]) -> dict[str, Any]:
    """Shape validation for a --venue-profile file. The allowed-field set and
    enums are derived from the formal contract
    (shared/contracts/submission/venue_profile.schema.json,
    additionalProperties false included) so a malformed or typoed profile is a
    usage error, never a silently-skewed or silently-skipped comparison."""
    allowed = set(_profile_schema()["properties"])
    unknown = set(raw) - allowed
    if unknown:
        raise ValueError(
            f"venue profile has unknown field(s) {sorted(unknown)} — the "
            f"schema is closed (a typoed limit would otherwise be silently "
            f"ignored); allowed: {sorted(allowed)}")
    if raw.get("declared_by") != "scholar":
        raise ValueError(
            "venue profile must carry `declared_by: scholar` — the profile is "
            "scholar-declared only, never scraped or inferred (spec §4)")
    name = raw.get("venue_name")
    if name is not None and not isinstance(name, str):
        raise ValueError(f"venue profile venue_name must be a string or null, "
                         f"got {name!r}")
    for field in ("word_limit", "abstract_word_limit", "reference_limit"):
        v = raw.get(field)
        if v is not None and (not _is_int(v) or v < 1):
            raise ValueError(f"venue profile {field} must be a positive "
                             f"integer or null, got {v!r}")
    scope = raw.get("word_count_scope")
    if scope is not None and scope not in _schema_enum("word_count_scope"):
        raise ValueError(f"venue profile word_count_scope must be one of "
                         f"{'/'.join(_schema_enum('word_count_scope'))}/null, "
                         f"got {scope!r}")
    blind = raw.get("blind_review")
    if blind is not None and blind not in _schema_enum("blind_review"):
        raise ValueError(f"venue profile blind_review must be one of "
                         f"{'/'.join(_schema_enum('blind_review'))}/null, "
                         f"got {blind!r}")
    kr = raw.get("keyword_range")
    if kr is not None:
        if (not isinstance(kr, dict) or set(kr) != {"min", "max"}
                or not _is_int(kr.get("min")) or kr["min"] < 0
                or not _is_int(kr.get("max")) or kr["max"] < 1
                or kr["min"] > kr["max"]):
            raise ValueError(
                f"venue profile keyword_range must be {{min >= 0, max >= 1}} "
                f"integers with min <= max, got {kr!r}")
    sections = raw.get("required_sections")
    if sections is not None and (
            not isinstance(sections, list)
            or not all(isinstance(s, str) and s for s in sections)):
        raise ValueError("venue profile required_sections must be a list of "
                         "non-empty strings or null")
    ack = raw.get("acknowledgments_forbidden_in_blind")
    if ack is not None and not isinstance(ack, bool):
        raise ValueError(
            f"venue profile acknowledgments_forbidden_in_blind must be a "
            f"boolean or null, got {ack!r}")
    return raw


# --- Family A: blind-review residue (§3.1) -----------------------------------

_FAMILY_A_IDS = tuple(
    cid for cid, (fam, _fc, _sc) in sorted(_CHECK_REGISTRY.items())
    if fam == "blind_review_residue")
_SCAN_A_IDS = ("A1", "A2", "A3", "A4", "A5", "A6")  # the variant-scanning subset

# Filename convention for the anonymized (blind-review) variant: a stem token
# match, so `paper_anonymized.docx` / `manuscript-blind.pdf` classify but
# `canonical.md` does not.
_BLIND_STEM_TOKENS = frozenset(
    {"anonymized", "anonymised", "anonymous", "anon", "blind", "blinded"})
# Only manuscript-class artifacts count as "the blind variant" — a
# blind-named ancillary file (blind_survey.csv) is not a blind manuscript
# and must not satisfy A7 under a declared double-blind venue.
_VARIANT_SUFFIXES = (".md", ".tex", ".txt", ".docx", ".pdf")

# A5 self-citation phrasing (§3.1 — heuristic by class). zh-TW list curated
# by the maintainer (#394 follow-up, 2026-06-10). 本文作者先前 is anchored on
# the 本文 prefix because bare 作者先前 matches 該作者先前 (a third party).
_SELF_CITATION_PHRASES = (
    "our previous work", "our earlier study", "our prior work",
    "we previously showed", "we have previously", "in our previous",
    "我們先前的研究", "我們過去的研究", "我們先前曾", "我們已於先前",
    "筆者先前的研究", "本研究團隊先前", "本文作者先前",
)

_ACK_TITLE_RE = re.compile(r"acknowledg(?:e)?ments?|致謝", re.IGNORECASE)


def _is_anonymized_name(rel: str) -> bool:
    if not rel.lower().endswith(_VARIANT_SUFFIXES):
        return False
    tokens = re.split(r"[-_.\s]+", Path(rel).stem.lower())
    return any(t in _BLIND_STEM_TOKENS for t in tokens)


def _a4_strict(profile: Optional[dict[str, Any]]) -> bool:
    """A4 is strict-eligible ONLY when the venue profile explicitly declares
    acknowledgments must be removed from the blind version (§3.1 load-bearing
    — the deterministic signal stays advisory otherwise because the
    de-anonymization judgment is the scholar's). Single definition so EVERY
    A4 emission path (pass/fail/not_checked/not_applicable) agrees."""
    return bool(profile) and (
        profile.get("acknowledgments_forbidden_in_blind") is True)


def _package_files(package_dir: Path) -> list[str]:
    return sorted(
        p.relative_to(package_dir).as_posix()
        for p in package_dir.rglob("*")
        if p.is_file() and p.name not in _SCAN_EXCLUDED_NAMES)


def _blanket_family_a(ids, status: str, reason: str,
                      profile: Optional[dict[str, Any]]
                      ) -> list[dict[str, Any]]:
    """One emitter for every whole-family blanket path (untriggered
    not_applicable / no-variant not_checked), so A4's profile-conditional
    eligibility cannot diverge between them."""
    return [_check(i, status, reason,
                   strict_eligible=_a4_strict(profile) if i == "A4" else None)
            for i in ids]


def run_family_a(package_dir: Path, manuscripts: dict[str, str],
                 profile: Optional[dict[str, Any]]
                 ) -> list[dict[str, Any]]:
    """Family A: blind-review residue scan (§3.1). Trigger is
    presence-or-declaration: an anonymized variant in the package, or a
    declared double-blind venue. Untriggered = not_applicable (the package
    has no blind submission set to protect)."""
    declared_double = bool(profile) and profile.get("blind_review") == "double"
    all_rels = _package_files(package_dir)
    anon_rels = [r for r in all_rels if _is_anonymized_name(r)]

    if not anon_rels and not declared_double:
        return _blanket_family_a(
            _FAMILY_A_IDS, "not_applicable",
            "not triggered: no anonymized variant in the package and no "
            "declared double-blind review (§3.1 presence-or-declaration)",
            profile)

    checks: list[dict[str, Any]] = []
    if declared_double and not anon_rels:
        checks.append(_check(
            "A7", "fail",
            "venue profile declares double-blind review but the package "
            "contains no anonymized manuscript variant "
            f"({'/'.join(_VARIANT_SUFFIXES)} with a name token among "
            f"{'/'.join(sorted(_BLIND_STEM_TOKENS))}) — the blind version "
            "is missing (the most basic residue of all, §3.1)"))
        checks.extend(_blanket_family_a(
            _SCAN_A_IDS, "not_checked", "no anonymized variant to scan",
            profile))
        return checks

    checks.append(_check(
        "A7", "pass",
        f"anonymized variant present: {', '.join(anon_rels)}"))
    checks.extend(_scan_blind_set(
        package_dir, manuscripts, all_rels, anon_rels, profile))
    return checks


def _scan_blind_set(package_dir: Path, manuscripts: dict[str, str],
                    all_rels: list[str], anon_rels: list[str],
                    profile: Optional[dict[str, Any]]
                    ) -> list[dict[str, Any]]:
    """A1-A6 over the blind submission set (the anonymized variants)."""
    checks: list[dict[str, Any]] = []
    pdf_rels = [r for r in anon_rels if r.lower().endswith(".pdf")]
    docx_rels = [r for r in anon_rels if r.lower().endswith(".docx")]
    text_rels = [r for r in anon_rels if r in manuscripts]

    checks.extend(_pdf_metadata_checks(package_dir, pdf_rels))
    checks.extend(_docx_residue_checks(package_dir, docx_rels))
    checks.extend(_text_residue_checks(manuscripts, text_rels, profile))
    checks.append(_filename_leakage_check(package_dir, all_rels, anon_rels))
    return checks


def _residue_verdict(check_id: str, findings: "list[tuple[str, str]]",
                     unreadable: list[str], what: str) -> dict[str, Any]:
    """fail on any (rel, message) finding; otherwise not_checked if any
    artifact was unreadable (incompleteness is never folded into pass, §1.4);
    else pass."""
    if findings:
        listed = "; ".join(f"{rel}: {msg}"
                           for rel, msg in findings[:_LOCATION_CAP])
        return _check(check_id, "fail",
                      f"{what} in the blind submission set: {listed}",
                      location=findings[0][0])
    if unreadable:
        return _check(check_id, "not_checked",
                      f"unreadable artifact(s), {what} could not be scanned: "
                      f"{', '.join(unreadable[:_LOCATION_CAP])}")
    return _check(check_id, "pass", f"no {what} in the blind submission set")


def _pdf_metadata_checks(package_dir: Path,
                         pdf_rels: list[str]) -> list[dict[str, Any]]:
    """A1: PDF info dict /Author + XMP dc:creator non-empty (§3.1)."""
    if not pdf_rels:
        return [_check("A1", "not_applicable",
                       "no PDF in the blind submission set")]
    if pypdf is None:
        return [_check("A1", "not_checked",
                       "parser unavailable: pypdf is not installed (pip "
                       "install pypdf) — PDF metadata cannot be scanned")]
    findings: "list[tuple[str, str]]" = []
    unreadable: list[str] = []
    for rel in pdf_rels:
        try:
            reader = pypdf.PdfReader(str(package_dir / rel))
            author = _pdf_info_author(reader)
            creators: list[str] = []
            try:
                xmp = reader.xmp_metadata
                creators = [c for c in (xmp.dc_creator or []) if str(c).strip()
                            ] if xmp else []
            except Exception:
                # A malformed XMP stream means HALF of A1's signal could not
                # be read — incompleteness, not a silent pass (§1.4). The
                # info-dict half still contributes findings if present.
                unreadable.append(f"{rel} (XMP stream)")
        except Exception:
            unreadable.append(rel)
            continue
        if author:
            findings.append((rel, f"/Author={author!r}"))
        if creators:
            findings.append((rel, f"XMP dc:creator={creators!r}"))
    return [_residue_verdict("A1", findings, unreadable,
                             "PDF metadata author(s)")]


def _pdf_info_author(reader) -> str:
    """The PDF info-dict /Author — the one definition A1 and the A6 token
    harvest share."""
    meta = reader.metadata
    return str(meta.get("/Author") or "").strip() if meta else ""


def _read_zip_part(z: "zipfile.ZipFile", name: str) -> bytes:
    """Bounded read of one zip part (the zip-bomb guard): the declared
    uncompressed size must stay under _MAX_XML_PART_BYTES."""
    if z.getinfo(name).file_size > _MAX_XML_PART_BYTES:
        raise ValueError(f"zip part {name} over the size limit")
    return z.read(name)


def _open_docx_guarded(path: Path) -> "zipfile.ZipFile":
    """Open a .docx with the zip-bomb entry-count guard applied — the one
    opening path for every DOCX reader (A2/A3 and the A6 token harvest), so
    the guards cannot drift apart."""
    z = zipfile.ZipFile(path)
    if len(z.namelist()) > _MAX_ZIP_ENTRIES:
        z.close()
        raise ValueError("zip entry count over limit")
    return z


def _docx_core_author_fields(z: "zipfile.ZipFile") -> "list[tuple[str, str]]":
    """[(label, value)] for the non-empty author fields of docProps/core.xml
    — the one extraction A2 and the A6 token harvest share."""
    if "docProps/core.xml" not in set(z.namelist()):
        return []
    root = _xml_fromstring(_read_zip_part(z, "docProps/core.xml"))
    fields = []
    for tag, label in ((_NS_DC + "creator", "creator"),
                       (_NS_CP + "lastModifiedBy", "lastModifiedBy")):
        el = root.find(tag)
        if el is not None and (el.text or "").strip():
            fields.append((label, el.text.strip()))
    return fields


# OOXML namespaces for the raw-structure DOCX scan. Read with stdlib
# zipfile+ElementTree rather than python-docx: the parts we need
# (docProps/core.xml, word/*.xml author attributes) are plain XML, and a
# stdlib reader means the DOCX residue class has NO missing-parser
# NOT-CHECKED hole at all (§1.3/§1.4; recorded as a spec §9 slice-3
# refinement — pypdf remains the only new dependency).
_NS_DC = "{http://purl.org/dc/elements/1.1/}"
_NS_CP = ("{http://schemas.openxmlformats.org/package/2006/"
          "metadata/core-properties}")
_NS_W = ("{http://schemas.openxmlformats.org/wordprocessingml/2006/main}")


def _docx_residue_checks(package_dir: Path,
                         docx_rels: list[str]) -> list[dict[str, Any]]:
    """A2: docProps/core.xml creator/lastModifiedBy non-empty. A3: w:ins /
    w:del / w:comment author attributes in document parts (§3.1)."""
    if not docx_rels:
        return [_check("A2", "not_applicable",
                       "no DOCX in the blind submission set"),
                _check("A3", "not_applicable",
                       "no DOCX in the blind submission set")]
    meta_findings: "list[tuple[str, str]]" = []
    rev_findings: "list[tuple[str, str]]" = []
    unreadable: list[str] = []
    for rel in docx_rels:
        try:
            with _open_docx_guarded(package_dir / rel) as z:
                for label, value in _docx_core_author_fields(z):
                    meta_findings.append((rel, f"{label}={value!r}"))
                for part in sorted(n for n in z.namelist()
                                   if n.startswith("word/")
                                   and n.endswith(".xml")):
                    root = _xml_fromstring(_read_zip_part(z, part))
                    for el in root.iter():
                        if el.tag in (_NS_W + "ins", _NS_W + "del",
                                      _NS_W + "comment"):
                            author = (el.get(_NS_W + "author") or "").strip()
                            if author:
                                kind = el.tag.split("}", 1)[1]
                                rev_findings.append(
                                    (rel, f"w:{kind} author={author!r}"))
        except _XML_READ_ERRORS:
            unreadable.append(rel)
    return [
        _residue_verdict("A2", meta_findings, unreadable,
                         "DOCX metadata author(s)"),
        _residue_verdict("A3", rev_findings, unreadable,
                         "DOCX revision/comment author(s)"),
    ]


def _text_residue_checks(manuscripts: dict[str, str], text_rels: list[str],
                         profile: Optional[dict[str, Any]]
                         ) -> list[dict[str, Any]]:
    """A4 (acknowledgments section) + A5 (self-citation phrasing) over the
    text-form anonymized variants."""
    checks: list[dict[str, Any]] = []
    a4_strict = _a4_strict(profile)
    if not text_rels:
        # The blind variant exists but only in a form we cannot read headings
        # from — the scan SHOULD run and cannot: not_checked honesty (§1.4),
        # never a not_applicable masquerade.
        checks.append(_check(
            "A4", "not_checked",
            "acknowledgments scan requires a text-form (md/tex/txt) "
            "anonymized variant; DOCX/PDF heading extraction is not supported",
            strict_eligible=a4_strict))
        checks.append(_check("A5", "not_checked",
                             "no extractable text in the blind submission set"))
        return checks

    ack_hits = []
    for rel in text_rels:
        for title in _headings(rel, manuscripts[rel]):
            if _ACK_TITLE_RE.search(title):
                ack_hits.append((rel, title))
                break
    if ack_hits:
        rel, title = ack_hits[0]
        checks.append(_check(
            "A4", "fail",
            f"acknowledgments section present in the anonymized variant "
            f"(heading {title!r}) — whether it de-anonymizes is the scholar's "
            f"judgment (§3.1); flagged, never auto-removed"
            + (" [venue declares acknowledgments forbidden in the blind "
               "version]" if a4_strict else ""),
            location=rel, strict_eligible=a4_strict))
    else:
        checks.append(_check(
            "A4", "pass",
            "no acknowledgments section in the anonymized variant",
            strict_eligible=a4_strict))

    phrase_hits = []
    for rel in text_rels:
        lowered = manuscripts[rel].lower()
        for phrase in _SELF_CITATION_PHRASES:
            if phrase.lower() in lowered:
                phrase_hits.append((rel, phrase))
    if phrase_hits:
        rel, phrase = phrase_hits[0]
        listed = ", ".join(sorted({p for _r, p in phrase_hits})[:_LOCATION_CAP])
        checks.append(_check(
            "A5", "fail",
            f"self-citation phrasing in the anonymized variant: {listed} — "
            f"legitimate prose can false-positive (heuristic, advisory-only)",
            signal_class="heuristic", location=rel))
    else:
        checks.append(_check(
            "A5", "pass",
            "no self-citation phrasing detected in the anonymized variant",
            signal_class="heuristic"))
    return checks


def _author_metadata_strings(package_dir: Path,
                             rels: list[str]) -> list[str]:
    """Author strings from PDF /Author + DOCX core.xml creator/lastModifiedBy
    of the given artifacts — the SAME extraction (and zip guards) as A1/A2,
    consumed best-effort (A6 is heuristic by class, so unreadable artifacts
    are simply skipped here)."""
    authors: list[str] = []
    for rel in rels:
        low = rel.lower()
        try:
            if low.endswith(".docx"):
                with _open_docx_guarded(package_dir / rel) as z:
                    authors.extend(
                        value for _label, value in _docx_core_author_fields(z))
            elif low.endswith(".pdf") and pypdf is not None:
                author = _pdf_info_author(
                    pypdf.PdfReader(str(package_dir / rel)))
                if author:
                    authors.append(author)
        except Exception:
            continue
    return authors


def _filename_leakage_check(package_dir: Path, all_rels: list[str],
                            anon_rels: list[str]) -> dict[str, Any]:
    """A6 (§3.1): author-name tokens from the NON-anonymized variant's
    metadata appearing in package filenames. Heuristic by class (coincidental
    name tokens false-positive). The metadata-source originals themselves are
    not scanned — their identified filenames are expected."""
    anon = set(anon_rels)
    original_rels = [r for r in all_rels
                     if r not in anon
                     and r.lower().endswith((".docx", ".pdf"))]
    authors = _author_metadata_strings(package_dir, original_rels)
    if not authors:
        return _check(
            "A6", "not_checked",
            "no author metadata available on the non-anonymized artifacts to "
            "derive name tokens from")
    # NOTE: not `\w` — underscore is a word char, and `smith_appendix` must
    # split into tokens. Token-to-token comparison under one delimiter model:
    # `smith` flags `smith_appendix.csv` but never `blacksmith_notes.md`.
    def name_tokens(s: str) -> set:
        return {t for t in re.split(r"[^a-z0-9]+", s.lower()) if t}

    tokens = {t for a in authors for t in name_tokens(a) if len(t) >= 3}
    originals = set(original_rels)
    scanned = [r for r in all_rels if r not in originals]
    hits = sorted(
        r for r in scanned if tokens & name_tokens(Path(r).name))
    if hits:
        return _check(
            "A6", "fail",
            f"author-name token(s) in package filename(s): "
            f"{', '.join(hits[:_LOCATION_CAP])} (tokens from "
            f"{', '.join(original_rels[:_LOCATION_CAP])} metadata) — "
            f"coincidental tokens can false-positive (heuristic)",
            location=hits[0])
    return _check(
        "A6", "pass",
        "no author-name tokens from the non-anonymized metadata appear in "
        "package filenames")


def run_checks(package_dir: Path,
               passport: Optional[dict[str, Any]] = None,
               join_map: Optional[dict[str, str]] = None,
               venue_profile: Optional[dict[str, Any]] = None
               ) -> tuple[list[dict[str, Any]], str]:
    """Collect the package texts once and run every check family.
    Returns (checks sorted by id, extraction_path)."""
    manuscripts, bibs = _collect_package_texts(package_dir)
    bib_keys = parse_bib_keys(bibs)
    reference_keys, reference_label = _reference_list(bib_keys, passport)
    checks_c, extraction_path = run_family_c(
        manuscripts, bibs, bib_keys, reference_keys, reference_label,
        passport=passport, join_map=join_map)
    checks_b = run_family_b(
        manuscripts, reference_keys, reference_label, venue_profile)
    checks_a = run_family_a(package_dir, manuscripts, venue_profile)
    return (sorted(checks_a + checks_b + checks_c, key=lambda c: c["id"]),
            extraction_path)


def _report_relpath(package_dir: Path,
                    report_path: Optional[Path]) -> Optional[str]:
    """Package-relative posix path of the report file, or None when the
    report lives outside the package (nothing extra to exclude from the
    fingerprint). Single home for the resolve-relative logic so the
    stamping side (build_report) and the freshness side (check_freshness)
    can never drift apart on what they exclude."""
    if report_path is None:
        return None
    try:
        return report_path.resolve().relative_to(
            package_dir.resolve()).as_posix()
    except ValueError:
        return None


def build_report(package_dir: Path, checks: list[dict[str, Any]],
                 extraction_path: str,
                 report_path: Optional[Path] = None,
                 policy_slug: Optional[str] = None,
                 inputs_fingerprint: Optional[str] = None) -> dict[str, Any]:
    emitted = {c["id"] for c in checks}
    if emitted != set(_CHECK_REGISTRY):
        # Roster guard (§1.4/#349): a runner that silently omits a registered
        # check would read as "covered"; fail loud instead.
        raise ValueError(
            f"check roster mismatch: emitted {sorted(emitted)}, "
            f"registered {sorted(_CHECK_REGISTRY)}")
    report_relpath = _report_relpath(package_dir, report_path)
    return {
        "header": {
            "extraction_path": extraction_path,
            "not_checked_count": sum(
                1 for c in checks if c["status"] == "not_checked"),
            "package_fingerprint": compute_package_fingerprint(
                package_dir, report_relpath),
            # Gate-2 P1: external inputs (venue profile / passport / join
            # map) shape Family B/C verdicts; the freshness guard compares
            # this against the reusing invocation's inputs.
            "inputs_fingerprint": (inputs_fingerprint
                                   or compute_inputs_fingerprint(
                                       None, None, None)),
            # §5.2/§5.3: the value handed down by the policy evaluator via
            # --policy; None = standalone unevaluated run (the argparse
            # default is None, never "advisory" — a null-stamped report can
            # never satisfy pipeline freshness).
            "policy_slug": policy_slug,
        },
        "checks": checks,
    }


def render_human(report: dict[str, Any]) -> str:
    h = report["header"]
    lines = [
        "submission package verification "
        f"(extraction: {h['extraction_path']}, "
        f"not-checked: {h['not_checked_count']}, "
        f"fingerprint: {h['package_fingerprint'][:12]}…)",
    ]
    for c in report["checks"]:
        status = c["status"].upper().replace("_", "-")
        loc = f" @ {c['location']}" if c["location"] else ""
        lines.append(
            f"  [{status}] {c['id']} ({c['family']}, {c['signal_class']})"
            f"{loc}: {c['detail']}")
    return "\n".join(lines)


def exit_code_for(report: dict[str, Any]) -> int:
    statuses = {c["status"] for c in report["checks"]}
    if "fail" in statuses:
        return 1
    if "not_checked" in statuses:
        return 3  # "passed what was checkable" (§8) — distinct from a full pass
    return 0


def evaluate_policy(report: dict[str, Any],
                    policy: Optional[str]) -> tuple[Optional[str], int]:
    """Slice-4 policy evaluation (§5.2/§5.3, applied with an
    already-resolved policy value — the orchestrator selects the policy,
    this is its deterministic tooling). The advisory/strict divergence
    lives HERE, not at the call site: any policy other than "strict"
    (advisory or None/standalone) is byte-equivalent slice-3 behavior.

    Returns (terminal_token_line | None, exit_code). Terminal signals are
    the STDOUT TOKENS, never raw exit codes: exit 1 also covers nonterminal
    heuristic fails (no token), so automation MUST key on the token. The
    evaluator keys on STATUS (fail / not_checked) gated by strict_eligible;
    not_applicable is neither, so an untriggered family can never compose
    into a block or an incompleteness verdict (the slice-3 schema pin)."""
    if policy != "strict":
        return None, exit_code_for(report)
    strict_fails = sorted(
        c["id"] for c in report["checks"]
        if c["strict_eligible"] and c["status"] == "fail")
    if strict_fails:
        return (
            "TERMINAL-BLOCK policy=submission_package "
            f"strict_eligible_fails={','.join(strict_fails)}",
            1,
        )
    incomplete = sorted(
        c["id"] for c in report["checks"]
        if c["strict_eligible"] and c["status"] == "not_checked")
    if incomplete:
        # Fail-closed (§5.2): a missing parser/profile must not silently
        # waive the one check class the scholar opted into blocking on.
        return (
            "VERIFICATION-INCOMPLETE "
            f"strict_eligible_not_checked={','.join(incomplete)}",
            4,
        )
    return None, exit_code_for(report)


def check_freshness(package_dir: Path, report_path: Path,
                    expected_policy: str,
                    expected_inputs_fingerprint: str) -> tuple[str, int]:
    """Slice-4 freshness guard (§5.2): the orchestrator MUST run this before
    ever reusing a report. Does NOT re-run checks and never writes; it
    recomputes the package fingerprint with the SAME exclusion set used at
    write time (report file + provenance_summary.md) and compares
    fingerprint + inputs fingerprint + policy_slug against what the reusing
    invocation carries. A null-stamped (standalone, unevaluated) report
    never satisfies freshness.

    A FRESH report re-emits its policy verdict (gate-2 review P1): freshness
    alone means "the report is trustworthy", not "the package passed" — a
    fresh strict report that recorded a blocking fail prints its terminal
    token again and exits accordingly, so a verdict can never evaporate
    across a resume/reuse.

    Returns (message, exit_code): exit 5 stale; fresh returns the
    re-evaluated verdict's exit code (0/1/3/4)."""
    if not report_path.is_file():
        return "STALE-REPORT reason=missing_report", 5
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        header = report["header"]
        stamped_slug = header["policy_slug"]
        stamped_fingerprint = header["package_fingerprint"]
    except (OSError, ValueError, KeyError, TypeError):
        return "STALE-REPORT reason=unreadable_report", 5
    if stamped_slug is None:
        return "STALE-REPORT reason=null_policy_slug", 5
    if stamped_slug != expected_policy:
        # !r: the slug comes from the report FILE (untrusted bytes under the
        # freshness threat model) — repr collapses embedded newlines so a
        # forged slug cannot inject a fake second token line into stdout.
        return (
            f"STALE-REPORT reason=policy_mismatch stamped={stamped_slug!r} "
            f"expected={expected_policy}",
            5,
        )
    if header.get("inputs_fingerprint") != expected_inputs_fingerprint:
        # Covers a changed/added/dropped venue profile, passport, or join
        # map, AND a legacy report predating the field (gets None).
        return "STALE-REPORT reason=inputs_mismatch", 5
    current = compute_package_fingerprint(
        package_dir, _report_relpath(package_dir, report_path))
    if current != stamped_fingerprint:
        return "STALE-REPORT reason=fingerprint_mismatch", 5
    try:
        emitted = {c["id"] for c in report["checks"]}
    except (KeyError, TypeError):
        return "STALE-REPORT reason=unreadable_report", 5
    if emitted != set(_CHECK_REGISTRY):
        # Roster guard on REUSE (same rule build_report enforces at write
        # time): the report file is excluded from the package fingerprint,
        # so a hand-edited report (e.g. checks: []) would otherwise read as
        # fresh and re-evaluate to a clean exit — a strict verdict must not
        # evaporate through a thinned-out roster (final-round review).
        return "STALE-REPORT reason=roster_mismatch", 5
    try:
        token, code = evaluate_policy(report, expected_policy)
    except (KeyError, TypeError):
        return "STALE-REPORT reason=unreadable_report", 5
    message = f"report fresh (policy={expected_policy})"
    if token is not None:
        message = f"{message}\n{token}"
    return message, code


def run(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        prog="verify_submission_package",
        description="Deterministic submission-package verifier (#394: Family "
                    "C reference integrity + Family B venue limits).",
        epilog="Exit codes: 0 all-checked no-fail; 1 at least one fail; "
               "2 usage/IO error; 3 no fail but at least one NOT-CHECKED; "
               "4 VERIFICATION-INCOMPLETE (strict only: a strict-eligible "
               "check is NOT-CHECKED — fail-closed); 5 STALE-REPORT "
               "(--check-freshness: fingerprint, inputs, or policy-slug "
               "mismatch). A FRESH report under --check-freshness re-emits "
               "its verdict — token + exit semantics identical to a live "
               "run; 'fresh' alone is never a pass. Terminal signals for "
               "automation are the stdout tokens (TERMINAL-BLOCK / "
               "VERIFICATION-INCOMPLETE / STALE-REPORT), NEVER raw exit "
               "codes — exit 1 also covers nonterminal heuristic fails.")
    parser.add_argument("package_dir", help="Output package directory to verify.")
    parser.add_argument(
        "--passport", default=None,
        help="Material Passport YAML supplying citation_verification_summary[] "
             "(the prose-reference join) and/or literature_corpus[] (the "
             "declared reference list).")
    parser.add_argument(
        "--join-map", default=None,
        help="Explicit scholar-supplied {ref_slug: citation_key} YAML/JSON "
             "mapping (overrides every other join source).")
    parser.add_argument(
        "--venue-profile", default=None,
        help="Scholar-declared venue profile YAML (schema shared/contracts/"
             "submission/venue_profile.schema.json) enabling the Family B "
             "limits checks. Absent: every Family B check reports "
             "NOT-CHECKED(no venue profile) — never guessed from the "
             "journal name.")
    parser.add_argument(
        "--report-out", default=None,
        help=f"Report path (default: <package_dir>/{REPORT_BASENAME}).")
    parser.add_argument(
        "--policy", choices=("advisory", "strict"), default=None,
        help="Already-resolved terminal-policy value handed down by the "
             "policy evaluator (the orchestrator reads terminal_policies "
             "and resolves key absence to advisory; this script never reads "
             "the passport's policy block, §5.3). Stamps header.policy_slug. "
             "Absent: standalone unevaluated run, policy_slug stays null.")
    parser.add_argument(
        "--check-freshness", action="store_true",
        help="Do not run checks; verify the existing report is fresh: its "
             "package_fingerprint still matches the package bytes and its "
             "policy_slug matches --policy (REQUIRED with this flag). "
             "Stale or null-stamped → STALE-REPORT + exit 5 (§5.2: never "
             "reuse a stale report).")
    args = parser.parse_args(argv)

    package_dir = Path(args.package_dir)
    if not package_dir.is_dir():
        print(f"[verify_submission_package ERROR] not a directory: "
              f"{package_dir}", file=sys.stderr)
        return 2

    if args.check_freshness:
        if args.policy is None:
            print("[verify_submission_package ERROR] --check-freshness "
                  "requires --policy: freshness is always relative to an "
                  "expected policy, never free-floating.", file=sys.stderr)
            return 2
        report_path = (Path(args.report_out) if args.report_out
                       else package_dir / REPORT_BASENAME)
        try:
            expected_inputs = compute_inputs_fingerprint(
                args.venue_profile, args.join_map, args.passport)
        except OSError as e:
            print(f"[verify_submission_package ERROR] could not read an "
                  f"input file for the freshness comparison: {e}",
                  file=sys.stderr)
            return 2
        message, code = check_freshness(package_dir, report_path,
                                        args.policy, expected_inputs)
        print(message)
        return code

    passport = None
    if args.passport is not None:
        try:
            passport = _load_yaml(Path(args.passport))
        except (OSError, ValueError, yaml.YAMLError) as e:
            print(f"[verify_submission_package ERROR] could not load passport: "
                  f"{e}", file=sys.stderr)
            return 2

    join_map = None
    if args.join_map is not None:
        try:
            raw = _load_yaml(Path(args.join_map))
        except (OSError, ValueError, yaml.YAMLError) as e:
            print(f"[verify_submission_package ERROR] could not load join map: "
                  f"{e}", file=sys.stderr)
            return 2
        join_map = {str(slug): str(key) for slug, key in raw.items()}

    venue_profile = None
    if args.venue_profile is not None:
        try:
            venue_profile = _validate_venue_profile(
                _load_yaml(Path(args.venue_profile)))
        except (OSError, ValueError, yaml.YAMLError) as e:
            print(f"[verify_submission_package ERROR] could not load venue "
                  f"profile: {e}", file=sys.stderr)
            return 2

    checks, extraction_path = run_checks(
        package_dir, passport=passport, join_map=join_map,
        venue_profile=venue_profile)
    report_path = (Path(args.report_out) if args.report_out
                   else package_dir / REPORT_BASENAME)
    report = build_report(package_dir, checks, extraction_path,
                          report_path=report_path,
                          policy_slug=args.policy,
                          inputs_fingerprint=compute_inputs_fingerprint(
                              args.venue_profile, args.join_map,
                              args.passport))

    try:
        report_path.write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8")
    except OSError as e:
        print(f"[verify_submission_package ERROR] could not write report: {e}",
              file=sys.stderr)
        return 2

    print(render_human(report))
    token, code = evaluate_policy(report, args.policy)
    if token is not None:
        print(token)
    return code


if __name__ == "__main__":
    sys.exit(run())
