#!/usr/bin/env python3
"""Tests for verify_submission_package — #394 Slice 1 (CLI skeleton + Family C).

Spec: docs/design/2026-06-10-394-submission-package-verifier-spec.md §3.3 / §5.1
/ §7.3 / §8. Mutation discipline per repo convention: every check has a fixture
that fails it and a test proving the failure fires.
"""
from __future__ import annotations

import json
import shutil
import zipfile
from pathlib import Path

import jsonschema
import pytest
import yaml

from verify_submission_package import run

REPO_ROOT = Path(__file__).resolve().parent.parent
FIXTURES = REPO_ROOT / "scripts" / "fixtures" / "submission_package"
SCHEMA_PATH = (
    REPO_ROOT / "shared" / "contracts" / "submission"
    / "submission_verification_report.schema.json"
)
REPORT_BASENAME = "submission_verification_report.json"


def load_schema():
    return json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))


def run_dir(package_dir, extra_args=()):
    """Run the CLI on a package dir; returns (exit_code, report_dict)."""
    rc = run([str(package_dir), *extra_args])
    report_path = package_dir / REPORT_BASENAME
    report = (
        json.loads(report_path.read_text(encoding="utf-8"))
        if report_path.is_file() else None
    )
    return rc, report


def run_on(fixture_name, tmp_path, extra_args=()):
    """Copy a fixture package into tmp and run the CLI on the copy.

    Returns (exit_code, report_dict, package_dir). The copy keeps the repo
    fixture pristine (the CLI writes its report into the package dir).
    """
    package_dir = tmp_path / fixture_name
    shutil.copytree(FIXTURES / fixture_name, package_dir)
    rc, report = run_dir(package_dir, extra_args)
    return rc, report, package_dir


def checks_by_id(report):
    return {c["id"]: c for c in report["checks"]}


# --- Round 1: clean package, joined marker path -----------------------------

def test_clean_package_family_c_passes(tmp_path):
    # Without a venue profile the Family B checks are NOT-CHECKED (§3.2), so
    # the honest exit code is 3 ("passed what was checkable", §8) — Family C
    # itself is fully green.
    rc, report, _ = run_on("clean", tmp_path)
    assert rc == 3
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "pass"
    assert by_id["C2"]["status"] == "pass"


def test_clean_package_is_deterministic_joined_marker(tmp_path):
    _, report, _ = run_on("clean", tmp_path)
    assert report["header"]["extraction_path"] == "joined_marker"
    by_id = checks_by_id(report)
    for cid in ("C1", "C2"):
        assert by_id[cid]["family"] == "reference_integrity"
        assert by_id[cid]["signal_class"] == "deterministic"
    # strict_eligible is class-level: C1 promotable, C2 (warn-only) never —
    # asserted in test_C2_is_never_strict_eligible.


# --- Slice 2: Family B venue limits ------------------------------------------

def test_no_venue_profile_family_b_not_checked(tmp_path):
    # §3.2: without a venue profile every Family B check is
    # NOT-CHECKED(no venue profile) — never guessed from the journal name
    # (R-L3-2-D mirror). The checks stay visible (deterministic,
    # strict-eligible) so the slice-4 fail-closed path has something to see.
    rc, report, _ = run_on("clean", tmp_path)
    assert rc == 3
    by_id = checks_by_id(report)
    for cid in ("B1", "B2", "B3", "B4", "B5"):
        assert by_id[cid]["status"] == "not_checked"
        assert "no venue profile" in by_id[cid]["detail"]
        assert by_id[cid]["family"] == "venue_limits"
        assert by_id[cid]["signal_class"] == "deterministic"
        assert by_id[cid]["strict_eligible"] is True
    assert report["header"]["not_checked_count"] == 5
    jsonschema.validate(report, load_schema())


def test_clean_report_validates_against_schema(tmp_path):
    _, report, _ = run_on("clean", tmp_path)
    jsonschema.validate(report, load_schema())


def test_policy_slug_is_null_in_standalone_runs(tmp_path):
    # §5.2/§5.3: the script never reads terminal_policies; the slug is stamped
    # by the slice-4 orchestrator hook. A standalone run always emits null.
    _, report, _ = run_on("clean", tmp_path)
    assert report["header"]["policy_slug"] is None


def test_report_written_into_package_dir(tmp_path):
    _, _, package_dir = run_on("clean", tmp_path)
    assert (package_dir / REPORT_BASENAME).is_file()


def test_full_profile_all_family_b_pass(tmp_path):
    # venue_clean satisfies every limit in profiles/full.yaml; with both
    # families green the exit code is a true 0.
    profile = FIXTURES / "profiles" / "full.yaml"
    rc, report, _ = run_on("venue_clean", tmp_path,
                           extra_args=["--venue-profile", str(profile)])
    assert rc == 0
    by_id = checks_by_id(report)
    for cid in ("B1", "B2", "B3", "B4", "B5", "C1", "C2"):
        assert by_id[cid]["status"] == "pass", (cid, by_id[cid]["detail"])
    # §3.2: the word-count method is declared in the report, never implied
    # venue-exact.
    assert "whitespace-split" in by_id["B1"]["detail"]
    assert "body_only" in by_id["B1"]["detail"]
    assert report["header"]["not_checked_count"] == 0
    jsonschema.validate(report, load_schema())


def test_violated_profile_every_family_b_check_fails(tmp_path):
    # Mutation discipline (§8): every Family B check has a fixture that fails
    # it. venue_violations breaks all five limits in profiles/tight.yaml.
    profile = FIXTURES / "profiles" / "tight.yaml"
    rc, report, _ = run_on("venue_violations", tmp_path,
                           extra_args=["--venue-profile", str(profile)])
    assert rc == 1
    by_id = checks_by_id(report)
    for cid in ("B1", "B2", "B3", "B4", "B5"):
        assert by_id[cid]["status"] == "fail", (cid, by_id[cid]["detail"])
        assert by_id[cid]["signal_class"] == "deterministic"
        assert by_id[cid]["strict_eligible"] is True
    assert "Data Availability" in by_id["B4"]["detail"]
    # Family C stays green — the violations are venue limits, not integrity.
    assert by_id["C1"]["status"] == "pass"
    jsonschema.validate(report, load_schema())


def test_partial_profile_runs_what_it_can(tmp_path):
    # §4: a partially-declared profile runs the checks it can and
    # NOT-CHECKEDs the rest, each with the undeclared field named.
    profile = tmp_path / "partial.yaml"
    profile.write_text(
        "word_limit: 200\ndeclared_by: scholar\n", encoding="utf-8")
    rc, report, _ = run_on("venue_clean", tmp_path,
                           extra_args=["--venue-profile", str(profile)])
    assert rc == 3
    by_id = checks_by_id(report)
    assert by_id["B1"]["status"] == "pass"
    for cid, field in (("B2", "abstract_word_limit"),
                       ("B3", "keyword_range"),
                       ("B4", "required_sections"),
                       ("B5", "reference_limit")):
        assert by_id[cid]["status"] == "not_checked"
        assert f"{field} not declared" in by_id[cid]["detail"]


def test_word_count_tolerance_two_percent(tmp_path):
    # §3.2: ±2% tolerance before fail (format-conversion noise). 101 words
    # against a 100 limit passes; 103 fails.
    profile = tmp_path / "profile.yaml"
    profile.write_text(
        "word_limit: 100\ndeclared_by: scholar\n", encoding="utf-8")
    for n_words, expected in ((101, "pass"), (103, "fail")):
        package = tmp_path / f"pkg{n_words}"
        package.mkdir()
        (package / "paper.md").write_text(
            " ".join(["word"] * n_words) + "\n", encoding="utf-8")
        run([str(package), "--venue-profile", str(profile)])
        report = json.loads(
            (package / REPORT_BASENAME).read_text(encoding="utf-8"))
        assert checks_by_id(report)["B1"]["status"] == expected, n_words


def test_invalid_venue_profile_is_usage_error(tmp_path):
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("# x\n", encoding="utf-8")
    cases = (
        "word_limit: 100\n",                                  # no declared_by
        "declared_by: tool\n",                                # wrong provenance
        "declared_by: scholar\nword_count_scope: detexed\n",  # bad enum
        "declared_by: scholar\nkeyword_range: {min: 5, max: 2}\n",  # min>max
        "declared_by: scholar\nword_limit: -3\n",             # bad int
    )
    for body in cases:
        profile = tmp_path / "bad.yaml"
        profile.write_text(body, encoding="utf-8")
        assert run([str(package), "--venue-profile", str(profile)]) == 2, body


def test_missing_abstract_and_keywords_not_checked(tmp_path):
    # Declared limits whose actuals cannot be located are NOT-CHECKED with the
    # reason — never folded into pass (§1.4), never guessed.
    profile = tmp_path / "profile.yaml"
    profile.write_text(
        "abstract_word_limit: 50\nkeyword_range: {min: 1, max: 5}\n"
        "declared_by: scholar\n", encoding="utf-8")
    rc, report, _ = run_on("clean", tmp_path,
                           extra_args=["--venue-profile", str(profile)])
    by_id = checks_by_id(report)
    assert by_id["B2"]["status"] == "not_checked"
    assert "no abstract section" in by_id["B2"]["detail"]
    assert by_id["B3"]["status"] == "not_checked"
    assert "no keywords line" in by_id["B3"]["detail"]


def test_latex_manuscript_word_count_declares_detex(tmp_path):
    # §10 item 4 (adjudicated at slice 2): LaTeX counting = naive detex +
    # whitespace-split, the method is declared in the report, never promised
    # venue-exact.
    profile = tmp_path / "profile.yaml"
    profile.write_text(
        "word_limit: 5\ndeclared_by: scholar\n", encoding="utf-8")
    rc, report, _ = run_on("fallback_latex", tmp_path,
                           extra_args=["--venue-profile", str(profile)])
    by_id = checks_by_id(report)
    assert by_id["B1"]["status"] == "fail"
    assert "naive detex" in by_id["B1"]["detail"]
    assert by_id["B1"]["location"] == "paper.tex"


def test_word_count_scope_all_counts_everything(tmp_path):
    # codex P2: `all` must actually count everything (keywords line included);
    # only body_only / body_plus_references exclude it. 10 body words +
    # "**Keywords:** a, b" (3 tokens) against limit 10: body_only passes,
    # all fails.
    base = " ".join(["word"] * 10) + "\n\n**Keywords:** alpha, beta\n"
    for scope, expected in (("body_only", "pass"), ("all", "fail")):
        package = tmp_path / f"pkg_{scope}"
        package.mkdir()
        (package / "paper.md").write_text(base, encoding="utf-8")
        profile = tmp_path / f"{scope}.yaml"
        profile.write_text(
            f"word_limit: 10\nword_count_scope: {scope}\n"
            "declared_by: scholar\n", encoding="utf-8")
        run([str(package), "--venue-profile", str(profile)])
        report = json.loads(
            (package / REPORT_BASENAME).read_text(encoding="utf-8"))
        assert checks_by_id(report)["B1"]["status"] == expected, scope


def test_profile_validation_matches_schema_strictness(tmp_path):
    # codex P2: the CLI gate must not be looser than
    # venue_profile.schema.json — unknown fields (additionalProperties false)
    # and booleans-as-integers are rejected.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("# x\n", encoding="utf-8")
    cases = (
        "declared_by: scholar\nword_limt: 100\n",     # unknown field (typo)
        "declared_by: scholar\nword_limit: true\n",   # bool is not an int
        "declared_by: scholar\nvenue_name: 42\n",     # venue_name not a string
        "declared_by: scholar\nkeyword_range: {min: -1, max: 2}\n",  # min < 0
    )
    for body in cases:
        profile = tmp_path / "bad.yaml"
        profile.write_text(body, encoding="utf-8")
        assert run([str(package), "--venue-profile", str(profile)]) == 2, body


def test_ambiguous_manuscript_not_checked(tmp_path):
    # codex P2: with several non-canonical candidates the verifier must not
    # silently pick the wordiest (it could be a response letter); it reports
    # NOT-CHECKED(ambiguous manuscript). A canonical name (paper.* /
    # manuscript.* / main.*) resolves the ambiguity.
    profile = tmp_path / "profile.yaml"
    profile.write_text(
        "word_limit: 100\ndeclared_by: scholar\n", encoding="utf-8")
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "chapter_one.md").write_text("alpha " * 20, encoding="utf-8")
    (package / "rejoinder.md").write_text("beta " * 30, encoding="utf-8")
    run([str(package), "--venue-profile", str(profile)])
    report = json.loads(
        (package / REPORT_BASENAME).read_text(encoding="utf-8"))
    b1 = checks_by_id(report)["B1"]
    assert b1["status"] == "not_checked"
    assert "ambiguous manuscript" in b1["detail"]

    (package / "paper.md").write_text("gamma " * 10, encoding="utf-8")
    run([str(package), "--venue-profile", str(profile)])
    report = json.loads(
        (package / REPORT_BASENAME).read_text(encoding="utf-8"))
    b1 = checks_by_id(report)["B1"]
    assert b1["status"] == "pass"
    assert b1["location"] == "paper.md"


def test_abstract_tolerance_and_b5_no_reference_list(tmp_path):
    # codex P3: pin the B2 ±2% tolerance and the B5
    # declared-limit-but-no-reference-list branch.
    profile = tmp_path / "profile.yaml"
    profile.write_text(
        "abstract_word_limit: 100\nreference_limit: 5\n"
        "declared_by: scholar\n", encoding="utf-8")
    for n_words, expected in ((101, "pass"), (103, "fail")):
        package = tmp_path / f"pkg{n_words}"
        package.mkdir()
        (package / "paper.md").write_text(
            "## Abstract\n\n" + " ".join(["word"] * n_words) + "\n",
            encoding="utf-8")
        run([str(package), "--venue-profile", str(profile)])
        report = json.loads(
            (package / REPORT_BASENAME).read_text(encoding="utf-8"))
        by_id = checks_by_id(report)
        assert by_id["B2"]["status"] == expected, n_words
        assert by_id["B5"]["status"] == "not_checked"
        assert "no machine-readable reference list" in by_id["B5"]["detail"]


def test_profile_with_no_manuscript_not_checked(tmp_path):
    profile = tmp_path / "profile.yaml"
    profile.write_text(
        "word_limit: 100\ndeclared_by: scholar\n", encoding="utf-8")
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "figure.png").write_bytes(b"\x89PNG\r\n")
    run([str(package), "--venue-profile", str(profile)])
    report = json.loads(
        (package / REPORT_BASENAME).read_text(encoding="utf-8"))
    b1 = checks_by_id(report)["B1"]
    assert b1["status"] == "not_checked"
    assert "no manuscript found" in b1["detail"]


# --- Slice 3: Family A blind-review residue ----------------------------------

def test_family_a_not_applicable_without_trigger(tmp_path):
    # §3.1: the residue scan runs only when the package contains an anonymized
    # variant or the profile declares double-blind. Untriggered checks are
    # not_applicable — visibly distinct from not_checked (they did not need to
    # run), so a single-blind package is not condemned to exit 3 forever.
    rc, report, _ = run_on("clean", tmp_path)
    by_id = checks_by_id(report)
    for cid in ("A1", "A2", "A3", "A4", "A5", "A6", "A7"):
        assert by_id[cid]["status"] == "not_applicable", cid
        assert "not triggered" in by_id[cid]["detail"]
        assert by_id[cid]["family"] == "blind_review_residue"
    # not_applicable is not incompleteness: it does not count as not_checked.
    assert report["header"]["not_checked_count"] == 5  # the B checks only
    jsonschema.validate(report, load_schema())


def test_declared_double_blind_without_variant_fails_A7(tmp_path):
    # §3.1: a declared-double-blind package with NO anonymized variant is
    # itself a fail — the most basic residue of all, the blind version is
    # missing. A1-A6 have nothing to scan: not_checked.
    profile = tmp_path / "double.yaml"
    profile.write_text(
        "blind_review: double\ndeclared_by: scholar\n", encoding="utf-8")
    rc, report, _ = run_on("clean", tmp_path,
                           extra_args=["--venue-profile", str(profile)])
    assert rc == 1
    by_id = checks_by_id(report)
    assert by_id["A7"]["status"] == "fail"
    assert "anonymized manuscript variant" in by_id["A7"]["detail"]
    assert by_id["A7"]["strict_eligible"] is True
    for cid in ("A1", "A2", "A3", "A4", "A5", "A6"):
        assert by_id[cid]["status"] == "not_checked", cid
        assert "no anonymized variant" in by_id[cid]["detail"]


def test_anonymized_variant_triggers_family_a(tmp_path):
    # Presence of an anonymized variant triggers the scan even without a
    # profile (presence-or-declaration, §3.1). With an .md-only variant the
    # PDF/DOCX metadata checks have no object: not_applicable.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text(
        "Body (Smith, 2024) <!--ref:smith2024-->.\n", encoding="utf-8")
    shutil.copy(FIXTURES / "clean" / "references.bib",
                package / "references.bib")
    (package / "paper_anonymized.md").write_text(
        "# T\n\nBody text without identity.\n", encoding="utf-8")
    rc, report = run_dir(package)
    by_id = checks_by_id(report)
    assert by_id["A7"]["status"] == "pass"
    for cid in ("A1", "A2", "A3"):
        assert by_id[cid]["status"] == "not_applicable", cid
        assert "no PDF" in by_id[cid]["detail"] or "no DOCX" in by_id[cid]["detail"]
    jsonschema.validate(report, load_schema())


_DOCX_CORE_TMPL = (
    '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
    '<cp:coreProperties '
    'xmlns:cp="http://schemas.openxmlformats.org/package/2006/metadata/core-properties" '
    'xmlns:dc="http://purl.org/dc/elements/1.1/">'
    "<dc:creator>{creator}</dc:creator>"
    "<cp:lastModifiedBy>{last_modified_by}</cp:lastModifiedBy>"
    "</cp:coreProperties>")
_DOCX_DOC_TMPL = (
    '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
    '<w:document '
    'xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">'
    "<w:body><w:p><w:r><w:t>Blind body text.</w:t></w:r></w:p>{extra}</w:body>"
    "</w:document>")


def make_docx(path, creator="", last_modified_by="", ins_author=None,
              comment_author=None):
    """Minimal raw-structure .docx (a zip with core.xml + document.xml [+
    comments.xml]) — exactly the parts the residue scan reads (§1.3: the
    deliverable is the raw file, not the rendered view)."""
    extra = ""
    if ins_author:
        extra = (f'<w:ins w:id="1" w:author="{ins_author}">'
                 "<w:r><w:t>inserted</w:t></w:r></w:ins>")
    with zipfile.ZipFile(path, "w") as z:
        z.writestr("docProps/core.xml", _DOCX_CORE_TMPL.format(
            creator=creator, last_modified_by=last_modified_by))
        z.writestr("word/document.xml", _DOCX_DOC_TMPL.format(extra=extra))
        if comment_author:
            z.writestr(
                "word/comments.xml",
                '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                '<w:comments xmlns:w="http://schemas.openxmlformats.org/'
                'wordprocessingml/2006/main">'
                f'<w:comment w:id="0" w:author="{comment_author}">'
                "<w:p><w:r><w:t>note</w:t></w:r></w:p></w:comment>"
                "</w:comments>")


def _blind_package(tmp_path, **docx_kwargs):
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    make_docx(package / "paper_anonymized.docx", **docx_kwargs)
    rc, report = run_dir(package)
    return checks_by_id(report)


def test_docx_metadata_author_residue_fails_A2(tmp_path):
    # A2 (§3.1): docProps/core.xml creator / lastModifiedBy non-empty in the
    # blind variant is a deterministic fact about the file — invisible to any
    # rendered-view scan (§1.3).
    by_id = _blind_package(tmp_path, creator="Jordan Smith")
    assert by_id["A2"]["status"] == "fail"
    assert "Jordan Smith" in by_id["A2"]["detail"]
    assert by_id["A2"]["strict_eligible"] is True
    assert by_id["A3"]["status"] == "pass"


def test_docx_clean_metadata_passes_A2_A3(tmp_path):
    by_id = _blind_package(tmp_path)
    assert by_id["A2"]["status"] == "pass"
    assert by_id["A3"]["status"] == "pass"


def test_docx_tracked_change_author_fails_A3(tmp_path):
    by_id = _blind_package(tmp_path, ins_author="J. Smith")
    assert by_id["A3"]["status"] == "fail"
    assert "J. Smith" in by_id["A3"]["detail"]


def test_docx_comment_author_fails_A3(tmp_path):
    by_id = _blind_package(tmp_path, comment_author="Reviewer Zero")
    assert by_id["A3"]["status"] == "fail"
    assert "Reviewer Zero" in by_id["A3"]["detail"]


def test_corrupt_docx_not_checked(tmp_path):
    # An unreadable artifact is incompleteness, never folded into pass (§1.4).
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    (package / "paper_anonymized.docx").write_bytes(b"not a zip")
    _rc, report = run_dir(package)
    by_id = checks_by_id(report)
    for cid in ("A2", "A3"):
        assert by_id[cid]["status"] == "not_checked"
        assert "unreadable" in by_id[cid]["detail"]


def test_pdf_metadata_author_fails_A1(tmp_path):
    pypdf = pytest.importorskip("pypdf")

    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    writer = pypdf.PdfWriter()
    writer.add_blank_page(width=72, height=72)
    writer.add_metadata({"/Author": "Jordan Smith"})
    with open(package / "paper_blind.pdf", "wb") as f:
        writer.write(f)
    _rc, report = run_dir(package)
    a1 = checks_by_id(report)["A1"]
    assert a1["status"] == "fail"
    assert "Jordan Smith" in a1["detail"]
    assert a1["strict_eligible"] is True


def test_pdf_parser_unavailable_is_not_checked(tmp_path, monkeypatch):
    # §1.4/#349: a missing parser must surface as NOT-CHECKED, never read as
    # covered. (The slice-4 strict mode turns this into
    # VERIFICATION-INCOMPLETE.)
    import verify_submission_package as v

    monkeypatch.setattr(v, "pypdf", None)
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    (package / "paper_blind.pdf").write_bytes(b"%PDF-1.4\n%%EOF\n")
    _rc, report = run_dir(package)
    a1 = checks_by_id(report)["A1"]
    assert a1["status"] == "not_checked"
    assert "pypdf" in a1["detail"]


def test_A4_strict_only_when_profile_forbids_acknowledgments(tmp_path):
    # §3.1 load-bearing: A4's SIGNAL is deterministic but the judgment is the
    # scholar's — strict-eligible ONLY when the venue profile explicitly
    # declares acknowledgments must be removed from the blind version.
    def build(profile_body):
        package = tmp_path / f"pkg{len(profile_body)}"
        package.mkdir()
        (package / "paper.md").write_text("Body.\n", encoding="utf-8")
        (package / "paper_anonymized.md").write_text(
            "# Title\n\n## Acknowledgments\n\nWe thank our colleagues.\n",
            encoding="utf-8")
        profile = tmp_path / f"p{len(profile_body)}.yaml"
        profile.write_text(profile_body, encoding="utf-8")
        run([str(package), "--venue-profile", str(profile)])
        return json.loads(
            (package / REPORT_BASENAME).read_text(encoding="utf-8"))

    base = "blind_review: double\ndeclared_by: scholar\n"
    a4 = checks_by_id(build(base))["A4"]
    assert a4["status"] == "fail"
    assert a4["strict_eligible"] is False

    a4 = checks_by_id(build(
        base + "acknowledgments_forbidden_in_blind: true\n"))["A4"]
    assert a4["status"] == "fail"
    assert a4["strict_eligible"] is True


def test_A6_filename_leakage_from_original_metadata(tmp_path):
    # §3.1 A6: author-name tokens harvested from the NON-anonymized artifact's
    # metadata, matched against package filenames (heuristic — coincidental
    # tokens can false-positive). The metadata-source original itself is not
    # scanned (its identified name is expected).
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    make_docx(package / "paper.docx", creator="Jordan Smith")
    make_docx(package / "paper_anonymized.docx")
    (package / "smith_appendix.csv").write_text("x\n", encoding="utf-8")
    _rc, report = run_dir(package)
    a6 = checks_by_id(report)["A6"]
    assert a6["status"] == "fail"
    assert "smith_appendix.csv" in a6["detail"]
    assert a6["signal_class"] == "heuristic"
    assert a6["strict_eligible"] is False


def test_A6_without_original_metadata_not_checked(tmp_path):
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    (package / "paper_anonymized.md").write_text("Body.\n", encoding="utf-8")
    _rc, report = run_dir(package)
    a6 = checks_by_id(report)["A6"]
    assert a6["status"] == "not_checked"
    assert "no author" in a6["detail"]


def test_A5_zh_tw_self_citation_phrase(tmp_path):
    # §10 item 1: the phrasing list must not be anglophone-only.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    (package / "paper_anonymized.md").write_text(
        "# 匿名稿\n\n如我們先前的研究所示，品保回饋迴圈存在斷點。\n",
        encoding="utf-8")
    _rc, report = run_dir(package)
    a5 = checks_by_id(report)["A5"]
    assert a5["status"] == "fail"
    assert "我們先前的研究" in a5["detail"]


def test_A5_zh_tw_third_person_author_self_reference(tmp_path):
    # zh-TW curation (#394 follow-up): third-person self-reference via
    # 本文作者 — the bare 作者先前 would false-positive on 該作者先前
    # (a cited third party's author), so the phrase is anchored on the
    # 本文 prefix.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    (package / "paper_anonymized.md").write_text(
        "# 匿名稿\n\n本文作者先前已就品保回饋迴圈提出分析架構。\n",
        encoding="utf-8")
    _rc, report = run_dir(package)
    a5 = checks_by_id(report)["A5"]
    assert a5["status"] == "fail"
    assert "本文作者先前" in a5["detail"]


def test_A5_other_authors_prior_work_not_flagged(tmp_path):
    # 該作者先前 refers to a cited third party, not the manuscript's own
    # authors — must stay clean (the reason the phrase list does not carry
    # a bare 作者先前 entry).
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    (package / "paper_anonymized.md").write_text(
        "# 匿名稿\n\n該作者先前的研究指出品保回饋迴圈存在斷點。\n",
        encoding="utf-8")
    _rc, report = run_dir(package)
    a5 = checks_by_id(report)["A5"]
    assert a5["status"] == "pass"


# --- codex slice-3 review round ----------------------------------------------

def test_A4_docx_only_variant_is_not_checked_not_applicable(tmp_path):
    # codex P1: a DOCX-only blind variant means the acknowledgments scan
    # SHOULD run but cannot (no text-form variant to read headings from) —
    # that is not_checked honesty, never not_applicable masquerade.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    make_docx(package / "paper_anonymized.docx")
    _rc, report = run_dir(package)
    a4 = checks_by_id(report)["A4"]
    assert a4["status"] == "not_checked"
    assert "text-form" in a4["detail"]


def test_A7_not_satisfied_by_blind_named_supplement(tmp_path):
    # codex P1: a declared double-blind package whose only blind-named file is
    # an ancillary CSV has NO blind manuscript variant — A7 must still fail.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    (package / "blind_survey.csv").write_text("q,a\n", encoding="utf-8")
    profile = tmp_path / "double.yaml"
    profile.write_text(
        "blind_review: double\ndeclared_by: scholar\n", encoding="utf-8")
    rc = run([str(package), "--venue-profile", str(profile)])
    report = json.loads(
        (package / REPORT_BASENAME).read_text(encoding="utf-8"))
    assert rc == 1
    assert checks_by_id(report)["A7"]["status"] == "fail"


def test_untriggered_A4_is_never_strict_eligible(tmp_path):
    # codex P1: A4's eligibility comes ONLY from the explicit profile
    # declaration — including on the untriggered/not_applicable path.
    _rc, report, _ = run_on("clean", tmp_path)
    assert checks_by_id(report)["A4"]["strict_eligible"] is False


def test_A6_token_match_does_not_flag_substrings(tmp_path):
    # codex P2: token-to-token matching — `Smith` must not flag
    # `blacksmith_notes.md`.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    make_docx(package / "paper.docx", creator="Jordan Smith")
    make_docx(package / "paper_anonymized.docx")
    (package / "blacksmith_notes.md").write_text("x\n", encoding="utf-8")
    _rc, report = run_dir(package)
    a6 = checks_by_id(report)["A6"]
    assert a6["status"] == "pass", a6["detail"]


def test_oversized_docx_part_is_not_checked(tmp_path, monkeypatch):
    # codex P2: unbounded zip reads are a zip-bomb exposure; oversized parts
    # are reported as unreadable incompleteness, never scanned or passed.
    import verify_submission_package as v

    monkeypatch.setattr(v, "_MAX_XML_PART_BYTES", 64)
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("Body.\n", encoding="utf-8")
    make_docx(package / "paper_anonymized.docx",
              creator="x" * 200)  # inflates core.xml past the test cap
    _rc, report = run_dir(package)
    a2 = checks_by_id(report)["A2"]
    assert a2["status"] == "not_checked"
    assert "unreadable" in a2["detail"]


def test_profile_rejects_nonboolean_acknowledgments_forbidden_field(tmp_path):
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("# x\n", encoding="utf-8")
    profile = tmp_path / "p.yaml"
    profile.write_text(
        "declared_by: scholar\nacknowledgments_forbidden_in_blind: maybe\n",
        encoding="utf-8")
    assert run([str(package), "--venue-profile", str(profile)]) == 2


def test_schema_accepts_not_applicable():
    # (Unknown statuses are rejected by test_schema_rejects_unknown_status.)
    ok = _minimal_report(status="not_applicable")
    jsonschema.validate(ok, load_schema())


def test_venue_profile_fixtures_validate_against_schema():
    profile_schema = json.loads(
        (REPO_ROOT / "shared" / "contracts" / "submission"
         / "venue_profile.schema.json").read_text(encoding="utf-8"))
    for name in ("full.yaml", "tight.yaml"):
        profile = yaml.safe_load(
            (FIXTURES / "profiles" / name).read_text(encoding="utf-8"))
        jsonschema.validate(profile, profile_schema)


# --- Round 2: fail / warn / NOT-CHECKED paths + exit codes -------------------

def test_orphan_intext_citation_fails_C1_exit_1(tmp_path):
    rc, report, _ = run_on("orphan_intext", tmp_path)
    assert rc == 1
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "fail"
    assert "ghost2024" in by_id["C1"]["detail"]
    assert by_id["C1"]["location"] == "paper.md"
    # The orphan is deterministic-classed on the joined marker path.
    assert by_id["C1"]["signal_class"] == "deterministic"
    assert by_id["C1"]["strict_eligible"] is True
    jsonschema.validate(report, load_schema())


def test_uncited_reference_entry_warns_C2_exit_0(tmp_path):
    # §3.3: uncited reference entry = warn (some venues allow further-reading
    # entries) — advisory, never a fail exit (3 = Family B not checked).
    rc, report, _ = run_on("uncited_reference", tmp_path)
    assert rc == 3
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "pass"
    assert by_id["C2"]["status"] == "warn"
    assert "chenlee2023" in by_id["C2"]["detail"]


def test_markers_without_join_source_not_checked_exit_3(tmp_path):
    # §3.3 + §8 join test: markers present, passport supplies a corpus (a
    # reference list) but NO citation_verification_summary — never a guessed
    # comparison.
    passport = FIXTURES / "passports" / "corpus_only.yaml"
    rc, report, _ = run_on("marker_no_join", tmp_path,
                           extra_args=["--passport", str(passport)])
    assert rc == 3
    by_id = checks_by_id(report)
    for cid in ("C1", "C2"):
        assert by_id[cid]["status"] == "not_checked"
        assert "missing prose-reference join" in by_id[cid]["detail"]
    assert report["header"]["not_checked_count"] == 7  # 2 C + 5 B (no profile)
    assert report["header"]["extraction_path"] == "none"
    jsonschema.validate(report, load_schema())


def test_join_map_resolves_the_no_join_case(tmp_path):
    # The explicit scholar-supplied join map is a valid join source (§3.3) and
    # joins the prose slug to the corpus citation_key.
    passport = FIXTURES / "passports" / "corpus_only.yaml"
    join = tmp_path / "join.yaml"
    join.write_text("smith-feedback-2024: smith2024\n", encoding="utf-8")
    rc, report, _ = run_on(
        "marker_no_join", tmp_path,
        extra_args=["--passport", str(passport), "--join-map", str(join)])
    assert rc == 3  # Family C green; B not checked (no profile)
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "pass"
    assert by_id["C2"]["status"] == "pass"
    assert report["header"]["extraction_path"] == "joined_marker"


def test_missing_package_dir_is_usage_error(tmp_path):
    assert run([str(tmp_path / "does-not-exist")]) == 2


def test_unparseable_passport_is_usage_error(tmp_path):

    bad = tmp_path / "bad.yaml"
    bad.write_text("just a string\n", encoding="utf-8")
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text("# x\n", encoding="utf-8")
    assert run([str(package), "--passport", str(bad)]) == 2


# --- Round 3: fallback extraction, summary join, fingerprint -----------------

def test_fallback_latex_cite_extraction_is_heuristic_best_effort(tmp_path):
    # §3.3: post-converted sources fall back to \cite{} extraction; the header
    # downgrades to best-effort and the whole path is heuristic-classed
    # (advisory-only) — even a true orphan fail is NOT strict-eligible.
    rc, report, _ = run_on("fallback_latex", tmp_path)
    assert rc == 1
    assert report["header"]["extraction_path"] == "best_effort"
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "fail"
    assert "ghost2024" in by_id["C1"]["detail"]
    assert "smith2024" not in by_id["C1"]["detail"]
    for cid in ("C1", "C2"):
        assert by_id[cid]["signal_class"] == "heuristic"
        assert by_id[cid]["strict_eligible"] is False
    assert by_id["C2"]["status"] == "pass"
    jsonschema.validate(report, load_schema())


def test_fallback_authoryear_extraction_matches_bib_metadata(tmp_path):
    rc, report, _ = run_on("fallback_authoryear", tmp_path)
    assert rc == 1
    assert report["header"]["extraction_path"] == "best_effort"
    by_id = checks_by_id(report)
    # Only the unmatched (Nowhere, 2020) is an orphan; Smith (2024) narrative
    # and (Chen & Lee, 2023) parenthetical both join to bib metadata.
    assert by_id["C1"]["status"] == "fail"
    assert "nowhere" in by_id["C1"]["detail"].lower()
    assert "smith" not in by_id["C1"]["detail"].lower()
    assert "chen" not in by_id["C1"]["detail"].lower()
    # Both bib entries were cited, so C2 passes — and the references section
    # itself was not scanned as in-text prose.
    assert by_id["C2"]["status"] == "pass"
    assert by_id["C1"]["signal_class"] == "heuristic"


def test_summary_join_consumes_real_prose_join(tmp_path):
    # The prose slug (smith-feedback-2024) differs from the citation_key
    # (smith2024): a pass proves the citation_verification_summary join was
    # consumed, not an identity guess (§3.3).
    passport = FIXTURES / "passports" / "summary_join.yaml"
    rc, report, _ = run_on("summary_join", tmp_path,
                           extra_args=["--passport", str(passport)])
    assert rc == 3  # Family C green; B not checked (no profile)
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "pass"
    assert by_id["C2"]["status"] == "pass"
    assert report["header"]["extraction_path"] == "joined_marker"
    for cid in ("C1", "C2"):
        assert by_id[cid]["signal_class"] == "deterministic"


def test_no_machine_readable_reference_list_not_checked(tmp_path):
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text(
        "Smith (2024) said things.\n", encoding="utf-8")
    rc = run([str(package)])
    report = json.loads(
        (package / REPORT_BASENAME).read_text(encoding="utf-8"))
    assert rc == 3
    by_id = checks_by_id(report)
    for cid in ("C1", "C2"):
        assert by_id[cid]["status"] == "not_checked"
        assert "no machine-readable reference list" in by_id[cid]["detail"]


def test_fingerprint_follows_audit_snapshot_convention_excluding_report(tmp_path):
    # §10 open item 3 (adjudicated at slice 1): `<relative-path>:<sha256>`
    # lines, byte-sorted, trailing newline, fingerprint = sha256 of the
    # manifest text; the report file itself is excluded. Pinned here by an
    # independent reimplementation.
    import hashlib

    _, report, package_dir = run_on("clean", tmp_path)
    lines = []
    for p in sorted(package_dir.rglob("*")):
        if not p.is_file() or p.name == REPORT_BASENAME:
            continue
        digest = hashlib.sha256(p.read_bytes()).hexdigest()
        lines.append(f"{p.relative_to(package_dir).as_posix()}:{digest}")
    lines.sort()
    expected = hashlib.sha256(
        ("\n".join(lines) + "\n").encode("utf-8")).hexdigest()
    assert report["header"]["package_fingerprint"] == expected


def test_fingerprint_stable_across_reruns_with_report_present(tmp_path):
    # Second run sees the first run's report inside the package dir; the
    # exclusion keeps the fingerprint stable (freshness guard usable, §5.2).

    _, first, package_dir = run_on("clean", tmp_path)
    run([str(package_dir)])
    second = json.loads(
        (package_dir / REPORT_BASENAME).read_text(encoding="utf-8"))
    assert (second["header"]["package_fingerprint"]
            == first["header"]["package_fingerprint"])


# --- Codex review round: P1 partial-join identity guess + P2s ----------------

def test_partial_summary_join_never_falls_back_to_identity(tmp_path):
    # P1: a marker slug ABSENT from the join source must never be compared via
    # an identity guess — even (especially) when the slug coincidentally equals
    # a citation_key in the reference list (§3.3 "never a guessed comparison").
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text(
        "Joined (Smith, 2024) <!--ref:smith-feedback-2024-->.\n"
        "Unjoined but key-shaped (Smith, 2024) <!--ref:smith2024-->.\n",
        encoding="utf-8")
    passport = FIXTURES / "passports" / "summary_join.yaml"
    rc = run([str(package), "--passport", str(passport)])
    report = json.loads(
        (package / REPORT_BASENAME).read_text(encoding="utf-8"))
    assert rc == 1
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "fail"
    assert "no join entry" in by_id["C1"]["detail"]
    assert "smith2024" in by_id["C1"]["detail"]


def test_C2_is_never_strict_eligible(tmp_path):
    # P2: C2's worst outcome is warn, which is advisory-only and never
    # policy-promotable (§5.3) — so the check itself is not strict-eligible,
    # even on the deterministic path.
    _, report, _ = run_on("clean", tmp_path)
    by_id = checks_by_id(report)
    assert by_id["C1"]["strict_eligible"] is True
    assert by_id["C2"]["strict_eligible"] is False


def test_custom_report_out_inside_package_excluded_from_fingerprint(tmp_path):
    # P2: a --report-out path inside the package must be excluded from the
    # fingerprint like the default basename, or reruns self-reference.

    package = tmp_path / "clean"
    shutil.copytree(FIXTURES / "clean", package)
    out = package / "custom_report.json"
    run([str(package), "--report-out", str(out)])
    first = json.loads(out.read_text(encoding="utf-8"))
    run([str(package), "--report-out", str(out)])
    second = json.loads(out.read_text(encoding="utf-8"))
    assert (first["header"]["package_fingerprint"]
            == second["header"]["package_fingerprint"])


def test_authoryear_fallback_tolerates_page_locators(tmp_path):
    # P3: `Smith (2024, p. 12)` / `(Chen & Lee, 2023, pp. 45–67)` are common
    # locator forms; missing them creates avoidable fallback false orphans.
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "paper.md").write_text(
        "Smith (2024, p. 12) framed it; details follow "
        "(Chen & Lee, 2023, pp. 45–67).\n", encoding="utf-8")
    shutil.copy(FIXTURES / "fallback_authoryear" / "references.bib",
                package / "references.bib")
    rc = run([str(package)])
    report = json.loads(
        (package / REPORT_BASENAME).read_text(encoding="utf-8"))
    by_id = checks_by_id(report)
    assert rc == 3  # Family C green; B not checked (no profile)
    assert by_id["C1"]["status"] == "pass"
    assert by_id["C2"]["status"] == "pass"


def test_schema_rejects_warn_with_strict_eligible():
    # P2: warn is advisory-only and never policy-promotable — tightened
    # structurally like the heuristic exclusion.
    bad = _minimal_report(status="warn", strict_eligible=True)
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, load_schema())
    ok = _minimal_report(status="warn", strict_eligible=False)
    jsonschema.validate(ok, load_schema())


# --- Report schema structural contract --------------------------------------

def _minimal_report(**check_overrides):
    check = {
        "id": "C1",
        "family": "reference_integrity",
        "signal_class": "deterministic",
        "strict_eligible": True,
        "status": "pass",
        "detail": "ok",
        "location": None,
    }
    check.update(check_overrides)
    return {
        "header": {
            "extraction_path": "joined_marker",
            "not_checked_count": 0,
            "package_fingerprint": "0" * 64,
            "inputs_fingerprint": "0" * 64,
            "policy_slug": None,
        },
        "checks": [check],
    }


def test_schema_rejects_heuristic_strict_eligible():
    # §3.1/§6: heuristic checks are advisory-only STRUCTURALLY — the schema
    # itself forbids the promotion, not just the emitter.
    bad = _minimal_report(signal_class="heuristic", strict_eligible=True)
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, load_schema())
    ok = _minimal_report(signal_class="heuristic", strict_eligible=False)
    jsonschema.validate(ok, load_schema())


def test_schema_binds_check_id_prefix_to_family():
    # The id prefix encodes the family (spec §3 tables); the contract binds
    # them so a later-slice emitter cannot ship mismatched pairs.
    bad = _minimal_report(id="C1", family="blind_review_residue")
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, load_schema())
    bad2 = _minimal_report(id="A1", family="reference_integrity")
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad2, load_schema())


def test_schema_rejects_unknown_status():
    bad = _minimal_report(status="skipped")
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, load_schema())


# --- Slice 4: terminality (--policy / --check-freshness, spec §5.2/§5.3/§8) --
#
# Terminal signals are STDOUT TOKENS (TERMINAL-BLOCK / VERIFICATION-INCOMPLETE
# / STALE-REPORT), never raw exit codes — exit 1 also carries nonterminal
# advisory/heuristic fails (gate-1 P1). The evaluator keys on STATUS
# (fail / not_checked), never on the strict_eligible bit alone, so
# not_applicable can never compose into a block (slice-3 schema pin).

def _strict_run(fixture_name, tmp_path, capsys, extra_args=()):
    rc, report, package_dir = run_on(
        fixture_name, tmp_path,
        extra_args=["--policy", "strict", *extra_args])
    out = capsys.readouterr().out
    return rc, report, package_dir, out


def test_strict_eligible_fail_blocks_with_token(tmp_path, capsys):
    # orphan_intext fails C1 on the joined marker path (deterministic class).
    rc, report, _, out = _strict_run("orphan_intext", tmp_path, capsys)
    assert rc == 1
    assert "TERMINAL-BLOCK policy=submission_package" in out
    assert report["header"]["policy_slug"] == "strict"


def test_strict_heuristic_fail_never_promotes(tmp_path, capsys):
    # fallback_latex fails C1 on the FALLBACK path (heuristic class). Under
    # strict the heuristic fail must NEVER appear as a TERMINAL-BLOCK
    # (§3.1/§6, structural exclusion). The run exits 4, not 1: the
    # profileless Family B not_checked outranks the nonterminal fail —
    # itself evidence of the fail-closed precedence (a heuristic fail does
    # not short-circuit the incompleteness verdict the way a strict fail
    # would).
    rc, report, _, out = _strict_run("fallback_latex", tmp_path, capsys)
    by_id = checks_by_id(report)
    assert by_id["C1"]["status"] == "fail"
    assert by_id["C1"]["signal_class"] == "heuristic"
    assert "TERMINAL-BLOCK" not in out
    assert rc == 4  # VERIFICATION-INCOMPLETE from Family B, not the C1 fail
    assert "C1" not in next(
        l for l in out.splitlines() if "VERIFICATION-INCOMPLETE" in l)


def test_evaluate_policy_unit_contract():
    # Unit pin of the evaluator's whole decision table: token + exit per
    # policy×status×strict_eligible combination, including precedence (a
    # strict fail outranks incomplete) and the not_applicable
    # never-composes rule. The advisory/strict divergence lives inside the
    # evaluator (it takes the resolved policy), so non-strict policies are
    # part of the table.
    from verify_submission_package import evaluate_policy

    def report_of(*checks):
        return {"checks": [
            {"id": cid, "strict_eligible": se, "status": status}
            for cid, se, status in checks
        ]}

    # Heuristic (strict_eligible=False) fail alone under strict: exit 1,
    # NO token.
    token, code = evaluate_policy(report_of(("A5", False, "fail"),
                                            ("C2", True, "pass")), "strict")
    assert token is None and code == 1
    # Strict-eligible fail under strict: token + exit 1.
    token, code = evaluate_policy(report_of(("B4", True, "fail")), "strict")
    assert code == 1 and "TERMINAL-BLOCK policy=submission_package" in token
    assert "B4" in token
    # The SAME report under advisory / under no policy: never a token —
    # the divergence is the evaluator's own contract, not a caller guard.
    for policy in ("advisory", None):
        token, code = evaluate_policy(report_of(("B4", True, "fail")), policy)
        assert token is None and code == 1
    # Strict-eligible not_checked under strict: incomplete token + exit 4.
    token, code = evaluate_policy(
        report_of(("B1", True, "not_checked")), "strict")
    assert code == 4 and "VERIFICATION-INCOMPLETE" in token
    # ... and under advisory: plain exit 3, no token.
    token, code = evaluate_policy(
        report_of(("B1", True, "not_checked")), "advisory")
    assert token is None and code == 3
    # Precedence: strict fail wins over incomplete (block now, the rerun
    # after remediation surfaces the rest).
    token, code = evaluate_policy(report_of(("B4", True, "fail"),
                                            ("B1", True, "not_checked")),
                                  "strict")
    assert code == 1 and "TERMINAL-BLOCK" in token
    # not_applicable never composes into anything (slice-3 schema pin),
    # heuristic not_checked doesn't either.
    token, code = evaluate_policy(report_of(("A1", True, "not_applicable"),
                                            ("A5", False, "not_checked"),
                                            ("C2", True, "pass")), "strict")
    assert token is None and code == 3
    # All green under strict: clean 0.
    token, code = evaluate_policy(report_of(("C1", True, "pass")), "strict")
    assert token is None and code == 0


def test_strict_eligible_not_checked_is_verification_incomplete(
        tmp_path, capsys):
    # venue_clean without a profile: Family B is strict-eligible not_checked
    # → fail-closed exit 4 + token (§5.2: a missing input must not silently
    # waive the class the scholar opted into blocking on).
    rc, report, _, out = _strict_run("venue_clean", tmp_path, capsys)
    assert rc == 4
    assert "VERIFICATION-INCOMPLETE" in out
    assert "TERMINAL-BLOCK" not in out
    assert report["header"]["policy_slug"] == "strict"


def test_advisory_same_not_checked_stays_exit_3(tmp_path, capsys):
    # Explicit advisory: byte-identical slice-3 behavior except the stamp.
    rc, report, _, = run_on("venue_clean", tmp_path,
                            extra_args=["--policy", "advisory"])
    out = capsys.readouterr().out
    assert rc == 3
    assert "VERIFICATION-INCOMPLETE" not in out
    assert "TERMINAL-BLOCK" not in out
    assert report["header"]["policy_slug"] == "advisory"


def test_no_policy_flag_stamps_null(tmp_path):
    # Standalone unevaluated run: argparse default is None (never "default
    # advisory" — gate-1 P1), the stamp stays null.
    _, report, _ = run_on("venue_clean", tmp_path)
    assert report["header"]["policy_slug"] is None


def test_strict_not_applicable_never_blocks(tmp_path, capsys):
    # clean has no anonymized variant and no blind_review declaration: Family
    # A is not_applicable (untriggered). Under strict that must NOT read as
    # incomplete or block — the evaluator keys on status, and not_applicable
    # is neither fail nor not_checked. (Family B absent-profile not_checked
    # still yields exit 4 here, proving the discrimination is per-status.)
    rc, report, _, out = _strict_run("clean", tmp_path, capsys)
    by_id = checks_by_id(report)
    assert by_id["A1"]["status"] == "not_applicable"
    assert rc == 4  # from Family B not_checked, NOT from Family A
    assert "VERIFICATION-INCOMPLETE" in out
    token_line = next(l for l in out.splitlines()
                      if "VERIFICATION-INCOMPLETE" in l)
    for aid in (f"A{i}" for i in range(1, 8)):
        assert aid not in token_line


def test_strict_full_profile_clean_package_exits_0(tmp_path, capsys):
    # The strict happy path: everything checked, everything green.
    profile = FIXTURES / "profiles" / "full.yaml"
    rc, report, _, out = _strict_run(
        "venue_clean", tmp_path, capsys,
        extra_args=["--venue-profile", str(profile)])
    assert rc == 0
    assert "TERMINAL-BLOCK" not in out
    assert "VERIFICATION-INCOMPLETE" not in out
    assert report["header"]["policy_slug"] == "strict"


# --- Slice 4: freshness guard (--check-freshness, §5.2) ----------------------

def _fresh_args(policy="advisory"):
    return ["--check-freshness", "--policy", policy]


def test_freshness_mutated_package_is_stale(tmp_path, capsys):
    _, _, package_dir = run_on("venue_clean", tmp_path,
                               extra_args=["--policy", "advisory"])
    manuscript = next(p for p in package_dir.iterdir()
                      if p.suffix == ".md" and p.name != "provenance_summary.md")
    manuscript.write_text(
        manuscript.read_text(encoding="utf-8") + "\nDrifted.\n",
        encoding="utf-8")
    capsys.readouterr()
    rc = run([str(package_dir), *_fresh_args()])
    out = capsys.readouterr().out
    assert rc == 5
    assert "STALE-REPORT" in out


def test_freshness_policy_mismatch_is_stale(tmp_path, capsys):
    # Report stamped advisory, orchestrator now wants strict: stale, rerun.
    _, _, package_dir = run_on("venue_clean", tmp_path,
                               extra_args=["--policy", "advisory"])
    capsys.readouterr()
    rc = run([str(package_dir), *_fresh_args(policy="strict")])
    out = capsys.readouterr().out
    assert rc == 5
    assert "STALE-REPORT" in out


def test_freshness_null_stamped_report_never_fresh(tmp_path, capsys):
    # A standalone (unevaluated, policy_slug=null) report never satisfies
    # pipeline freshness — gate-1 P1 (null must not impersonate advisory).
    # The reason token is pinned: null_policy_slug ("you handed the pipeline
    # a standalone report") is a different remediation from policy_mismatch
    # ("the policy changed since stamping") — without the dedicated branch
    # the null case would collapse into the mismatch reason.
    _, _, package_dir = run_on("venue_clean", tmp_path)  # no --policy
    capsys.readouterr()
    rc = run([str(package_dir), *_fresh_args()])
    out = capsys.readouterr().out
    assert rc == 5
    assert "STALE-REPORT reason=null_policy_slug" in out


def test_freshness_missing_report_is_stale(tmp_path, capsys):
    package_dir = tmp_path / "pkg"
    package_dir.mkdir()
    (package_dir / "paper.md").write_text("Body.\n", encoding="utf-8")
    rc = run([str(package_dir), *_fresh_args()])
    out = capsys.readouterr().out
    assert rc == 5
    assert "STALE-REPORT" in out


def test_freshness_requires_policy(tmp_path, capsys):
    # --check-freshness without --policy is a usage error (exit 2): freshness
    # is always relative to an expected policy, never free-floating.
    _, _, package_dir = run_on("venue_clean", tmp_path,
                               extra_args=["--policy", "advisory"])
    capsys.readouterr()
    rc = run([str(package_dir), "--check-freshness"])
    err = capsys.readouterr().err
    assert rc == 2
    assert "policy" in err.lower()


def test_freshness_does_not_rerun_checks(tmp_path, capsys):
    # Freshness must not rewrite the report: mtime-stable bytes.
    _, _, package_dir = run_on("venue_clean", tmp_path,
                               extra_args=["--policy", "advisory"])
    report_path = package_dir / REPORT_BASENAME
    before = report_path.read_bytes()
    capsys.readouterr()
    run([str(package_dir), *_fresh_args()])
    assert report_path.read_bytes() == before


def test_provenance_summary_outside_fingerprint(tmp_path, capsys):
    # gate-1 P1 self-staleness: provenance_summary.md is the pipeline's own
    # advisory carrier (D4 appends to it AFTER the report is stamped) — it is
    # excluded from the fingerprint, so mutating it does NOT stale the report.
    package_dir = tmp_path / "venue_clean"
    shutil.copytree(FIXTURES / "venue_clean", package_dir)
    (package_dir / "provenance_summary.md").write_text(
        "# Provenance\n", encoding="utf-8")
    rc, _ = run_dir(package_dir, extra_args=["--policy", "advisory"])
    (package_dir / "provenance_summary.md").write_text(
        "# Provenance\n\n## Submission Package Advisories\n\n- B2: ...\n",
        encoding="utf-8")
    capsys.readouterr()
    rc = run([str(package_dir), *_fresh_args()])
    out = capsys.readouterr().out
    # Fresh (no STALE token); the exit code is the re-emitted underlying
    # verdict — 3 here (profileless Family B not_checked), NOT a stale 5.
    assert rc == 3
    assert "STALE-REPORT" not in out
    assert "report fresh" in out


def test_advisory_run_is_byte_equivalent_for_package_files(tmp_path):
    # §11 byte-equivalence: an explicit-advisory run mutates NOTHING in the
    # package except adding the report file.
    package_dir = tmp_path / "venue_clean"
    shutil.copytree(FIXTURES / "venue_clean", package_dir)
    before = {
        p.relative_to(package_dir).as_posix(): p.read_bytes()
        for p in package_dir.rglob("*") if p.is_file()
    }
    profile = FIXTURES / "profiles" / "full.yaml"
    run_dir(package_dir, extra_args=["--policy", "advisory",
                                     "--venue-profile", str(profile)])
    after = {
        p.relative_to(package_dir).as_posix(): p.read_bytes()
        for p in package_dir.rglob("*") if p.is_file()
    }
    assert set(after) - set(before) == {REPORT_BASENAME}
    for rel, content in before.items():
        assert after[rel] == content, f"{rel} mutated by an advisory run"


# --- Slice 4 gate-2 review round: freshness re-emit + external inputs -------

def test_freshness_fresh_strict_report_reemits_terminal_token(
        tmp_path, capsys):
    # Gate-2 P1: freshness alone means "the report is trustworthy", not "the
    # package passed". A fresh strict report that recorded a blocking fail
    # must re-emit its terminal verdict on reuse — otherwise the verdict
    # silently evaporates on resume and the orchestrator (gating on tokens)
    # reads the reuse as a pass.
    _, _, package_dir = run_on("orphan_intext", tmp_path,
                               extra_args=["--policy", "strict"])
    capsys.readouterr()
    rc = run([str(package_dir), "--check-freshness", "--policy", "strict"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "report fresh" in out
    assert "TERMINAL-BLOCK policy=submission_package" in out


def test_freshness_fresh_advisory_report_reemits_underlying_code(
        tmp_path, capsys):
    # Same contract on the advisory side: a fresh advisory report with
    # not_checked rows re-emits exit 3, not a flat 0.
    _, _, package_dir = run_on("venue_clean", tmp_path,
                               extra_args=["--policy", "advisory"])
    capsys.readouterr()
    rc = run([str(package_dir), *_fresh_args()])
    out = capsys.readouterr().out
    assert rc == 3
    assert "report fresh" in out
    assert "STALE-REPORT" not in out


def test_freshness_changed_venue_profile_is_stale(tmp_path, capsys):
    # Gate-2 P1: Family B verdicts depend on the venue profile — a report
    # produced under one profile must never read as fresh under another
    # (a lenient-profile report would otherwise waive a stricter profile's
    # limits without any check ever running against them).
    full = FIXTURES / "profiles" / "full.yaml"
    tight = FIXTURES / "profiles" / "tight.yaml"
    _, _, package_dir = run_on(
        "venue_clean", tmp_path,
        extra_args=["--policy", "advisory", "--venue-profile", str(full)])
    capsys.readouterr()
    rc = run([str(package_dir), "--check-freshness", "--policy", "advisory",
              "--venue-profile", str(tight)])
    out = capsys.readouterr().out
    assert rc == 5
    assert "STALE-REPORT reason=inputs_mismatch" in out


def test_freshness_same_venue_profile_stays_fresh(tmp_path, capsys):
    full = FIXTURES / "profiles" / "full.yaml"
    _, _, package_dir = run_on(
        "venue_clean", tmp_path,
        extra_args=["--policy", "advisory", "--venue-profile", str(full)])
    capsys.readouterr()
    rc = run([str(package_dir), "--check-freshness", "--policy", "advisory",
              "--venue-profile", str(full)])
    out = capsys.readouterr().out
    assert rc == 0
    assert "report fresh" in out


def test_freshness_dropped_input_is_stale(tmp_path, capsys):
    # Running with a profile, then checking freshness WITHOUT one, is an
    # inputs change (declared → absent) and must be stale.
    full = FIXTURES / "profiles" / "full.yaml"
    _, _, package_dir = run_on(
        "venue_clean", tmp_path,
        extra_args=["--policy", "advisory", "--venue-profile", str(full)])
    capsys.readouterr()
    rc = run([str(package_dir), *_fresh_args()])
    out = capsys.readouterr().out
    assert rc == 5
    assert "STALE-REPORT reason=inputs_mismatch" in out


def test_freshness_thinned_roster_is_stale(tmp_path, capsys):
    # Final-round review P2: the report file is excluded from the package
    # fingerprint, so a hand-edited report with checks thinned out (here:
    # emptied) would otherwise read as fresh and re-evaluate to a clean
    # exit — the roster guard build_report enforces at write time must
    # hold on reuse too.
    _, _, package_dir = run_on("orphan_intext", tmp_path,
                               extra_args=["--policy", "strict"])
    report_path = package_dir / REPORT_BASENAME
    doctored = json.loads(report_path.read_text(encoding="utf-8"))
    doctored["checks"] = []
    report_path.write_text(json.dumps(doctored), encoding="utf-8")
    capsys.readouterr()
    rc = run([str(package_dir), "--check-freshness", "--policy", "strict"])
    out = capsys.readouterr().out
    assert rc == 5
    assert "STALE-REPORT reason=roster_mismatch" in out
    assert "report fresh" not in out
