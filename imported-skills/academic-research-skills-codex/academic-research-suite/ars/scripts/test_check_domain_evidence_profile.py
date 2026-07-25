"""Mutation suite for check_domain_evidence_profile.py (#259).

Per the iron law: positive + negative tests for every check. Each negative
fixture mutates ONE artifact so exactly one check (C1-C7) fails, proving the
linter cannot trivially accept-all. Fixtures use cwd-swap (REPO_ROOT = Path.cwd()).
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
LINT = REPO_ROOT / "scripts" / "check_domain_evidence_profile.py"

# The four files the lint reads.
INTAKE = "academic-paper/agents/intake_agent.md"
PROFILES = "academic-paper/references/domain_evidence_profiles.md"
CONSUMER = "academic-paper/agents/literature_strategist_agent.md"
SQH = "deep-research/references/source_quality_hierarchy.md"

# Heading literals the C8/C10 fixtures mutate, kept here (not imported from the
# lint module) deliberately: the suite drives the lint via subprocess, so it
# stays import-free. Names match the lint module's constants
# (INTAKE_NO_HANDOFF_HEADING / DECISION_TREE_HEADING) so a future heading reword
# is easy to keep in sync; if it drifts, the fixture precondition assert in the
# affected test fails loudly in CI rather than silently passing.
INTAKE_NO_HANDOFF_HEADING = "### When No Handoff Materials Are Detected"
DECISION_TREE_HEADING = "### Literature Screening Decision Tree"


def run_lint(cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(LINT)], cwd=str(cwd),
        capture_output=True, text=True,
    )


def test_integration_passes_against_real_repo():
    """The lint passes against the actual repo after Tasks 1-3 land."""
    result = run_lint(REPO_ROOT)
    assert result.returncode == 0, result.stderr


def _clone_repo(tmp_path: Path) -> Path:
    """Copy the four lint-relevant files into a minimal repo tree under tmp_path."""
    dst = tmp_path / "repo"
    for rel in (INTAKE, PROFILES, CONSUMER, SQH):
        target = dst / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(REPO_ROOT / rel, target)
    return dst


def _mutate(repo: Path, rel: str, old: str, new: str) -> None:
    """Replace ALL occurrences of `old` (not just the first).

    A single-occurrence replace silently self-breaks a mutation test when the
    token appears more than once in the file: the lint's `if token not in text`
    check still finds the surviving copy, the lint passes, and the negative
    test's `assert returncode != 0` fails. We replace all, then assert the token
    is actually gone so a future multi-occurrence token can't reintroduce the bug.
    """
    p = repo / rel
    text = p.read_text(encoding="utf-8")
    assert old in text, f"fixture precondition: '{old}' not found in {rel}"
    p.write_text(text.replace(old, new), encoding="utf-8")
    assert old not in p.read_text(encoding="utf-8"), (
        f"fixture postcondition: '{old}' still present in {rel} after replace-all"
    )


def test_clone_passes_clean():
    """Sanity: an unmutated clone passes (so each negative isolates one break)."""
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        repo = _clone_repo(Path(d))
        assert run_lint(repo).returncode == 0


def test_neg_a_drop_ship_enum(tmp_path):
    """(a) make a ship-ready enum value go missing (rename all copies) -> C2's
    closed-set table check fails. `humanities_interpretive` occurs twice in the
    profiles doc (table row + carry-forward fold), so _mutate must replace ALL."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "humanities_interpretive", "humanities_BOGUS")
    r = run_lint(repo)
    assert r.returncode != 0 and "C2" in r.stderr


def test_neg_a2_fifth_effective_row(tmp_path):
    """(a2) add a 5th effective profile row (`clinical`) to the table -> C2's
    closed-set check fails (extra row not in SHIP_ENUM). This is the spec's
    'add a 5th effective enum value' mutation strategy; the bare-presence check
    would have missed it. (closed-set regression coverage.)"""
    repo = _clone_repo(tmp_path)
    p = repo / PROFILES
    text = p.read_text(encoding="utf-8")
    # Insert a 5th data row right after the unknown_user_defined table row.
    marker = "| `unknown_user_defined` |"
    assert marker in text
    idx = text.index(marker)
    line_end = text.index("\n", idx)
    injected = "\n| `clinical` | RCTs | journal | gaps | smuggled-in effective |"
    p.write_text(text[:line_end] + injected + text[line_end:], encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C2" in r.stderr


def test_neg_a3_intake_drop_enum_C1(tmp_path):
    """(a3) drop a ship enum value from INTAKE (not PROFILES) -> C1 fails. test_neg_a
    only mutates PROFILES (proves C2); this one proves C1 actually fires on the
    intake surface. (C1/C4 negative-fixture coverage.)"""
    repo = _clone_repo(tmp_path)
    _mutate(repo, INTAKE, "general_social_science", "general_BOGUS")
    r = run_lint(repo)
    assert r.returncode != 0 and "C1" in r.stderr


def test_neg_c4_drop_advisory_or_246(tmp_path):
    """(c4) remove the advisory-only statement -> C4 fails. C4 previously had no
    negative fixture at all. (C1/C4 negative-fixture coverage.)"""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "Advisory only", "Mandatory grading")
    r = run_lint(repo)
    assert r.returncode != 0 and "C4" in r.stderr


def test_neg_b_disqualifying_rename(tmp_path):
    """(b) rename gaps column back to 'disqualifying' -> C2 fails."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "Critical gaps to surface", "Disqualifying gaps")
    r = run_lint(repo)
    assert r.returncode != 0 and "C2" in r.stderr


def test_neg_c_strip_fallback_case(tmp_path):
    """(c) strip a graceful-fallback case from the consumer -> C3 fails."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, CONSUMER, "[PROFILE-UNRESOLVED]", "REMOVED-TAG")
    r = run_lint(repo)
    assert r.returncode != 0 and "C3" in r.stderr


def test_neg_d_delete_legacy_text(tmp_path):
    """(d) delete the preserved Medicine/Health legacy row -> C5 fails. We mutate
    the distinctive verbatim phrase ('evidence-based-medicine') that C5 now binds
    to the Medicine/Health row, NOT the bare 'Medicine/Health' label (which could
    survive elsewhere). Replace-all removes every copy of the phrase."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, PROFILES, "evidence-based-medicine", "REMOVED")
    r = run_lint(repo)
    assert r.returncode != 0 and "C5" in r.stderr


def test_neg_e_remove_policy_fold(tmp_path):
    """(e) delete ONLY the Policy fold line (not Social Science's identical fold)
    -> C5 fails. This is the real regression a review round flagged: the phrase
    'folded into general_social_science' appears for BOTH Social Science and
    Policy, so a phrase-only check (or replace-all) would miss a Policy-only
    deletion. C5 now binds 'Policy' to the fold on the same line; this fixture
    removes exactly that line and the bound check must fire."""
    repo = _clone_repo(tmp_path)
    p = repo / PROFILES
    lines = p.read_text(encoding="utf-8").splitlines(keepends=True)
    kept = [ln for ln in lines if not ("Policy" in ln and "folded into" in ln)]
    assert len(kept) == len(lines) - 1, "fixture expects exactly one Policy-fold line"
    p.write_text("".join(kept), encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C5" in r.stderr


def test_neg_f_leak_into_deep_research(tmp_path):
    """(f) add a Domain Evidence Profiles section to source_quality_hierarchy.md
    -> C6 R-5 leak guard (heading branch) fails."""
    repo = _clone_repo(tmp_path)
    p = repo / SQH
    p.write_text(p.read_text() + "\n## Domain Evidence Profiles\nleak\n", encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C6" in r.stderr


def test_neg_f2_edit_fsa_table_cell(tmp_path):
    """(f2) edit ONE cell of the Field-Specific Adjustments table (no leaked
    heading) -> C6's SHA-256 pin branch fails. Fixture (f) only trips the leaked-
    heading guard; without this, the hash-pin behavior could regress while C6
    still has a passing negative. Mutate a distinctive cell substring that exists
    in the real table (e.g. the Medicine/Health 'evidence-based medicine' note)."""
    repo = _clone_repo(tmp_path)
    p = repo / SQH
    text = p.read_text(encoding="utf-8")
    # Pick a substring guaranteed to be inside the FSA table; edit it so the
    # block digest changes but no `## Domain Evidence Profiles` heading appears.
    assert "Evidence-based medicine tradition" in text, "fixture expects the EBM note cell"
    p.write_text(text.replace("Evidence-based medicine tradition", "EDITED note"), encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C6" in r.stderr


def test_neg_g_carrier_regression(tmp_path):
    """(g) inside the Step 12 block, store the profile via Material Passport
    -> C7 carrier-regression guard fails."""
    repo = _clone_repo(tmp_path)
    # Insert a forbidden carrier line right after the Step 12 heading.
    p = repo / INTAKE
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "### Step 12: Domain Evidence Profile",
        "### Step 12: Domain Evidence Profile\n\nStore the profile on the Material Passport.",
        1,
    )
    p.write_text(text, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C7" in r.stderr


def test_neg_g2_carrier_regression_with_distant_negation(tmp_path):
    """(g2) C7 false-negative guard: a regression line that ALSO contains a
    distant negation word ("Store on the Material Passport, do not use the PCR")
    must STILL fail C7. A per-line "any negation anywhere" filter would wrongly
    let this through; C7's per-occurrence "negation immediately before the token"
    rule catches it (the 'do not' negates the PCR, not the carrier)."""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "### Domain Evidence Profile Resolution",
        "### Domain Evidence Profile Resolution\n\nStore on the Material Passport, do not use the PCR.",
        1,
    )
    p.write_text(text, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C7" in r.stderr


def test_neg_g3_carrier_regression_not_only(tmp_path):
    """(g3) C7 'not only/not just' guard: "Store not only on the Material Passport
    but also in the PCR" AFFIRMS the carrier (not only X = also X), so it must FAIL
    C7. C7's negation exemption uses a `(?!\\s+only|\\s+just)` lookahead so 'not
    only' is not treated as a negation. This fixture locks that branch — without
    it, a future edit could drop the lookahead while the other C7 fixtures still
    pass."""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    text = p.read_text(encoding="utf-8")
    text = text.replace(
        "### Domain Evidence Profile Resolution",
        "### Domain Evidence Profile Resolution\n\nStore not only on the Material Passport but also in the PCR.",
        1,
    )
    p.write_text(text, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C7" in r.stderr


def test_pos_historical_contrast_does_not_trip_c7(tmp_path):
    """Scope-lock: a Material Passport mention OUTSIDE the heading ranges (e.g.
    historical-contrast prose) must NOT trip C7."""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    # Append contrast prose far from the resolution heading range.
    p.write_text(
        p.read_text() + "\n\n## History\nThe R1-R6 design used the Material Passport and Schema 13.\n",
        encoding="utf-8",
    )
    r = run_lint(repo)
    assert r.returncode == 0, r.stderr


# --- C8: no-handoff flow directive upper bound covers Step 12 (#327 P1) ---------
#
# Bug (#327 P1): intake_agent.md's ONLY no-handoff control-flow directive bounded
# the interview at "Step 1-11", but the Domain Evidence Profile producer is
# Step 12. An agent following the directive literally never runs Step 12, never
# writes the PCR row, and the consumer silently takes the [NO-PROFILE-NEUTRAL]
# fallback — the feature never activates on the most common path. C8 pins the
# directive's upper bound so this cannot silently regress; the runtime fix is in
# intake_agent.md line ~63.

def test_neg_h_step12_bound_regression(tmp_path):
    """(h) revert the no-handoff flow directive to a Step-11 upper bound (drop the
    Step 12 coverage) -> C8 fails. This is the exact #327 P1 regression: the
    directive that bounds the no-handoff interview must reach Step 12, or the
    Domain Evidence Profile producer is orphaned. Mutate within the no-handoff
    block so we exercise C8's scoped detection, not a global token scan."""
    repo = _clone_repo(tmp_path)
    p = repo / INTAKE
    text = p.read_text(encoding="utf-8")
    # Find the no-handoff block and strip every "Step 12" mention inside it,
    # simulating the orphaned-bound regression.
    idx = text.index(INTAKE_NO_HANDOFF_HEADING)
    nxt = text.index("\n## ", idx)  # next H2 (Plan Mode Detection) ends the block
    block = text[idx:nxt]
    assert "then Step 12" in block, "fixture precondition: no-handoff block must execute Step 12"
    mutated = block.replace("then Step 12", "then Step 11")
    p.write_text(text[:idx] + mutated + text[nxt:], encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C8" in r.stderr


def test_neg_h2_step12_mentioned_but_negated(tmp_path):
    """(h2) C8 strength: a directive that MENTIONS the Step 12 token but negates
    its execution ("Do not run Step 12 in this flow") must STILL fail C8. A bare
    token-presence guard would let this orphan the producer; C8 requires the
    affirmative 'then Step 12' directive. (Hardening from codex review.)"""
    repo = _clone_repo(tmp_path)
    p = repo / INTAKE
    text = p.read_text(encoding="utf-8")
    idx = text.index(INTAKE_NO_HANDOFF_HEADING)
    nxt = text.index("\n## ", idx)
    block = text[idx:nxt]
    # Replace the affirmative directive with one that mentions but negates Step 12.
    # Anchored on the period-less core phrase so directive-tail extensions
    # (e.g. #392's ", then Step 13 (...)") don't break the fixture.
    mutated = block.replace(
        "then Step 12 (Domain Evidence Profile) per its own gating in that step",
        "Do not run Step 12 in this flow",
    )
    assert mutated != block, "fixture precondition: affirmative directive must be present to replace"
    p.write_text(text[:idx] + mutated + text[nxt:], encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C8" in r.stderr


def test_pos_step11_outside_nohandoff_block_does_not_trip_c8(tmp_path):
    """Scope-lock: a "Step 1-11" mention OUTSIDE the no-handoff block (e.g. the
    plan-mode "instead of the full 11" prose) must NOT trip C8. C8 only inspects
    the no-handoff directive's own block."""
    repo = _clone_repo(tmp_path)
    p = repo / INTAKE
    # Append unrelated prose mentioning Step 1-11 far from the no-handoff block.
    p.write_text(
        p.read_text() + "\n\n## Misc\nSome other flow uses Step 1-11 only, unrelated.\n",
        encoding="utf-8",
    )
    r = run_lint(repo)
    assert r.returncode == 0, r.stderr


# --- C9: reserved-fallback row gets its own advisory, not malformed (#327 P2#2) -
#
# Bug (#327 P2#2): intake writes a reserved request as the display form
# `unknown_user_defined (requested: <reserved>)`. The consumer's case (c) (value
# not in the 4 enum) then swept that valid reserved fallback into
# [PROFILE-UNRESOLVED] — the "malformed/hallucinated row" signal. C9 pins that
# the consumer resolution block (1) carries a distinct reserved-fallback advisory
# tag and (2) actually parses the `(requested: …)` parenthetical, so a future
# edit can't collapse the reserved-fallback path back into the malformed signal.


def test_neg_i_reserved_fallback_tag_removed(tmp_path):
    """(i) drop the reserved-fallback advisory tag from the consumer -> C9 fails.
    Without a distinct tag the reserved-fallback path collapses back into the
    [PROFILE-UNRESOLVED] malformed signal (the #327 P2#2 regression)."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, CONSUMER, "[PROFILE-RESERVED-FALLBACK]", "[PROFILE-UNRESOLVED]")
    r = run_lint(repo)
    assert r.returncode != 0 and "C9" in r.stderr


def test_neg_i2_reserved_parse_removed(tmp_path):
    """(i2) remove the `(requested:` display form from the consumer block ->
    C9 fails. The distinct tag is useless if the block never carries the
    `(requested: <reserved>)` form the agent must route on."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, CONSUMER, "(requested:", "(legacy-noparse:")
    r = run_lint(repo)
    assert r.returncode != 0 and "C9" in r.stderr


def test_neg_i3_form_present_but_no_parse_instruction(tmp_path):
    """(i3) C9 strength: keep the `(requested: …)` display form but strip the
    explicit parse INSTRUCTION -> C9 must still fail. A block can show the form
    as an example while losing the "parse the parenthetical" directive, leaving
    the agent on exact-string equality so the reserved fallback routes to (c).
    (Hardening from codex review.)"""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    text = p.read_text(encoding="utf-8")
    # Remove the two parse/parsing instruction phrases inside the resolution
    # block (verified by grep to be the block's only parse-instruction wording)
    # while leaving the `(requested: …)` display form intact.
    assert "parse the leading" in text and "Resolve by parsing" in text, (
        "fixture precondition: both parse-instruction phrases must be present"
    )
    mutated = text.replace("parse the leading", "use the leading").replace(
        "Resolve by parsing", "Resolve by reading"
    )
    assert "(requested:" in mutated, "fixture: display form must survive the mutation"
    p.write_text(mutated, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C9" in r.stderr


# --- C10: currency/date gate is profile-aware in the decision tree (#327 P2#3) --
#
# Bug (#327 P2#3): currency_window is in PROFILE_LOOSENABLE and four prose
# passages say the year-range relaxes for humanities_interpretive canonical
# texts, but the time-range NODE in the screening decision tree had no profile
# branch — so a canonical humanities source admitted at the peer-review node was
# RE-EXCLUDED at the time-range node unless it had >100 cites (an INVARIANT 5
# monotonic-admit violation). The prose just below the tree also said the profile
# admits "at the peer-review node only", encoding the bug AND contradicting the
# four other passages. C10 pins, inside the decision-tree block, that (1) the
# currency node consults the profile and (2) the "peer-review node only" fossil
# wording is gone.


def test_neg_j_currency_node_not_profile_aware(tmp_path):
    """(j) strip the currency-node profile branch from the decision tree -> C10
    fails. This is the #327 P2#3 regression: without it, a canonical humanities
    source is re-excluded at the time-range node, violating INVARIANT 5. C10 keys
    on the branch-exclusive 'recency is not a quality signal' rationale (occurs
    once, only in that admit branch), so deleting the branch trips it."""
    repo = _clone_repo(tmp_path)
    _mutate(repo, CONSUMER, "recency is not a quality signal", "REMOVED-PHRASE")
    r = run_lint(repo)
    assert r.returncode != 0 and "C10" in r.stderr


def test_neg_j2_peer_review_node_only_fossil(tmp_path):
    """(j2) reintroduce the "peer-review node only" fossil wording -> C10 fails.
    That phrasing both encodes the bug (profile can't touch the currency node) and
    contradicts the four prose passages that say currency relaxes for humanities.
    The fix reworded it to name the PROFILE_LOOSENABLE gates; this fixture proves
    C10 catches a regression back to the narrow wording."""
    repo = _clone_repo(tmp_path)
    p = repo / CONSUMER
    text = p.read_text(encoding="utf-8")
    block_idx = text.index(DECISION_TREE_HEADING)
    # Inject the fossil phrase into the post-tree prose within the tree block.
    nxt = text.index("\n### ", block_idx + len(DECISION_TREE_HEADING))
    injected = text[:nxt] + "\nThe profile is added at the peer-review node only.\n" + text[nxt:]
    p.write_text(injected, encoding="utf-8")
    r = run_lint(repo)
    assert r.returncode != 0 and "C10" in r.stderr
