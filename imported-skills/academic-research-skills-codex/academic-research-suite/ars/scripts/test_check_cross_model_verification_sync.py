"""Tests for the cross-model grounding-guard doc-sync lint (#346 / #349).

Mutation-style: confirm the lint PASSES the real tree and FAILS on each violation class it
exists to catch, so it is not vacuously green.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
LINT = REPO / "scripts" / "check_cross_model_verification_sync.py"
DOC = REPO / "shared" / "cross_model_verification.md"

# A re-inline of the (pre-#349 naive) Gemini sources jq, used by the re-inline mutation test.
REINLINE_OLD = 'cites="$(jq -r -f "$GUARD/gemini_sources.jq" <<<"$body")"'
REINLINE_NEW = (
    'cites="$(jq -r \'[ .candidates[0].groundingMetadata.groundingSupports[]?'
    '.groundingChunkIndices[]? ]\' <<<"$body")"'
)


def _load_lint():
    spec = importlib.util.spec_from_file_location("xmv_sync_lint", LINT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _assert_lint_fails_on_mutation(tmp_path, monkeypatch, old: str, new: str):
    """Apply a string mutation to the doc and assert the lint rejects it (returns 1)."""
    mod = _load_lint()
    mutated = DOC.read_text(encoding="utf-8").replace(old, new)
    assert mutated != DOC.read_text(encoding="utf-8"), f"mutation {old!r}→{new!r} was a no-op"
    fake = tmp_path / "cross_model_verification.md"
    fake.write_text(mutated, encoding="utf-8")
    monkeypatch.setattr(mod, "DOC", fake)
    assert mod.main() == 1


def test_lint_passes_real_tree():
    assert _load_lint().main() == 0


def test_required_filters_all_exist_on_disk():
    mod = _load_lint()
    for name in mod.REQUIRED_FILTERS:
        assert (mod.GUARD_DIR / name).is_file(), f"canonical filter absent: {name}"


@pytest.mark.parametrize(
    "old,new",
    [
        # drop a canonical-filter reference (rename it so the doc no longer wires the .jq)
        ("gemini_is_grounded.jq", "gemini_RENAMED.jq"),
        # drop each safety branch
        ("NOT_SEARCHED", "OK_FINE"),
        ("CROSS-MODEL-ERROR", "oops"),
    ],
    ids=["filter-ref-dropped", "not-searched-dropped", "cross-model-error-dropped"],
)
def test_lint_fails_on_doc_mutation(tmp_path, monkeypatch, old, new):
    """Each removal of a wired filter reference or a safety branch must fail the lint."""
    _assert_lint_fails_on_mutation(tmp_path, monkeypatch, old, new)


def test_lint_fails_when_guard_reinlined(tmp_path, monkeypatch):
    """Re-inlining the naive Gemini sources jq must be caught — it bypasses the tested .jq.

    Kept separate from the parametrized cases: this is a distinct mechanism (check 4 — an inline
    jq program referencing a grounding token), not a dropped reference/branch.
    """
    _assert_lint_fails_on_mutation(tmp_path, monkeypatch, REINLINE_OLD, REINLINE_NEW)


def test_lint_fails_when_jq_f_only_in_comment(tmp_path, monkeypatch):
    """A commented-out `jq -f` line (filename surviving only in a comment) must NOT satisfy the
    wiring check — the lint scans executable bash lines, not comments/prose."""
    _assert_lint_fails_on_mutation(
        tmp_path,
        monkeypatch,
        REINLINE_OLD,
        '# ' + REINLINE_OLD + '\n  cites="$(jq -r ".candidates[0].x" <<<"$body")"',
    )


def test_lint_fails_when_jq_f_only_in_trailing_comment(tmp_path, monkeypatch):
    """A `jq -f` filename surviving only in a TRAILING comment on a weak inline line must NOT
    satisfy the wiring check — trailing comments are stripped before the check."""
    _assert_lint_fails_on_mutation(
        tmp_path,
        monkeypatch,
        REINLINE_OLD,
        'cites="$(jq -r ".candidates[0].x" <<<"$body")"  # ' + REINLINE_OLD,
    )


def test_lint_fails_on_double_quoted_inline_grounding_jq(tmp_path, monkeypatch):
    """An inline jq program referencing a grounding token must be caught even when double-quoted
    (the re-inline guard scans both quote styles, not just single quotes)."""
    _assert_lint_fails_on_mutation(
        tmp_path,
        monkeypatch,
        REINLINE_OLD,
        'cites="$(jq -r "[.candidates[0].groundingMetadata.groundingChunks[].web.uri]" <<<"$body")"',
    )


# --- #453 narrowed regression checks (Task 5) ------------------------------------------------

def test_lint_fails_if_compat_drops_normalizer_invocation(tmp_path, monkeypatch):
    """(#453) The compatible block must INVOKE normalize_compat_verdict.py (check 8 wiring).
    Mutate the canonical-unit invocation away — re-implementing verdict logic inline instead of
    calling the behavior-tested unit must fail the lint. This single test replaces the three
    removed check-5 tests (drops-NOT_SEARCHED / precedence-rejection-only / block-identifier-lost),
    which all pinned the now-deleted inline `case`/`grep` precedence logic."""
    _assert_lint_fails_on_mutation(
        tmp_path, monkeypatch,
        'printf \'%s\' "$text" | python3 "$GUARD/normalize_compat_verdict.py"',
        'first="$(printf \'%s\' "$text" | grep -oiE \'(NOT_FOUND|MISMATCH)\' | head -1)"',
    )


def test_lint_fails_if_normalizer_only_in_comment(tmp_path, monkeypatch):
    """A commented-out normalizer invocation (with inline logic restored) must NOT satisfy
    check 8 — the pipe + comment-stripping require a real piped invocation."""
    _assert_lint_fails_on_mutation(
        tmp_path, monkeypatch,
        'printf \'%s\' "$text" | python3 "$GUARD/normalize_compat_verdict.py"',
        '# normalize via python3 "$GUARD/normalize_compat_verdict.py"\n    echo "STATUS: $text"',
    )


def test_lint_fails_if_compat_block_identifier_lost_v2(tmp_path, monkeypatch):
    """(#453) Anti-vacuity: if the endpoint identifier that locates the compatible block is
    lost, check 8 cannot scope itself and must fail loud (not silently pass). `openai_compatible`
    still appears in the detection block (`echo "CROSS_MODEL_AVAILABLE=openai_compatible"`), so the
    guard path runs but the block can no longer be located."""
    _assert_lint_fails_on_mutation(
        tmp_path, monkeypatch,
        'endpoint="${ARS_OPENAI_COMPAT_BASE_URL%/}/chat/completions"',
        'endpoint="$(build_endpoint)"',
    )


def test_lint_fails_if_openai_base_url_expansion_reintroduced(tmp_path, monkeypatch):
    """A passive OPENAI_BASE_URL expansion in executable bash must fail (the passive-downgrade
    regression). Reintroduce the PR's endpoint line."""
    _assert_lint_fails_on_mutation(
        tmp_path, monkeypatch,
        'endpoint="${ARS_OPENAI_COMPAT_BASE_URL%/}/chat/completions"',
        'endpoint="${OPENAI_BASE_URL:-https://api.openai.com}/v1/chat/completions"',
    )


def test_lint_fails_if_double_v1_reintroduced(tmp_path, monkeypatch):
    """A literal /v1/v1 in executable bash must fail (the double-v1 endpoint bug)."""
    _assert_lint_fails_on_mutation(
        tmp_path, monkeypatch,
        'endpoint="${ARS_OPENAI_COMPAT_BASE_URL%/}/chat/completions"',
        'endpoint="${ARS_OPENAI_COMPAT_BASE_URL%/}/v1/v1/chat/completions"',
    )


def test_lint_allows_openai_base_url_in_prose(tmp_path, monkeypatch):
    """A PROSE/comment mention of OPENAI_BASE_URL (explaining we don't read it) must NOT
    false-fail — the check targets executable assignment/expansion only."""
    mod = _load_lint()
    text = DOC.read_text(encoding="utf-8")
    injected = text.replace(
        "## API Call Patterns",
        "We deliberately never read `OPENAI_BASE_URL` here.\n\n## API Call Patterns",
        1,
    )
    assert injected != text
    fake = tmp_path / "cross_model_verification.md"
    fake.write_text(injected, encoding="utf-8")
    monkeypatch.setattr(mod, "DOC", fake)
    assert mod.main() == 0


# --- Defensive hardenings against future silent-vacuity (Task 5 follow-up) -------------------

def test_bash_blocks_includes_unterminated_final_block():
    """An unterminated trailing ```bash block must still be scanned (fail-closed parsing).

    Directly exercises `_bash_blocks`: without the EOF flush, a final block with no closing fence
    silently drops — fail-OPEN for the bash-scanning checks. We assert the OPENAI_BASE_URL
    expansion inside the unterminated block is recovered, so a downstream check could see it.
    (A whole-doc main()==1 assertion would be vacuously green here — a minimal synthetic doc fails
    for unrelated reasons like missing filters — so we pin the parse contract, not the exit code.)"""
    mod = _load_lint()
    text = 'intro\n\n```bash\nendpoint="${OPENAI_BASE_URL:-x}/chat/completions"\n'  # no closing fence
    blocks = mod._bash_blocks(text)
    recovered = [ln for b in blocks for ln in b]
    assert any("OPENAI_BASE_URL" in ln for ln in recovered), (
        "unterminated final ```bash block was dropped — its OPENAI_BASE_URL expansion would "
        f"escape the bash-scanning checks (fail-OPEN). Recovered lines: {recovered!r}"
    )
