"""Behavioral tests for the cross-model grounding guards (#346 / #349).

The grounding guards in `shared/cross_model_verification.md` are the load-bearing safety
boundary of the cross-model citation verifier: they must emit NOT_SEARCHED (and discard the
verdict) whenever the API response carries no grounding evidence, so a from-memory guess can
never be laundered into VERIFIED. The contract-bearing jq lives in canonical files under
`scripts/cross_model_verification/` (referenced by the doc via `jq -f`); these tests run those
files against synthetic fixtures so a future edit, or a provider response-shape change, that
stops the guard failing closed is caught by CI instead of silently degrading.

The dangerous failure class is "jq still exists, but no longer fails closed" — string presence
cannot catch it, so this is a behavioral test (run the jq, assert the verdict), paired with a
mutation test (an accept-all jq substitution MUST fail these fixtures, proving they are not
vacuously green).

jq is REQUIRED: if it is absent the tests fail clearly rather than skip (a skipped safety test
reads as "covered" when it is not).
"""
from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

GUARD_DIR = Path(__file__).resolve().parent / "cross_model_verification"

OPENAI_GUARD = GUARD_DIR / "openai_has_completed_web_search.jq"
OPENAI_TEXT = GUARD_DIR / "openai_text.jq"
OPENAI_SOURCES = GUARD_DIR / "openai_sources.jq"
GEMINI_GUARD = GUARD_DIR / "gemini_is_grounded.jq"
GEMINI_SOURCES = GUARD_DIR / "gemini_sources.jq"

ALL_FILTERS = [OPENAI_GUARD, OPENAI_TEXT, OPENAI_SOURCES, GEMINI_GUARD, GEMINI_SOURCES]


# Resolved once at import — repeated shutil.which() across every assertion is wasted I/O, and a
# single lookup is enough to fail loud when jq is absent.
_JQ_PATH = shutil.which("jq")


def _require_jq() -> str:
    assert _JQ_PATH is not None, (
        "jq is required to test the cross-model grounding guards but was not found on PATH. "
        "Install jq (it is the runtime the documented bash patterns depend on); do not skip."
    )
    return _JQ_PATH


def _run_jq_raw(filter_path: Path, json_text: str, *, raw: bool = False, exit_test: bool = False):
    """Run `jq [-r] [-e] -f <filter>` over a pre-serialized JSON string. Returns (rc, stdout)."""
    jq = _require_jq()
    args = [jq]
    if exit_test:
        args.append("-e")
    if raw:
        args.append("-r")
    args += ["-f", str(filter_path)]
    proc = subprocess.run(args, input=json_text, capture_output=True, text=True)
    return proc.returncode, proc.stdout.strip()


def _run_jq(filter_path: Path, payload: dict, *, raw: bool = False, exit_test: bool = False):
    """Run `jq [-r] [-e] -f <filter>` over a Python payload. Returns (returncode, stdout)."""
    return _run_jq_raw(filter_path, json.dumps(payload), raw=raw, exit_test=exit_test)


def test_jq_version_diagnostic():
    """Print the jq version for CI diagnostics; assert jq is present (no exact-version pin)."""
    jq = _require_jq()
    out = subprocess.run([jq, "--version"], capture_output=True, text=True).stdout.strip()
    print(f"jq under test: {out}")
    assert out.startswith("jq")


def test_all_canonical_filters_exist_and_parse():
    """Each canonical filter exists and compiles+runs cleanly on `null` input (rc == 0).

    Every filter guards its input access (`?`, `// []`, type-checked `select`), so on `null` it
    returns a benign empty/false result with exit 0. Asserting rc == 0 — not merely the absence of
    the string "syntax error" — also catches compile errors that don't use that exact wording
    (e.g. an undefined function), which a stderr-substring check would miss.
    """
    for f in ALL_FILTERS:
        assert f.is_file(), f"missing canonical filter: {f}"
        rc, _ = _run_jq_raw(f, "null")
        assert rc == 0, f"{f.name} did not compile+run cleanly on null input"


# ---------------------------------------------------------------------------
# OpenAI guard
# ---------------------------------------------------------------------------

OPENAI_GROUNDED = {
    "output": [
        {"type": "web_search_call", "status": "completed"},
        {
            "type": "message",
            "content": [
                {
                    "type": "output_text",
                    "text": "VERIFIED",
                    "annotations": [
                        {"type": "url_citation", "url": "https://doi.org/10.1/a"},
                        {"type": "url_citation", "url": "https://example.org/b"},
                    ],
                }
            ],
        },
    ]
}

OPENAI_FROM_MEMORY = {
    "output": [
        {
            "type": "message",
            "content": [{"type": "output_text", "text": "VERIFIED", "annotations": []}],
        }
    ]
}

OPENAI_SEARCH_NO_CITATION = {
    "output": [
        {"type": "web_search_call", "status": "completed"},
        {
            "type": "message",
            "content": [{"type": "output_text", "text": "VERIFIED", "annotations": []}],
        },
    ]
}


def test_openai_grounded_passes_guard():
    rc, _ = _run_jq(OPENAI_GUARD, OPENAI_GROUNDED, exit_test=True)
    assert rc == 0  # a completed web_search_call → grounded


def test_openai_from_memory_fails_guard():
    rc, _ = _run_jq(OPENAI_GUARD, OPENAI_FROM_MEMORY, exit_test=True)
    assert rc != 0  # no web_search_call → NOT_SEARCHED


def test_openai_grounded_extracts_text_and_sources():
    _, text = _run_jq(OPENAI_TEXT, OPENAI_GROUNDED, raw=True)
    assert text == "VERIFIED"
    _, sources = _run_jq(OPENAI_SOURCES, OPENAI_GROUNDED, raw=True)
    assert sources == "https://doi.org/10.1/a, https://example.org/b"


def test_openai_search_without_citation_yields_blank_sources():
    """A completed search but a VERIFIED with no url_citation → blank sources → downgraded."""
    _, sources = _run_jq(OPENAI_SOURCES, OPENAI_SEARCH_NO_CITATION, raw=True)
    assert sources == ""


# ---------------------------------------------------------------------------
# Gemini guard
# ---------------------------------------------------------------------------

GEMINI_GROUNDED = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "webSearchQueries": ["smith 2020 journal"],
                "groundingChunks": [
                    {"web": {"uri": "https://doi.org/10.1/a"}},
                    {"web": {"uri": "https://example.org/b"}},
                    {"web": {"uri": "https://uncited.org/c"}},
                ],
                "groundingSupports": [{"groundingChunkIndices": [0, 1]}],
            },
        }
    ]
}

GEMINI_SEARCH_NO_SUPPORT = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "webSearchQueries": ["smith 2020"],
                "groundingChunks": [{"web": {"uri": "https://doi.org/10.1/a"}}],
                # no groundingSupports → text not tied to any chunk → from-memory
            },
        }
    ]
}

GEMINI_NEGATIVE_INDEX = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "webSearchQueries": ["q"],
                "groundingChunks": [
                    {"web": {"uri": "https://first.org"}},
                    {"web": {"uri": "https://last.org"}},
                ],
                "groundingSupports": [{"groundingChunkIndices": [-1]}],
            },
        }
    ]
}

GEMINI_STRING_INDEX = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "webSearchQueries": ["q"],
                "groundingChunks": [{"web": {"uri": "https://a.org"}}],
                "groundingSupports": [{"groundingChunkIndices": ["0"]}],
            },
        }
    ]
}

GEMINI_OUT_OF_RANGE = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "webSearchQueries": ["q"],
                "groundingChunks": [{"web": {"uri": "https://a.org"}}],
                "groundingSupports": [{"groundingChunkIndices": [5]}],
            },
        }
    ]
}


def test_gemini_grounded_passes_guard():
    rc, _ = _run_jq(GEMINI_GUARD, GEMINI_GROUNDED, exit_test=True)
    assert rc == 0


def test_gemini_search_without_support_fails_guard():
    rc, _ = _run_jq(GEMINI_GUARD, GEMINI_SEARCH_NO_SUPPORT, exit_test=True)
    assert rc != 0  # searched, chunks present, but no groundingSupports → NOT_SEARCHED


# #351: groundingSupports present but linking to NO valid chunk index (empty / negative / string /
# out-of-range / a bare {}). These have a non-empty groundingSupports array but no actual link to a
# retrieved chunk, so the verdict is not grounded — the guard must fail closed (previously it
# false-passed on the non-empty-array check alone, which let an ungrounded NOT_FOUND/MISMATCH be
# trusted, since the blank-source downgrade only rescues VERIFIED).
def _gemini_supports(support_objs, chunks=None):
    return {
        "candidates": [
            {
                "content": {"parts": [{"text": "VERIFIED"}]},
                "groundingMetadata": {
                    "webSearchQueries": ["q"],
                    "groundingChunks": chunks if chunks is not None else [{"web": {"uri": "X"}}],
                    "groundingSupports": support_objs,
                },
            }
        ]
    }


@pytest.mark.parametrize(
    "support_objs",
    [
        [{}],  # no groundingChunkIndices at all
        [{"groundingChunkIndices": []}],  # empty index list
        [{"groundingChunkIndices": [-1]}],  # negative
        [{"groundingChunkIndices": ["0"]}],  # string
        [{"groundingChunkIndices": [5]}],  # out of range (only 1 chunk)
    ],
    ids=["no-indices", "empty-indices", "negative", "string", "out-of-range"],
)
def test_gemini_guard_fails_closed_without_valid_supported_index(support_objs):
    rc, _ = _run_jq(GEMINI_GUARD, _gemini_supports(support_objs), exit_test=True)
    assert rc != 0


# Guard-derives-from-extractor cases (#351 round 2): the guard embeds the SAME extraction as
# gemini_sources.jq, so the safety invariant `guard-pass ⟹ sources non-blank` holds for every
# shape — including a multi-candidate response where candidate 0 is unsupported (the guard must read
# the same candidate[0] the extractor does, not `any` candidate), a fractional index, and a
# non-string uri. Each row is (label, candidate-list, guard-should-pass).
_GUARD_DERIVE_CASES = [
    # candidate 0 unsupported, candidate 1 grounded: guard reads candidate[0] like the extractor,
    # so it must FAIL (a true `any`-candidate guard would pass here then emit candidate 0's blank).
    (
        "multi-candidate-cand0-unsupported",
        [
            {"groundingMetadata": {"webSearchQueries": ["q"], "groundingChunks": [{"web": {"uri": "X"}}], "groundingSupports": [{"groundingChunkIndices": []}]}},
            {"groundingMetadata": {"webSearchQueries": ["q"], "groundingChunks": [{"web": {"uri": "Y"}}], "groundingSupports": [{"groundingChunkIndices": [0]}]}},
        ],
        False,
    ),
    # fractional index: jq does not fractional-index, so the extractor yields nothing → guard fails.
    (
        "fractional-index",
        [{"groundingMetadata": {"webSearchQueries": ["q"], "groundingChunks": [{"web": {"uri": "X"}}], "groundingSupports": [{"groundingChunkIndices": [0.5]}]}}],
        False,
    ),
    # valid index but the indexed chunk's uri is not a string → no extractable source → guard fails.
    (
        "non-string-uri",
        [{"groundingMetadata": {"webSearchQueries": ["q"], "groundingChunks": [{"web": {"uri": 123}}], "groundingSupports": [{"groundingChunkIndices": [0]}]}}],
        False,
    ),
    # a real grounded response: guard passes.
    (
        "legit-grounded",
        [{"groundingMetadata": {"webSearchQueries": ["q"], "groundingChunks": [{"web": {"uri": "A"}}], "groundingSupports": [{"groundingChunkIndices": [0]}]}}],
        True,
    ),
]


@pytest.mark.parametrize(
    "candidates,should_pass",
    [(c, p) for _, c, p in _GUARD_DERIVE_CASES],
    ids=[label for label, _, _ in _GUARD_DERIVE_CASES],
)
def test_gemini_guard_derives_from_extractor(candidates, should_pass):
    """Guard-pass tracks the extractor exactly: it embeds the same candidate[0] extraction and
    passes iff that yields ≥1 source (plus a real search signal)."""
    payload = {"candidates": candidates}
    rc, _ = _run_jq(GEMINI_GUARD, payload, exit_test=True)
    assert (rc == 0) == should_pass


def test_gemini_guard_pass_implies_sources_nonblank():
    """The safety invariant (one-directional): if the guard passes, gemini_sources.jq returns at
    least one source. (The converse is intentionally NOT required — the guard is strictly stronger,
    also demanding a real webSearchQueries signal, so a chunks-but-no-search response fails the
    guard while sources are non-blank.)"""
    for _, candidates, should_pass in _GUARD_DERIVE_CASES:
        payload = {"candidates": candidates}
        rc, _ = _run_jq(GEMINI_GUARD, payload, exit_test=True)
        _, src = _run_jq(GEMINI_SOURCES, payload, raw=True)
        if rc == 0:  # guard passed → sources MUST be non-blank
            assert src != "", f"guard passed but sources blank for {candidates!r}"

    # The guard is strictly stronger: chunks + valid support but NO webSearchQueries → guard fails
    # even though a source is extractable.
    no_search = {"candidates": [{"groundingMetadata": {"groundingChunks": [{"web": {"uri": "X"}}], "groundingSupports": [{"groundingChunkIndices": [0]}]}}]}
    rc_ns, _ = _run_jq(GEMINI_GUARD, no_search, exit_test=True)
    _, src_ns = _run_jq(GEMINI_SOURCES, no_search, raw=True)
    assert rc_ns != 0 and src_ns != ""


def test_gemini_sources_only_from_supported_chunks():
    """Sources come only from chunks cited by groundingSupports — the uncited chunk C is dropped."""
    _, sources = _run_jq(GEMINI_SOURCES, GEMINI_GROUNDED, raw=True)
    assert sources == "https://doi.org/10.1/a, https://example.org/b"
    assert "uncited.org" not in sources


def test_gemini_negative_index_fails_closed():
    """A negative groundingChunkIndex must NOT silently select a chunk from the end (#349 fix).

    Before the fail-closed guard, jq's `$chunks[-1]` returned the LAST chunk's URI, fabricating a
    real-but-wrong source that would defeat the blank-source downgrade.
    """
    rc, sources = _run_jq(GEMINI_SOURCES, GEMINI_NEGATIVE_INDEX, raw=True)
    assert rc == 0  # no crash
    assert sources == ""  # blank → downgraded to NOT_SEARCHED, not "https://last.org"


def test_gemini_string_index_fails_closed():
    """A string groundingChunkIndex must yield blank sources, not a jq crash (#349 fix)."""
    rc, sources = _run_jq(GEMINI_SOURCES, GEMINI_STRING_INDEX, raw=True)
    assert rc == 0  # the select() drops the string before indexing — no "Cannot index" error
    assert sources == ""


def test_gemini_out_of_range_index_fails_closed():
    """An index >= len(groundingChunks) must yield blank sources, not a crash."""
    rc, sources = _run_jq(GEMINI_SOURCES, GEMINI_OUT_OF_RANGE, raw=True)
    assert rc == 0
    assert sources == ""


# Malformed-CONTAINER fixtures: a field arrives as the wrong JSON type (not just a bad index).
# `length` is truthy for non-empty strings/objects, and indexing a string crashes — so these must
# be type-normalized to fail closed, not silently pass the guard or fabricate/crash on sources.

GEMINI_SUPPORTS_NOT_ARRAY = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "webSearchQueries": ["q"],
                "groundingSupports": {"bogus": 1},  # object, not array
            },
        }
    ]
}

GEMINI_QUERIES_NOT_ARRAY = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "webSearchQueries": "q",  # string, not array
                "groundingSupports": [{"groundingChunkIndices": [0]}],
            },
        }
    ]
}

GEMINI_CHUNKS_NOT_ARRAY = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "groundingChunks": "oops",  # string, not array — index 0 would crash
                "groundingSupports": [{"groundingChunkIndices": [0]}],
            },
        }
    ]
}

GEMINI_URI_NOT_STRING = {
    "candidates": [
        {
            "content": {"parts": [{"text": "VERIFIED"}]},
            "groundingMetadata": {
                "groundingChunks": [{"web": {"uri": 123}}],  # number, not a URL string
                "groundingSupports": [{"groundingChunkIndices": [0]}],
            },
        }
    ]
}


def test_gemini_guard_fails_closed_on_non_array_supports():
    """groundingSupports as an object must not pass the guard (length is truthy on objects)."""
    rc, _ = _run_jq(GEMINI_GUARD, GEMINI_SUPPORTS_NOT_ARRAY, exit_test=True)
    assert rc != 0


def test_gemini_guard_fails_closed_on_non_array_queries():
    """webSearchQueries as a string must not pass the guard (length is truthy on strings)."""
    rc, _ = _run_jq(GEMINI_GUARD, GEMINI_QUERIES_NOT_ARRAY, exit_test=True)
    assert rc != 0


def test_gemini_sources_fails_closed_on_non_array_chunks():
    """groundingChunks as a string must yield blank sources, not crash on `$chunks[.]`."""
    rc, sources = _run_jq(GEMINI_SOURCES, GEMINI_CHUNKS_NOT_ARRAY, raw=True)
    assert rc == 0
    assert sources == ""


def test_gemini_sources_fails_closed_on_non_string_uri():
    """A chunk whose uri is a number must not fabricate a SOURCES entry."""
    rc, sources = _run_jq(GEMINI_SOURCES, GEMINI_URI_NOT_STRING, raw=True)
    assert rc == 0
    assert sources == ""


OPENAI_URL_NOT_STRING = {
    "output": [
        {"type": "web_search_call", "status": "completed"},
        {
            "type": "message",
            "content": [
                {
                    "type": "output_text",
                    "text": "VERIFIED",
                    "annotations": [{"type": "url_citation", "url": True}],  # bool, not a URL
                }
            ],
        },
    ]
}

OPENAI_URL_OBJECT = {
    "output": [
        {"type": "web_search_call", "status": "completed"},
        {
            "type": "message",
            "content": [
                {
                    "type": "output_text",
                    "text": "VERIFIED",
                    "annotations": [{"type": "url_citation", "url": {"n": 1}}],  # object → join crash
                }
            ],
        },
    ]
}


def test_openai_sources_fails_closed_on_non_string_url():
    """A url_citation whose url is a bool must not fabricate a SOURCES entry."""
    rc, sources = _run_jq(OPENAI_SOURCES, OPENAI_URL_NOT_STRING, raw=True)
    assert rc == 0
    assert sources == ""


def test_openai_sources_fails_closed_on_object_url():
    """A url_citation whose url is an object must yield blank sources, not crash `join`."""
    rc, sources = _run_jq(OPENAI_SOURCES, OPENAI_URL_OBJECT, raw=True)
    assert rc == 0
    assert sources == ""


# Top-level container fixtures: `candidates` / `output` arriving as an OBJECT instead of an array.
# `.candidates[]?` / `.output[]?` iterate an object's VALUES, so without array-normalization a
# malformed top-level container could pass the guard (false-grounded) and then crash / leak in the
# source extractor (`.candidates[0]` on an object errors; `.output[]?` surfaces a nested url).

GEMINI_CANDIDATES_NOT_ARRAY = {
    "candidates": {  # object, not array
        "0": {
            "groundingMetadata": {
                "webSearchQueries": ["q"],
                "groundingChunks": [{"web": {"uri": "https://leak.org"}}],
                "groundingSupports": [{"groundingChunkIndices": [0]}],
            }
        }
    }
}

OPENAI_OUTPUT_NOT_ARRAY = {
    "output": {  # object, not array
        "a": {"type": "web_search_call", "status": "completed"},
        "b": {
            "type": "message",
            "content": [
                {
                    "type": "output_text",
                    "text": "VERIFIED",
                    "annotations": [{"type": "url_citation", "url": "https://leak.org"}],
                }
            ],
        },
    }
}


def test_gemini_guard_fails_closed_on_non_array_candidates():
    """candidates as an object must not pass the guard (.candidates[]? would iterate its values)."""
    rc, _ = _run_jq(GEMINI_GUARD, GEMINI_CANDIDATES_NOT_ARRAY, exit_test=True)
    assert rc != 0


def test_gemini_sources_fails_closed_on_non_array_candidates():
    """candidates as an object must yield blank sources, not crash on `.candidates[0]`."""
    rc, sources = _run_jq(GEMINI_SOURCES, GEMINI_CANDIDATES_NOT_ARRAY, raw=True)
    assert rc == 0
    assert sources == ""


def test_openai_guard_fails_closed_on_non_array_output():
    """output as an object must not pass the guard (.output[]? would iterate its values)."""
    rc, _ = _run_jq(OPENAI_GUARD, OPENAI_OUTPUT_NOT_ARRAY, exit_test=True)
    assert rc != 0


def test_openai_sources_fails_closed_on_non_array_output():
    """output as an object must not surface a url nested in its values."""
    rc, sources = _run_jq(OPENAI_SOURCES, OPENAI_OUTPUT_NOT_ARRAY, raw=True)
    assert rc == 0
    assert sources == ""


# Nested-container fixtures: a valid array `output` but `content` / `annotations` arriving as an
# OBJECT. Every container on the OpenAI path (output → content → annotations → url) is normalized,
# so none of these may surface a nested url.

OPENAI_CONTENT_NOT_ARRAY = {
    "output": [
        {"type": "web_search_call", "status": "completed"},
        {
            "type": "message",
            "content": {  # object, not array
                "x": {
                    "type": "output_text",
                    "text": "VERIFIED",
                    "annotations": [{"type": "url_citation", "url": "https://leak.org"}],
                }
            },
        },
    ]
}

OPENAI_ANNOTATIONS_NOT_ARRAY = {
    "output": [
        {
            "type": "message",
            "content": [
                {
                    "type": "output_text",
                    "text": "VERIFIED",
                    "annotations": {"x": {"type": "url_citation", "url": "https://leak.org"}},
                }
            ],
        }
    ]
}


def test_openai_sources_fails_closed_on_non_array_content():
    """content as an object must not surface a url nested in its values."""
    rc, sources = _run_jq(OPENAI_SOURCES, OPENAI_CONTENT_NOT_ARRAY, raw=True)
    assert rc == 0
    assert sources == ""


def test_openai_sources_fails_closed_on_non_array_annotations():
    """annotations as an object must not surface a url nested in its values."""
    rc, sources = _run_jq(OPENAI_SOURCES, OPENAI_ANNOTATIONS_NOT_ARRAY, raw=True)
    assert rc == 0
    assert sources == ""


def test_openai_text_fails_closed_on_non_array_content():
    """content as an object must not surface text nested in its values."""
    rc, text = _run_jq(OPENAI_TEXT, OPENAI_CONTENT_NOT_ARRAY, raw=True)
    assert rc == 0
    assert text == ""


def test_openai_text_fails_closed_on_non_string_text():
    """#351: an output_text whose `text` is an object must not crash `join` (rc 5) — the malformed
    value is dropped, yielding empty text rather than a jq error."""
    payload = {
        "output": [
            {"type": "message", "content": [{"type": "output_text", "text": {"bad": 1}}]}
        ]
    }
    rc, text = _run_jq(OPENAI_TEXT, payload, raw=True)
    assert rc == 0
    assert text == ""


# #351 round 2: a malformed ARRAY ELEMENT (a non-object, e.g. `output: [5]` / `content: [7]`) must
# be skipped, not crash `.type` ("Cannot index number with \"type\""). Each iterated level now
# type-checks the element as an object before reading `.type`.
@pytest.mark.parametrize(
    "filter_path,payload",
    [
        (OPENAI_GUARD, {"output": [5]}),
        (OPENAI_TEXT, {"output": [5]}),
        (OPENAI_SOURCES, {"output": [5]}),
        (OPENAI_TEXT, {"output": [{"type": "message", "content": [7]}]}),
        (OPENAI_SOURCES, {"output": [{"type": "message", "content": [7]}]}),
        (OPENAI_SOURCES, {"output": [{"type": "message", "content": [{"type": "output_text", "annotations": [9]}]}]}),
    ],
    ids=["guard-output", "text-output", "sources-output", "text-content", "sources-content", "sources-annotations"],
)
def test_openai_filters_skip_non_object_array_elements(filter_path, payload):
    """A non-object array element at any iterated level must not crash the filter."""
    rc, out = _run_jq(filter_path, payload, raw=(filter_path is not OPENAI_GUARD),
                      exit_test=(filter_path is OPENAI_GUARD))
    if filter_path is OPENAI_GUARD:
        assert rc != 0  # no completed web_search_call → not grounded, no crash
    else:
        assert rc == 0 and out == ""  # nothing extracted, no crash


# #353 round 3 (cross-model review): the structural rederive array-normalized every CONTAINER but left the
# object DEREFERENCES unguarded, so a non-object at any field-access point crashed jq (rc 5,
# "Cannot index number with string …") instead of failing closed. `obj/1` now normalizes
# `candidates[0]`, `groundingMetadata`, each `groundingSupports` element, each cited
# `groundingChunks` element, and its `web`. These five shapes are the exact crash witnesses.
# Each carries an otherwise-valid grounded skeleton (webSearchQueries + one support citing index 0)
# so the malformed field is the only reason the verdict drops — proving the normalization, not a
# missing search signal, is what fails it closed.
_GEMINI_NONOBJECT_CASES = [
    {"candidates": [5]},
    {"candidates": [{"groundingMetadata": 5}]},
    {"candidates": [{"groundingMetadata": {
        "webSearchQueries": ["q"],
        "groundingChunks": [{"web": {"uri": "https://ok.org"}}],
        "groundingSupports": [5],
    }}]},
    {"candidates": [{"groundingMetadata": {
        "webSearchQueries": ["q"],
        "groundingChunks": [5],
        "groundingSupports": [{"groundingChunkIndices": [0]}],
    }}]},
    {"candidates": [{"groundingMetadata": {
        "webSearchQueries": ["q"],
        "groundingChunks": [{"web": 5}],
        "groundingSupports": [{"groundingChunkIndices": [0]}],
    }}]},
]


@pytest.mark.parametrize(
    "payload",
    _GEMINI_NONOBJECT_CASES,
    ids=["candidates0", "groundingMetadata", "groundingSupports-elem", "groundingChunks-elem", "web"],
)
def test_gemini_guard_fails_closed_on_non_object_dereference(payload):
    """The Gemini guard must return a clean non-grounded verdict (rc 1), never a jq crash (rc 5)."""
    rc, _ = _run_jq(GEMINI_GUARD, payload, exit_test=True)
    assert rc == 1, f"expected clean fail-closed (rc 1), got rc {rc} (rc 5 = jq crash)"


@pytest.mark.parametrize(
    "payload",
    _GEMINI_NONOBJECT_CASES,
    ids=["candidates0", "groundingMetadata", "groundingSupports-elem", "groundingChunks-elem", "web"],
)
def test_gemini_sources_fails_closed_on_non_object_dereference(payload):
    """The Gemini source extractor must yield blank (rc 0, empty), never a jq crash (rc 5)."""
    rc, sources = _run_jq(GEMINI_SOURCES, payload, raw=True)
    assert rc == 0, f"expected clean exit (rc 0), got rc {rc} (rc 5 = jq crash)"
    assert sources == "", f"malformed dereference must not fabricate a source, got {sources!r}"


# #353 round 4 (cross-model review): the FIRST hardening pass normalized every nested container/value but left
# the ROOT `.candidates` dereference itself unguarded — `arr(.candidates)` protects the *result*,
# not the access. A non-object root (`5`, `"x"`, `[]`, `true`) crashed jq before `arr` ran. Both my
# 176-run fuzz and the first 10 tests missed it because every fixture had a `{...}` root. Fixed with
# `arr(obj(.).candidates)`. `null` already fail-closed (`.candidates` on null is null), so it is a
# crash-free control here, not a regression witness.
@pytest.mark.parametrize(
    "root", [5, "x", True, [], {}, 1.5, None],
    ids=["int", "str", "bool", "array", "object", "float", "null"],
)
def test_gemini_filters_fail_closed_on_non_object_root(root):
    """A non-object (or empty-object) root must not crash either Gemini filter at `.candidates`."""
    rc_g, _ = _run_jq(GEMINI_GUARD, root, exit_test=True)
    rc_s, sources = _run_jq(GEMINI_SOURCES, root, raw=True)
    assert rc_g != 5, f"guard crashed (rc 5) on root {root!r}"
    assert rc_g != 0, f"guard must not pass an ungrounded non-object root {root!r}"
    assert rc_s == 0 and sources == "", f"sources must be blank, no crash, on root {root!r} (got rc {rc_s}, {sources!r})"


# ---------------------------------------------------------------------------
# Mutation test — prove the fixtures are not vacuously green
# ---------------------------------------------------------------------------


def test_mutation_accept_all_guard_would_be_caught():
    """An accept-all guard (`true`) MUST pass the from-memory fixtures — proving our real guards'
    rejection of them is meaningful, not an artifact of malformed fixtures.

    If swapping in a trivial `true` guard did NOT change the verdict on a from-memory fixture, the
    fixture could never distinguish a working guard from a broken one (vacuously green).
    """
    jq = _require_jq()
    # Real OpenAI guard rejects from-memory; accept-all must instead accept it.
    rc_real, _ = _run_jq(OPENAI_GUARD, OPENAI_FROM_MEMORY, exit_test=True)
    rc_mut = subprocess.run(
        [jq, "-e", "true"], input=json.dumps(OPENAI_FROM_MEMORY), capture_output=True, text=True
    ).returncode
    # The real guard rejects (non-0) and the accept-all mutant accepts (0): the fixture
    # discriminates a working guard from a broken one (these two facts imply rc_real != rc_mut).
    assert rc_real != 0, "real OpenAI guard should reject a from-memory response"
    assert rc_mut == 0, "accept-all mutant should pass it — confirms the fixture discriminates"

    # Same for Gemini.
    rc_real_g, _ = _run_jq(GEMINI_GUARD, GEMINI_SEARCH_NO_SUPPORT, exit_test=True)
    rc_mut_g = subprocess.run(
        [jq, "-e", "true"],
        input=json.dumps(GEMINI_SEARCH_NO_SUPPORT),
        capture_output=True,
        text=True,
    ).returncode
    assert rc_real_g != 0
    assert rc_mut_g == 0


def test_mutation_naive_sources_would_leak_negative_index():
    """The naive (pre-#349) Gemini source filter — indexing every support index without the
    type/range select — MUST extract the wrong URL on the negative-index fixture, proving the
    fail-closed guard is load-bearing (the fixture would catch a regression to the naive form).
    """
    jq = _require_jq()
    naive = (
        "(.candidates[0].groundingMetadata.groundingChunks // []) as $chunks "
        "| [ .candidates[0].groundingMetadata.groundingSupports[]?.groundingChunkIndices[]? ] "
        "| unique | [ .[] | $chunks[.].web.uri // empty ] | unique | join(\", \")"
    )
    naive_out = subprocess.run(
        [jq, "-r", naive],
        input=json.dumps(GEMINI_NEGATIVE_INDEX),
        capture_output=True,
        text=True,
    ).stdout.strip()
    # The naive filter fabricates the last chunk's URL from index -1 ...
    assert naive_out == "https://last.org"
    # ... while the canonical fail-closed filter yields blank — the regression is observable.
    _, canonical_out = _run_jq(GEMINI_SOURCES, GEMINI_NEGATIVE_INDEX, raw=True)
    assert canonical_out == ""
    assert naive_out != canonical_out
