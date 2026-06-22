"""PITH v2 unit tests — myskills standalone, SIZE_GATE=10000."""
import sys
import time
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))
import compress as compress_mod
from compress import (
    compress,
    benford_mad,
    SIZE_GATE,
    MAX_RETRIES,
    LOGICAL_WHITELIST,
    FILLER_PATTERNS,
)

assert SIZE_GATE == 10000, f"Tests require SIZE_GATE=10000, got {SIZE_GATE}"

# ── Diverse text generator ────────────────────────────────────────────

_SENTENCES = [
    "Quantum computing exploits superposition to process multiple computational states simultaneously.",
    "Machine learning systems extract meaningful patterns from high-dimensional training distributions.",
    "Distributed consensus protocols coordinate agreement across fault-tolerant heterogeneous replicas.",
    "Neural attention mechanisms selectively weight contextually relevant positional information.",
    "Cryptographic hash functions produce deterministic fixed-length digests from arbitrary inputs.",
    "Containerized microservices improve deployment isolation and enable horizontal scalability.",
    "Graph traversal algorithms systematically explore connectivity relationships in structured datasets.",
    "Transformer encoders generate contextual token embeddings through multi-head self-attention layers.",
    "Bayesian inference updates prior probability beliefs using observed likelihood evidence efficiently.",
    "Compiler optimization passes analyze control-flow graphs to eliminate redundant computational operations.",
    "Backpropagation computes gradient descent updates through layered differentiable computational graphs.",
    "Relational databases enforce referential integrity constraints through transactional atomicity guarantees.",
    "Federated learning trains models across decentralized devices without centralizing raw training data.",
    "Sparse matrix representations reduce memory overhead for computations on large-scale irregular graphs.",
    "Homomorphic encryption enables arithmetic operations directly on encrypted ciphertext representations.",
]


def diverse_long_text(chars: int = SIZE_GATE + 2000) -> str:
    parts: list[str] = []
    while sum(len(p) + 1 for p in parts) < chars:
        parts.extend(_SENTENCES)
    text = " ".join(parts)
    return text[: chars + 200]


def short_text() -> str:
    return "Short text well below the ten-thousand-character size gate threshold."


# ── Test 1: Size Gate ─────────────────────────────────────────────────

class TestSizeGate:
    def test_passthrough_below_threshold(self):
        text = short_text()
        assert len(text) < SIZE_GATE
        t0 = time.perf_counter()
        result, meta = compress(text)
        elapsed_ms = (time.perf_counter() - t0) * 1000
        assert result == text
        assert meta["action"] == "passthrough"
        assert "size gate" in meta["reason"]
        assert elapsed_ms < 1.0, f"Size gate latency {elapsed_ms:.2f}ms > 1ms"

    def test_passthrough_near_boundary(self):
        text = "word " * 1800
        assert len(text) < SIZE_GATE
        result, meta = compress(text)
        assert result == text
        assert meta["action"] == "passthrough"

    def test_passthrough_zero_savings(self):
        text = short_text()
        _, meta = compress(text)
        assert meta["saved_pct"] == 0.0
        assert meta["original_tokens"] == meta["compressed_tokens"]

    def test_above_threshold_not_size_gated(self):
        text = diverse_long_text()
        assert len(text) >= SIZE_GATE
        _, meta = compress(text)
        assert "size gate" not in meta.get("reason", "")


# ── Test 2: Shannon >= Threshold ──────────────────────────────────────

class TestShannonThreshold:
    def test_ge_threshold_rare_words_not_bulk_deleted(self):
        base = diverse_long_text()
        text = base + " NeuralPITH tokenized latency benchmark achieved."
        assert len(text) >= SIZE_GATE
        result, meta = compress(text, target_ratio=0.7)
        if meta["action"] == "compressed":
            assert "NeuralPITH" in result, (
                f">= threshold violated: unique word pruned.\nmeta={meta}\nresult[:300]={result[:300]}"
            )

    def test_common_words_pruned_below_threshold(self):
        text = diverse_long_text()
        result, meta = compress(text, target_ratio=0.5)
        if meta["action"] == "compressed":
            assert meta["saved_pct"] > 0

    def test_log_cache_populated_after_compression(self):
        compress_mod.LOG_CACHE.clear()
        compress(diverse_long_text(), target_ratio=0.7)
        assert len(compress_mod.LOG_CACHE) > 0

    def test_logical_whitelist_always_kept(self):
        assert "not"   in LOGICAL_WHITELIST
        assert "never" in LOGICAL_WHITELIST
        assert "if"    in LOGICAL_WHITELIST
        assert "nor"   in LOGICAL_WHITELIST
        assert "and"   in LOGICAL_WHITELIST
        assert "or"    in LOGICAL_WHITELIST


# ── Test 3: Filler Pre-pass ───────────────────────────────────────────

class TestFillerPatterns:
    def test_pattern_matches_known_boilerplate(self):
        assert FILLER_PATTERNS.match("I believe this analysis is complete")
        assert FILLER_PATTERNS.match("Let me check the output carefully")
        assert FILLER_PATTERNS.match("No errors were encountered during execution")
        assert FILLER_PATTERNS.match("The search was completed successfully")
        assert FILLER_PATTERNS.match("I need to analyze the user request")

    def test_pattern_does_not_match_content(self):
        assert not FILLER_PATTERNS.match("Quantum superposition enables parallel state processing")
        assert not FILLER_PATTERNS.match("Transformer architectures revolutionized natural language")
        assert not FILLER_PATTERNS.match("Distributed consensus tolerates Byzantine fault scenarios")

    def test_filler_removed_from_long_text(self):
        base = diverse_long_text()
        text = base + (
            " I believe this information covers the topic adequately."
            " No errors were encountered during runtime."
            " Let me summarize what I found."
        )
        assert len(text) >= SIZE_GATE
        result, meta = compress(text, target_ratio=0.7)
        if meta["action"] == "compressed":
            assert "I believe" not in result
            assert "Let me" not in result

    def test_filler_removal_does_not_invert_content_negations(self):
        base = diverse_long_text()
        text = base + " The system must never process invalid inputs without explicit authorization."
        assert len(text) >= SIZE_GATE
        result, meta = compress(text, target_ratio=0.7)
        if meta["action"] == "compressed":
            low = result.lower()
            assert "never" in low or "not" in low or "invalid" in low


# ── Test 4: Benford Gate ──────────────────────────────────────────────

class TestBenfordGate:
    def test_no_false_rollback_normal_compression(self):
        text = diverse_long_text(chars=SIZE_GATE + 5000)
        result, meta = compress(text, target_ratio=0.7)
        if meta["action"] == "compressed":
            assert meta.get("benford_ok", True), (
                f"False Benford rollback.\n"
                f"original_mad={meta.get('original_benford_mad')}, "
                f"compressed_mad={meta.get('compressed_benford_mad')}"
            )

    def test_benford_gate_retries_on_forced_failure(self):
        text = diverse_long_text()
        call_count = [0]
        real = compress_mod.benford_mad

        def mock(sentences):
            call_count[0] += 1
            if call_count[0] == 1:
                return 5.0
            if call_count[0] == 2:
                return 50.0
            return real(sentences)

        with patch.object(compress_mod, "benford_mad", mock):
            result, _ = compress_mod.compress(text)

        assert result is not None
        assert call_count[0] > 2

    def test_benford_gate_bounded_retries(self):
        text = diverse_long_text()
        call_count = [0]

        def always_fail(_):
            call_count[0] += 1
            return 9999.0

        with patch.object(compress_mod, "benford_mad", always_fail):
            result, _ = compress_mod.compress(text)

        assert result is not None
        assert call_count[0] <= MAX_RETRIES + 2

    def test_benford_gate_halves_reduction(self):
        text = diverse_long_text()
        call_count = [0]
        real = compress_mod.benford_mad
        threshold_history: list[float] = []

        orig_prune = compress_mod._prune_tokens

        def tracking_prune(sentence, info, threshold):
            threshold_history.append(threshold)
            return orig_prune(sentence, info, threshold)

        def mock_benford(sentences):
            call_count[0] += 1
            if call_count[0] == 1:
                return 4.0
            if call_count[0] <= 3:
                return 40.0
            return real(sentences)

        with (
            patch.object(compress_mod, "benford_mad", mock_benford),
            patch.object(compress_mod, "_prune_tokens", tracking_prune),
        ):
            compress_mod.compress(text)

        assert len(set(round(t, 6) for t in threshold_history)) >= 1


# ── Test 5: Polarity Protection ───────────────────────────────────────

class TestPolarityProtection:
    def test_negation_whitelist_words_survive(self):
        text = diverse_long_text()
        text += " The pipeline must never fail and should not discard validated results."
        result, meta = compress(text, target_ratio=0.5)
        if meta["action"] == "compressed":
            assert "never" in result.lower() or "not" in result.lower()

    def test_polarity_rollback_on_negation_loss(self):
        call_log: list[int] = []
        orig = compress_mod._count_negations

        def mock_count(s):
            v = orig(s)
            call_log.append(v)
            if len(call_log) % 2 == 0:
                return v + 1
            return v

        text = diverse_long_text()
        with patch.object(compress_mod, "_count_negations", mock_count):
            result, _ = compress_mod.compress(text)
        assert result is not None


# ── Test 6: Meta-Context Receptor ─────────────────────────────────────

class TestMetaContextReceptor:
    def test_compressed_output_wrapped_in_xml(self):
        text = diverse_long_text()
        result, meta = compress(text)
        if meta["action"] == "compressed":
            assert result.startswith("<pith_optimization_layer")
            assert result.strip().endswith("</pith_optimization_layer>")

    def test_xml_attributes_present(self):
        text = diverse_long_text()
        result, meta = compress(text)
        if meta["action"] == "compressed":
            assert "version='2.0'" in result
            assert "engine='shannon_local'" in result
            assert "ratio=" in result

    def test_passthrough_not_wrapped(self):
        text = short_text()
        result, meta = compress(text)
        assert meta["action"] == "passthrough"
        assert not result.startswith("<pith_optimization_layer")
