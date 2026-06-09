"""Property-based tests for QoS compatibility checker using Hypothesis.

These tests verify invariants that must hold for ALL possible QoS combinations,
not just hand-picked examples. This catches edge cases that example-based tests miss.
"""

import os
import sys

from hypothesis import given, assume, settings
from hypothesis import strategies as st

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
from qos_checker import (
    QoSProfile, Reliability, Durability, History, Liveliness,
    check_compatibility, CompatibilityResult,
)

# -- Strategies --

reliability_st = st.sampled_from(list(Reliability))
durability_st = st.sampled_from(list(Durability))
history_st = st.sampled_from(list(History))
liveliness_st = st.sampled_from(list(Liveliness))
depth_st = st.integers(min_value=0, max_value=10000)
ms_st = st.integers(min_value=0, max_value=60000)


@st.composite
def qos_profile_st(draw):
    return QoSProfile(
        reliability=draw(reliability_st),
        durability=draw(durability_st),
        history=draw(history_st),
        depth=draw(depth_st),
        deadline_ms=draw(ms_st),
        lifespan_ms=draw(ms_st),
        liveliness=draw(liveliness_st),
        liveliness_lease_ms=draw(ms_st),
    )


class TestQoSPropertyInvariants:
    """Invariants that must hold for ALL QoS profile combinations."""

    @given(profile=qos_profile_st())
    @settings(max_examples=200)
    def test_identical_profiles_always_compatible(self, profile):
        """A profile must always be compatible with itself."""
        result = check_compatibility(profile, profile)
        assert result.compatible is True
        assert len(result.issues) == 0

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=500)
    def test_result_is_well_formed(self, pub, sub):
        """check_compatibility must always return a valid CompatibilityResult."""
        result = check_compatibility(pub, sub)
        assert isinstance(result, CompatibilityResult)
        assert isinstance(result.compatible, bool)
        assert isinstance(result.issues, list)
        assert isinstance(result.warnings, list)
        assert isinstance(result.suggestions, list)

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=500)
    def test_incompatible_implies_issues(self, pub, sub):
        """If result is incompatible, there must be at least one issue."""
        result = check_compatibility(pub, sub)
        if not result.compatible:
            assert len(result.issues) > 0

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=500)
    def test_no_issues_implies_compatible(self, pub, sub):
        """If there are no issues, the result must be compatible."""
        result = check_compatibility(pub, sub)
        if len(result.issues) == 0:
            assert result.compatible is True

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=500)
    def test_issues_have_suggestions(self, pub, sub):
        """Every incompatibility issue should have at least one suggestion."""
        result = check_compatibility(pub, sub)
        if len(result.issues) > 0:
            assert len(result.suggestions) > 0


class TestDDSRxOProperties:
    """Properties derived from DDS Request-vs-Offered (RxO) semantics."""

    @given(
        durability=durability_st,
        history=history_st,
        depth=depth_st,
        deadline_ms=ms_st,
        lifespan_ms=ms_st,
        liveliness=liveliness_st,
        liveliness_lease_ms=ms_st,
    )
    @settings(max_examples=200)
    def test_best_effort_pub_reliable_sub_always_incompatible(
        self, durability, history, depth, deadline_ms, lifespan_ms,
        liveliness, liveliness_lease_ms
    ):
        """BEST_EFFORT pub + RELIABLE sub is ALWAYS incompatible per DDS RxO."""
        pub = QoSProfile(
            Reliability.BEST_EFFORT, durability, history, depth,
            deadline_ms=deadline_ms, lifespan_ms=lifespan_ms,
            liveliness=liveliness, liveliness_lease_ms=liveliness_lease_ms,
        )
        sub = QoSProfile(
            Reliability.RELIABLE, durability, history, depth,
            deadline_ms=deadline_ms, lifespan_ms=lifespan_ms,
            liveliness=liveliness, liveliness_lease_ms=liveliness_lease_ms,
        )
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("RELIABILITY" in i for i in result.issues)

    @given(
        reliability=reliability_st,
        history=history_st,
        depth=depth_st,
        deadline_ms=ms_st,
        lifespan_ms=ms_st,
        liveliness=liveliness_st,
        liveliness_lease_ms=ms_st,
    )
    @settings(max_examples=200)
    def test_volatile_pub_transient_local_sub_always_incompatible(
        self, reliability, history, depth, deadline_ms, lifespan_ms,
        liveliness, liveliness_lease_ms
    ):
        """VOLATILE pub + TRANSIENT_LOCAL sub is ALWAYS incompatible per DDS RxO."""
        pub = QoSProfile(
            reliability, Durability.VOLATILE, history, depth,
            deadline_ms=deadline_ms, lifespan_ms=lifespan_ms,
            liveliness=liveliness, liveliness_lease_ms=liveliness_lease_ms,
        )
        sub = QoSProfile(
            reliability, Durability.TRANSIENT_LOCAL, history, depth,
            deadline_ms=deadline_ms, lifespan_ms=lifespan_ms,
            liveliness=liveliness, liveliness_lease_ms=liveliness_lease_ms,
        )
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("DURABILITY" in i for i in result.issues)

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=300)
    def test_deadline_rxo_semantics(self, pub, sub):
        """If both deadlines are set and pub > sub, must be incompatible."""
        assume(pub.deadline_ms > 0 and sub.deadline_ms > 0)
        assume(pub.deadline_ms > sub.deadline_ms)
        result = check_compatibility(pub, sub)
        assert any("DEADLINE" in i for i in result.issues)

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=300)
    def test_liveliness_lease_rxo_semantics(self, pub, sub):
        """If both leases are set and pub > sub, must be incompatible."""
        assume(pub.liveliness_lease_ms > 0 and sub.liveliness_lease_ms > 0)
        assume(pub.liveliness_lease_ms > sub.liveliness_lease_ms)
        result = check_compatibility(pub, sub)
        assert any("LIVELINESS LEASE" in i for i in result.issues)

    @given(
        reliability=reliability_st,
        durability=durability_st,
        history=history_st,
        depth=depth_st,
        deadline_ms=ms_st,
        lifespan_ms=ms_st,
        liveliness_lease_ms=ms_st,
    )
    @settings(max_examples=200)
    def test_automatic_pub_manual_sub_always_incompatible(
        self, reliability, durability, history, depth, deadline_ms,
        lifespan_ms, liveliness_lease_ms
    ):
        """AUTOMATIC pub + MANUAL_BY_TOPIC sub is ALWAYS incompatible."""
        pub = QoSProfile(
            reliability, durability, history, depth,
            deadline_ms=deadline_ms, lifespan_ms=lifespan_ms,
            liveliness=Liveliness.AUTOMATIC,
            liveliness_lease_ms=liveliness_lease_ms,
        )
        sub = QoSProfile(
            reliability, durability, history, depth,
            deadline_ms=deadline_ms, lifespan_ms=lifespan_ms,
            liveliness=Liveliness.MANUAL_BY_TOPIC,
            liveliness_lease_ms=liveliness_lease_ms,
        )
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("LIVELINESS" in i for i in result.issues)


class TestWarningProperties:
    """Property-based tests for warning conditions."""

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=300)
    def test_keep_all_always_warns(self, pub, sub):
        """Any KEEP_ALL usage should produce a warning."""
        assume(pub.history == History.KEEP_ALL or sub.history == History.KEEP_ALL)
        result = check_compatibility(pub, sub)
        assert any("KEEP_ALL" in w for w in result.warnings)

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=300)
    def test_depth_zero_keep_last_warns(self, pub, sub):
        """depth=0 with KEEP_LAST should always warn."""
        assume(
            (pub.history == History.KEEP_LAST and pub.depth == 0)
            or (sub.history == History.KEEP_LAST and sub.depth == 0)
        )
        result = check_compatibility(pub, sub)
        assert any("depth=0" in w for w in result.warnings)

    @given(pub=qos_profile_st(), sub=qos_profile_st())
    @settings(max_examples=300)
    def test_lifespan_shorter_than_deadline_warns(self, pub, sub):
        """Publisher lifespan < subscriber deadline should warn."""
        assume(pub.lifespan_ms > 0 and sub.deadline_ms > 0)
        assume(pub.lifespan_ms < sub.deadline_ms)
        result = check_compatibility(pub, sub)
        assert any("lifespan" in w.lower() for w in result.warnings)
