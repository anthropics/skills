#!/usr/bin/env python3
"""Anti-false-closure pebble for #272 (DELIBERATELY xfail).

The #272 guidance layer ships a *documented* instruction/data boundary and a lint
that keeps the documentation from rotting. It provides NO verified runtime
defense against indirect prompt injection: a static document cannot guarantee the
model honors the principle when a live fetch returns adversarial content. That
runtime defense belongs to the structural (envelope / task-dispatch) layer —
#134 Slice 3+ — and is not built yet.

This test exists so that absence is visible and un-ignorable in the codebase,
rather than living only in an issue tracker where "we already added guidance for
the boundary" can quietly become a permanent excuse to never build the real
defense. It is the codebase analogue of a reverse-invariant pin.

It is marked xfail (expected to fail), so CI stays green. DO NOT delete it to make
CI "cleaner." Remove it only when the structural runtime defense actually lands —
at which point this becomes a real, passing assertion (drop the xfail marker and
wire it to the runtime mechanism).

Design: docs/design/2026-06-07-272-instruction-data-boundary-design.md § 6.
Structural home: #134 Slice 3+.

Run:
    python -m pytest scripts/test_runtime_injection_boundary_xfail.py
"""
from __future__ import annotations

import sys

import pytest


@pytest.mark.xfail(
    reason="Runtime instruction/data enforcement is unbuilt (#272 structural "
           "layer / #134 Slice 3+). The guidance layer documents the boundary "
           "but does not enforce it at runtime. Remove this xfail only when the "
           "structural defense lands.",
    strict=True,
)
def test_runtime_injection_boundary_is_enforced():
    """Placeholder for the unbuilt runtime defense.

    When the structural layer exists, this asserts that an agent receiving
    retrieved content carrying an embedded instruction does NOT act on that
    instruction at runtime. Today there is no runtime mechanism to assert against,
    so the pin fails by construction.
    """
    runtime_enforcement_exists = False  # flips True when the structural layer lands
    assert runtime_enforcement_exists, (
        "No runtime instruction/data enforcement mechanism exists yet "
        "(#272 structural layer / #134 Slice 3+)."
    )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
