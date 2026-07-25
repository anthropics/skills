#!/usr/bin/env python3
"""Citation verification summary reducer (Delta 4) — SINGLE SOURCE OF TRUTH.

Reduces per-resolver outcomes to the 3-class `lookup_verified` value using the
v3.11 narrowed-false definition (C-V6(a)): `false` requires at least one
ID-keyed unmatched (a DOI/arXiv ID that provably fails to resolve = fabrication
evidence); a title-only unmatched (no resolvable identifier to key on) is a
coverage gap and reduces to `unresolvable`, never `false`.

run_evals.py imports `reduce_lookup_verified` from here; there is exactly one
reducer implementation in the repo (the old un-narrowed copy in run_evals.py
was removed when this landed).

OQ-5 recall limit (user-facing surfacing deferred). The narrowed-false rule
means a fabricated citation that carries NO resolvable identifier (no DOI /
arXiv ID, only a bogus title) reduces to `unresolvable`, NOT `false`, so the
citation-existence gate does not block it — it is indistinguishable from a
legitimately unindexed (regional / non-English / pre-digital) paper. This is an
accepted recall limit, caught instead by the v3.8 claim-faithfulness audit +
human review. The user-facing explanation of this limit (in docs/ARCHITECTURE.md
and the user guide) and the policy that consumes this verdict
(`terminal_policies.citation_existence`, enum {advisory, strict}) both land with
the Delta 3 / C-V6 policy batch — this data-layer batch only computes the
verdict; it does not gate on it. Gold fixture 051 (the OQ-5 by-design
false-negative: a no-identifier fabrication) pins that a title-only unmatched
reduces to unresolvable, never false. The complementary real-but-unindexed
canary remains unfilled (issue #250).

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md
§2 Delta 4 + §0(4a) + INVARIANT C-V6(a).
"""
from __future__ import annotations

from typing import Any, Mapping

STATUS_MATCHED = "matched"
STATUS_UNMATCHED = "unmatched"
STATUS_UNREACHABLE = "unreachable"
STATUS_SKIPPED = "skipped"

QUERIED_BY_ID = "id"


def reduce_lookup_verified(resolver_outcomes: Mapping[str, Any]) -> str:
    """Reduce per-resolver outcomes to a 3-class lookup_verified value.

    Each value in `resolver_outcomes` is a dict with at least `status`, and
    (for unmatched rows) `queried_by` ∈ {'id', 'title', None}.

    Rules (symmetric 3-class; `unresolvable` is NEVER collapsed into `false`):

    * `skipped` outcomes are EXCLUDED from classification (resolver
      applicability / policy, not adjudication). "applicable" = not skipped.
    * `true` iff >=1 applicable resolver is `matched` (matched WINS — true even
      if another applicable resolver is `unmatched`).
    * `false` (v3.11 narrowed, C-V6(a)) iff NO applicable resolver is `matched`
      AND >=1 applicable resolver is an **ID-keyed** `unmatched`
      (status=unmatched AND queried_by='id'). A bogus DOI/arXiv ID that
      provably fails to resolve is fabrication evidence. Anti-fabrication bias:
      one ID-keyed unmatched stands even alongside an `unreachable` (a transient
      outage does not cancel positive non-existence evidence).
    * `unresolvable` otherwise — every applicable resolver `unreachable` (total
      outage), OR every resolver `skipped` (empty adjudicating set, manual
      exempt), OR the only negative signals are title-only `unmatched`
      (queried_by != 'id' — no resolvable identifier to key on = coverage gap,
      the real-but-unindexed paper; C-V6(a)/(f) + OQ-5 by-design FN).
    """
    outcomes = [v or {} for v in resolver_outcomes.values()]
    applicable = [o for o in outcomes if o.get("status") != STATUS_SKIPPED]

    if any(o.get("status") == STATUS_MATCHED for o in applicable):
        return "true"

    id_keyed_unmatched = any(
        o.get("status") == STATUS_UNMATCHED and o.get("queried_by") == QUERIED_BY_ID
        for o in applicable
    )
    if id_keyed_unmatched:
        return "false"

    return "unresolvable"
