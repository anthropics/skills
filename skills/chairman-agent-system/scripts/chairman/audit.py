"""Hash-chained audit records.

Each entry commits to the one before it, so altering or deleting any record
invalidates every hash after it. :func:`verify_chain` finds the first break.

What this gives you, precisely: **tamper evidence**, not tamper prevention.
Anyone who can write to the database can also recompute the whole chain. To
get a guarantee rather than a signal, the head hash has to be anchored
somewhere the same party cannot rewrite — printed in an external log,
committed to a separate append-only store, or countersigned. The chain
detects casual and partial edits, which is the common case; it does not stop
a determined operator with database access.
"""

from __future__ import annotations

import hashlib
import json
from typing import Iterable, List, Sequence, Tuple

from .models import AuditEntry

GENESIS_HASH = "0" * 64


def _canonical(payload: dict) -> str:
    """Deterministic JSON so an identical record always hashes identically."""
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), default=str)


def compute_hash(
    prev_hash: str,
    seq: int,
    timestamp: str,
    actor: str,
    action: str,
    resource: str,
    outcome: str,
    details: dict,
) -> str:
    body = _canonical(
        {
            "seq": seq,
            "timestamp": timestamp,
            "actor": actor,
            "action": action,
            "resource": resource,
            "outcome": outcome,
            "details": details,
        }
    )
    return hashlib.sha256((prev_hash + body).encode("utf-8")).hexdigest()


def entry_hash_of(entry: AuditEntry) -> str:
    """Recompute an entry's hash from its own contents."""
    return compute_hash(
        entry.prev_hash,
        entry.seq,
        entry.timestamp,
        entry.actor,
        entry.action,
        entry.resource,
        entry.outcome,
        entry.details,
    )


def verify_chain(entries: Sequence[AuditEntry]) -> Tuple[bool, List[str]]:
    """Walk the log and report every integrity break found.

    Returns ``(ok, problems)``. An empty log is trivially valid.
    """
    problems: List[str] = []
    expected_prev = GENESIS_HASH

    for index, entry in enumerate(entries):
        expected_seq = index + 1
        if entry.seq != expected_seq:
            problems.append(
                f"entry {index}: sequence is {entry.seq}, expected {expected_seq} "
                "(record inserted or deleted)"
            )

        if entry.prev_hash != expected_prev:
            problems.append(
                f"seq {entry.seq}: prev_hash does not match the preceding entry "
                "(chain broken)"
            )

        recomputed = entry_hash_of(entry)
        if recomputed != entry.entry_hash:
            problems.append(
                f"seq {entry.seq}: contents do not match stored hash (record altered)"
            )

        expected_prev = entry.entry_hash

    return (not problems, problems)


def head_hash(entries: Iterable[AuditEntry]) -> str:
    """The hash to anchor externally. Commits to the entire log to date."""
    last = GENESIS_HASH
    for entry in entries:
        last = entry.entry_hash
    return last
