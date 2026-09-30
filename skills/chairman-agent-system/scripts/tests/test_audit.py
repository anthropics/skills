"""The audit chain must notice edits, deletions, and insertions."""

from __future__ import annotations

import json
import unittest

from chairman import GENESIS_HASH, Registry, Store, head_hash, verify_chain


class TestAuditChain(unittest.TestCase):
    def setUp(self):
        self.store = Store(":memory:")
        self.registry = Registry(self.store)
        self.registry.install_chairman()

    def tearDown(self):
        self.store.close()

    def test_empty_log_verifies(self):
        ok, problems = verify_chain([])
        self.assertTrue(ok)
        self.assertEqual(problems, [])

    def test_clean_log_verifies(self):
        for i in range(5):
            self.store.append_audit("chairman", "test", f"res-{i}", "allowed", {"i": i})
        ok, problems = self.registry.verify_audit()
        self.assertTrue(ok, problems)

    def test_first_entry_chains_to_genesis(self):
        entries = self.store.list_audit()
        self.assertEqual(entries[0].prev_hash, GENESIS_HASH)

    def test_entries_chain_to_predecessor(self):
        self.store.append_audit("chairman", "test", "a", "allowed")
        self.store.append_audit("chairman", "test", "b", "allowed")
        entries = self.store.list_audit()
        for prev, curr in zip(entries, entries[1:]):
            self.assertEqual(curr.prev_hash, prev.entry_hash)

    def test_detects_altered_record(self):
        self.store.append_audit("chairman", "read:finance", "ledger", "denied")
        entries = self.store.list_audit()
        target = entries[-1]

        # Flip a denial into an approval, leaving the stored hash untouched —
        # exactly what someone covering their tracks would try.
        self.store._raw_execute(
            "UPDATE audit SET outcome = ? WHERE seq = ?", ("allowed", target.seq)
        )

        ok, problems = self.registry.verify_audit()
        self.assertFalse(ok)
        self.assertTrue(any("do not match stored hash" in p for p in problems))

    def test_detects_deleted_record(self):
        for i in range(4):
            self.store.append_audit("chairman", "test", f"res-{i}", "allowed")
        entries = self.store.list_audit()
        victim = entries[2]

        self.store._raw_execute("DELETE FROM audit WHERE seq = ?", (victim.seq,))

        ok, problems = self.registry.verify_audit()
        self.assertFalse(ok)
        self.assertTrue(any("sequence is" in p or "chain broken" in p for p in problems))

    def test_detects_altered_details_payload(self):
        self.store.append_audit(
            "chairman", "assign_task", "task-1", "allowed", {"budget": 100}
        )
        entries = self.store.list_audit()
        target = entries[-1]

        self.store._raw_execute(
            "UPDATE audit SET details = ? WHERE seq = ?",
            (json.dumps({"budget": 1_000_000}), target.seq),
        )

        ok, problems = self.registry.verify_audit()
        self.assertFalse(ok)

    def test_head_hash_changes_on_every_append(self):
        first = head_hash(self.store.list_audit())
        self.store.append_audit("chairman", "test", "x", "allowed")
        second = head_hash(self.store.list_audit())
        self.assertNotEqual(first, second)

    def test_denials_are_recorded_not_just_approvals(self):
        from chairman import Classification, Tool

        # The Chairman holds every tool, so force a denial via clearance on a
        # weaker agent instead — see test_registry for the full path. Here we
        # only assert that a denied outcome reaches the log at all.
        self.store.append_audit("someone", "read:finance", "ledger", "denied", {})
        outcomes = [e.outcome for e in self.store.list_audit()]
        self.assertIn("denied", outcomes)


if __name__ == "__main__":
    unittest.main()
