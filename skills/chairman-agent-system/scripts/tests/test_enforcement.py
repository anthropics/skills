"""The enforcement point: authorization that cannot be skipped by not asking."""

from __future__ import annotations

import threading
import unittest

from chairman import (
    Classification,
    Level,
    NotFound,
    PermissionDenied,
    Registry,
    Session,
    Store,
    Tool,
    ToolBox,
    active_tools,
)

COMPLETE = dict(
    purpose="Ledger reconciliation and anomaly detection",
    objectives=["Flag anomalies within 24h"],
    reporting="Daily briefing",
    risks="Touches confidential ledger data",
)


class EnforcementTestCase(unittest.TestCase):
    def setUp(self):
        self.store = Store(":memory:")
        self.registry = Registry(self.store)
        self.registry.install_chairman()
        self.box = ToolBox()
        self.calls: list = []

        @self.box.register("ledger.balance", Tool.FINANCE, Classification.CONFIDENTIAL)
        def balance(account: str) -> float:
            self.calls.append(("balance", account))
            return 42.0

        @self.box.register(
            "ledger.post", Tool.FINANCE, Classification.CONFIDENTIAL, writes=True
        )
        def post(account: str, amount: float) -> str:
            self.calls.append(("post", account, amount))
            return "posted"

        @self.box.register("scan.run", Tool.SECURITY, Classification.INTERNAL)
        def scan(target: str) -> str:
            self.calls.append(("scan", target))
            return "clean"

        @self.box.register("boom", Tool.FINANCE, Classification.PUBLIC)
        def boom() -> None:
            raise RuntimeError("handler exploded")

        self.balance = balance
        self.post = post
        self.scan = scan
        self.boom = boom

    def tearDown(self):
        self.store.close()

    def make(self, name, level=Level.OPERATOR, tools=(Tool.FINANCE,),
             classification=Classification.CONFIDENTIAL):
        request = self.registry.request_agent(
            requested_by="chairman", name=name, level=level, tools=tools,
            max_classification=classification, **COMPLETE,
        )
        return self.registry.approve_request(request.request_id, approver="chairman")

    def session_for(self, name, **kw):
        self.make(name, **kw)
        return Session(self.registry, self.box, name)


class TestBypass(EnforcementTestCase):
    """The property the whole module exists for."""

    def test_direct_call_is_refused(self):
        self.session_for("analyst")
        with self.assertRaises(PermissionDenied) as ctx:
            self.balance("ACME")
        self.assertIn("must be invoked through an authorized Session", str(ctx.exception))
        self.assertEqual(self.calls, [])

    def test_direct_call_refused_even_with_a_live_session_open(self):
        """Holding a session does not unlock the raw function."""
        session = self.session_for("analyst")
        session.invoke("ledger.balance", "ACME")
        self.calls.clear()
        with self.assertRaises(PermissionDenied):
            self.balance("ACME")
        self.assertEqual(self.calls, [])

    def test_guard_closes_after_a_successful_invoke(self):
        session = self.session_for("analyst")
        session.invoke("ledger.balance", "ACME")
        self.assertEqual(active_tools(), frozenset())

    def test_guard_closes_after_the_handler_raises(self):
        session = self.session_for("analyst")
        with self.assertRaises(RuntimeError):
            session.invoke("boom")
        self.assertEqual(active_tools(), frozenset())
        with self.assertRaises(PermissionDenied):
            self.boom()

    def test_guard_authorizes_one_tool_at_a_time(self):
        """Crossing a tool boundary always costs an authorization."""
        session = self.session_for(
            "analyst", tools=(Tool.FINANCE, Tool.SECURITY)
        )

        @self.box.register("nested", Tool.FINANCE, Classification.PUBLIC)
        def nested():
            # Reaching a second tool from inside the first must not inherit
            # the caller's clearance.
            return self.scan("host")

        with self.assertRaises(PermissionDenied):
            session.invoke("nested")

    def test_guard_does_not_leak_across_threads(self):
        session = self.session_for("analyst")
        leaked = []

        @self.box.register("threaded", Tool.FINANCE, Classification.PUBLIC)
        def threaded():
            def worker():
                try:
                    self.balance("ACME")
                    leaked.append("guard leaked into thread")
                except PermissionDenied:
                    leaked.append("refused")

            t = threading.Thread(target=worker)
            t.start()
            t.join()
            return leaked

        session.invoke("threaded")
        self.assertEqual(leaked, ["refused"])


class TestAuthorization(EnforcementTestCase):
    def test_permitted_call_returns_the_handler_result(self):
        session = self.session_for("analyst")
        self.assertEqual(session.invoke("ledger.balance", "ACME"), 42.0)
        self.assertEqual(self.calls, [("balance", "ACME")])

    def test_denies_tool_outside_the_agents_grant(self):
        session = self.session_for("analyst", tools=(Tool.FINANCE,))
        with self.assertRaises(PermissionDenied) as ctx:
            session.invoke("scan.run", "host")
        self.assertIn("not granted", str(ctx.exception))
        self.assertEqual(self.calls, [])

    def test_denies_write_tool_below_operator_level(self):
        """Isolate the write floor from the clearance check.

        ``ledger.post`` is CONFIDENTIAL, so a level 2 agent fails on
        clearance before the write rule is ever consulted. Registering a
        write tool the agent *can* read proves the floor bites on its own.
        """

        @self.box.register(
            "notes.append", Tool.FINANCE, Classification.INTERNAL, writes=True
        )
        def append(text: str) -> str:
            return text

        session = self.session_for(
            "junior", level=Level.INTERNAL, classification=Classification.INTERNAL
        )
        with self.assertRaises(PermissionDenied) as ctx:
            session.invoke("notes.append", "hello")
        self.assertIn("write requires", str(ctx.exception))

    def test_denies_classification_above_clearance(self):
        session = self.session_for(
            "junior", level=Level.INTERNAL, classification=Classification.INTERNAL
        )
        with self.assertRaises(PermissionDenied):
            session.invoke("ledger.balance", "ACME")

    def test_suspended_agent_cannot_invoke(self):
        session = self.session_for("analyst")
        session.invoke("ledger.balance", "ACME")
        self.registry.suspend("analyst", by="chairman", reason="under review")
        with self.assertRaises(PermissionDenied):
            session.invoke("ledger.balance", "ACME")

    def test_unknown_tool_raises_not_found(self):
        session = self.session_for("analyst")
        with self.assertRaises(NotFound):
            session.invoke("nope.missing")

    def test_unknown_agent_fails_at_session_construction(self):
        with self.assertRaises(NotFound):
            Session(self.registry, self.box, "ghost")


class TestDynamicClassification(EnforcementTestCase):
    def test_sensitivity_can_depend_on_arguments(self):
        def by_path(path: str) -> Classification:
            return (
                Classification.RESTRICTED
                if path.startswith("/payroll")
                else Classification.PUBLIC
            )

        @self.box.register("fs.read", Tool.FINANCE, by_path)
        def read(path: str) -> str:
            return f"contents of {path}"

        session = self.session_for("analyst")  # cleared to CONFIDENTIAL
        self.assertEqual(session.invoke("fs.read", "/public/x"), "contents of /public/x")
        with self.assertRaises(PermissionDenied):
            session.invoke("fs.read", "/payroll/y")

    def test_classifier_returning_wrong_type_is_rejected(self):
        @self.box.register("bad", Tool.FINANCE, lambda: "confidential")
        def bad():
            return None

        session = self.session_for("analyst")
        with self.assertRaises(TypeError):
            session.invoke("bad")


class TestAuditTrail(EnforcementTestCase):
    def test_permission_decision_and_execution_are_logged_separately(self):
        session = self.session_for("analyst")
        session.invoke("ledger.balance", "ACME")
        actions = [e.action for e in self.registry.audit_log()]
        self.assertIn("read:finance", actions)
        self.assertIn("invoke:ledger.balance", actions)

    def test_denied_invocation_is_logged(self):
        session = self.session_for("analyst", tools=(Tool.FINANCE,))
        with self.assertRaises(PermissionDenied):
            session.invoke("scan.run", "host")
        denied = [e for e in self.registry.audit_log() if e.outcome == "denied"]
        self.assertTrue(denied)

    def test_handler_failure_is_logged_as_error_not_denial(self):
        session = self.session_for("analyst")
        with self.assertRaises(RuntimeError):
            session.invoke("boom")
        entry = [e for e in self.registry.audit_log() if e.action == "invoke:boom"][-1]
        self.assertEqual(entry.outcome, "error")
        self.assertEqual(entry.details["error"], "RuntimeError")

    def test_chain_stays_verifiable_through_mixed_traffic(self):
        session = self.session_for("analyst", tools=(Tool.FINANCE,))
        session.invoke("ledger.balance", "ACME")
        for bad in (lambda: session.invoke("scan.run", "h"), lambda: session.invoke("boom")):
            with self.assertRaises(Exception):
                bad()
        ok, problems = self.registry.verify_audit()
        self.assertTrue(ok, problems)


class TestToolBox(EnforcementTestCase):
    def test_duplicate_registration_is_refused(self):
        with self.assertRaises(ValueError):
            @self.box.register("ledger.balance", Tool.FINANCE, Classification.PUBLIC)
            def dupe():
                return None

    def test_registration_preserves_function_metadata(self):
        self.assertEqual(self.balance.__name__, "balance")
        self.assertEqual(self.balance.__chairman_tool__, "ledger.balance")

    def test_available_lists_only_what_the_agent_may_call(self):
        session = self.session_for("analyst", tools=(Tool.FINANCE,))
        available = session.available()
        self.assertIn("ledger.balance", available)
        self.assertIn("ledger.post", available)
        self.assertNotIn("scan.run", available)

    def test_available_reflects_write_restrictions(self):
        session = self.session_for(
            "junior", level=Level.INTERNAL, classification=Classification.INTERNAL
        )
        self.assertNotIn("ledger.post", session.available())


if __name__ == "__main__":
    unittest.main()
