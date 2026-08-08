"""End-to-end lifecycle: proposal, approval, delegation, termination."""

from __future__ import annotations

import unittest

from chairman import (
    AgentStatus,
    Classification,
    IncompleteRequest,
    Level,
    NotFound,
    PermissionDenied,
    Registry,
    RequestStatus,
    StateError,
    Store,
    Tool,
)

COMPLETE = dict(
    purpose="Daily financial metrics analysis and anomaly detection",
    objectives=["Flag anomalies within 24h", "Publish a daily briefing"],
    reporting="Daily briefing, weekly deep dive",
    risks="Handles confidential ledger data; mis-flagging wastes analyst time",
)


class RegistryTestCase(unittest.TestCase):
    def setUp(self):
        self.store = Store(":memory:")
        self.registry = Registry(self.store)
        self.chairman = self.registry.install_chairman()

    def tearDown(self):
        self.store.close()

    def make(self, name, level=Level.EXECUTIVE, tools=(Tool.FINANCE,),
             classification=Classification.CONFIDENTIAL, parent="chairman"):
        request = self.registry.request_agent(
            requested_by=parent,
            name=name,
            level=level,
            tools=tools,
            max_classification=classification,
            **COMPLETE,
        )
        return self.registry.approve_request(request.request_id, approver="chairman")


class TestBootstrap(RegistryTestCase):
    def test_chairman_holds_every_tool(self):
        self.assertEqual(self.chairman.tools, frozenset(Tool))
        self.assertEqual(self.chairman.level, Level.CHAIRMAN)

    def test_install_is_idempotent(self):
        again = self.registry.install_chairman()
        self.assertEqual(again.agent_id, self.chairman.agent_id)

    def test_refuses_second_chairman_under_different_name(self):
        with self.assertRaises(StateError):
            self.registry.install_chairman(name="usurper")


class TestProposalGate(RegistryTestCase):
    def test_rejects_proposal_missing_justification(self):
        with self.assertRaises(IncompleteRequest) as ctx:
            self.registry.request_agent(
                requested_by="chairman",
                name="vague-agent",
                level=Level.OPERATOR,
                tools=[Tool.FINANCE],
                max_classification=Classification.INTERNAL,
                purpose="",
                objectives=[],
                reporting="",
                risks="",
            )
        message = str(ctx.exception)
        for field in ("purpose", "objectives", "reporting", "risks"):
            self.assertIn(field, message)

    def test_incomplete_proposal_is_still_audited(self):
        with self.assertRaises(IncompleteRequest):
            self.registry.request_agent(
                requested_by="chairman",
                name="vague-agent",
                level=Level.OPERATOR,
                tools=[Tool.FINANCE],
                max_classification=Classification.INTERNAL,
                purpose="",
                objectives=[],
                reporting="",
                risks="",
            )
        actions = [e.action for e in self.registry.audit_log()]
        self.assertIn("request_agent", actions)

    def test_proposal_alone_creates_no_agent(self):
        request = self.registry.request_agent(
            requested_by="chairman",
            name="pending-agent",
            level=Level.OPERATOR,
            tools=[Tool.FINANCE],
            max_classification=Classification.INTERNAL,
            **COMPLETE,
        )
        self.assertEqual(request.status, RequestStatus.PENDING)
        self.assertIsNone(self.store.get_agent_by_name("pending-agent"))

    def test_approval_brings_agent_into_existence(self):
        request = self.registry.request_agent(
            requested_by="chairman",
            name="finance-analyst",
            level=Level.OPERATOR,
            tools=[Tool.FINANCE, Tool.DATA_ANALYSIS],
            max_classification=Classification.CONFIDENTIAL,
            **COMPLETE,
        )
        agent = self.registry.approve_request(request.request_id, approver="chairman")
        self.assertEqual(agent.status, AgentStatus.ACTIVE)
        self.assertEqual(agent.parent_id, self.chairman.agent_id)
        self.assertIsNotNone(self.store.get_agent_by_name("finance-analyst"))

    def test_rejection_requires_a_reason(self):
        request = self.registry.request_agent(
            requested_by="chairman", name="doomed", level=Level.OPERATOR,
            tools=[Tool.FINANCE], max_classification=Classification.INTERNAL, **COMPLETE,
        )
        with self.assertRaises(IncompleteRequest):
            self.registry.reject_request(request.request_id, "chairman", reason="")

    def test_rejected_request_cannot_be_approved(self):
        request = self.registry.request_agent(
            requested_by="chairman", name="doomed", level=Level.OPERATOR,
            tools=[Tool.FINANCE], max_classification=Classification.INTERNAL, **COMPLETE,
        )
        self.registry.reject_request(request.request_id, "chairman", reason="not needed")
        with self.assertRaises(StateError):
            self.registry.approve_request(request.request_id, approver="chairman")

    def test_duplicate_names_refused(self):
        self.make("analyst")
        with self.assertRaises(StateError):
            self.registry.request_agent(
                requested_by="chairman", name="analyst", level=Level.OPERATOR,
                tools=[Tool.FINANCE], max_classification=Classification.INTERNAL,
                **COMPLETE,
            )


class TestDelegationLimits(RegistryTestCase):
    def test_child_cannot_receive_tools_parent_lacks(self):
        division = self.make("division-chair", tools=(Tool.FINANCE,))
        with self.assertRaises(PermissionDenied) as ctx:
            self.registry.request_agent(
                requested_by="division-chair",
                name="rogue",
                level=Level.OPERATOR,
                tools=[Tool.FINANCE, Tool.SECURITY],
                max_classification=Classification.INTERNAL,
                **COMPLETE,
            )
        self.assertIn("security", str(ctx.exception))

    def test_child_cannot_outrank_parent(self):
        self.make("division-chair", level=Level.EXECUTIVE)
        with self.assertRaises(PermissionDenied):
            self.registry.request_agent(
                requested_by="division-chair",
                name="rogue",
                level=Level.EXECUTIVE,
                tools=[Tool.FINANCE],
                max_classification=Classification.INTERNAL,
                **COMPLETE,
            )

    def test_approval_revalidates_after_parent_suspension(self):
        """A proposal filed while healthy must not sail through afterwards."""
        self.make("division-chair", level=Level.EXECUTIVE)
        request = self.registry.request_agent(
            requested_by="division-chair",
            name="late-hire",
            level=Level.OPERATOR,
            tools=[Tool.FINANCE],
            max_classification=Classification.INTERNAL,
            **COMPLETE,
        )
        self.registry.suspend("division-chair", by="chairman", reason="under review")

        with self.assertRaises(PermissionDenied) as ctx:
            self.registry.approve_request(request.request_id, approver="chairman")
        self.assertIn("conditions changed", str(ctx.exception))

    def test_terminated_reports_free_a_slot(self):
        parent = self.make("manager", level=Level.INTERNAL, tools=(Tool.FINANCE,),
                           classification=Classification.INTERNAL)
        # Level 2 permits 5 reports.
        for i in range(5):
            self.make(f"worker-{i}", level=Level.READ_ONLY, tools=(Tool.FINANCE,),
                      classification=Classification.PUBLIC, parent="manager")

        with self.assertRaises(PermissionDenied):
            self.registry.request_agent(
                requested_by="manager", name="worker-6", level=Level.READ_ONLY,
                tools=[Tool.FINANCE], max_classification=Classification.PUBLIC,
                **COMPLETE,
            )

        self.registry.terminate("worker-0", by="chairman", reason="redundant")
        request = self.registry.request_agent(
            requested_by="manager", name="worker-6", level=Level.READ_ONLY,
            tools=[Tool.FINANCE], max_classification=Classification.PUBLIC, **COMPLETE,
        )
        self.assertEqual(request.status, RequestStatus.PENDING)


class TestLifecycle(RegistryTestCase):
    def test_suspended_agent_cannot_act(self):
        self.make("analyst", level=Level.OPERATOR)
        self.registry.suspend("analyst", by="chairman", reason="policy breach")
        decision = self.registry.authorize(
            "analyst", Tool.FINANCE, Classification.INTERNAL
        )
        self.assertFalse(decision.allowed)

    def test_reinstated_agent_can_act_again(self):
        self.make("analyst", level=Level.OPERATOR)
        self.registry.suspend("analyst", by="chairman", reason="policy breach")
        self.registry.reinstate("analyst", by="chairman", reason="cleared")
        decision = self.registry.authorize(
            "analyst", Tool.FINANCE, Classification.INTERNAL
        )
        self.assertTrue(decision.allowed, decision.reason)

    def test_chairman_cannot_be_terminated(self):
        with self.assertRaises(PermissionDenied):
            self.registry.terminate("chairman", by="chairman", reason="nope")

    def test_termination_cascades_to_descendants(self):
        self.make("division-chair", level=Level.EXECUTIVE)
        self.make("manager", level=Level.CROSS_AGENT, parent="division-chair")
        self.make("worker", level=Level.OPERATOR, parent="manager")

        terminated = self.registry.terminate(
            "division-chair", by="chairman", reason="division dissolved"
        )
        names = {a.name for a in terminated}
        self.assertEqual(names, {"division-chair", "manager", "worker"})
        for name in names:
            self.assertEqual(
                self.store.get_agent_by_name(name).status, AgentStatus.TERMINATED
            )

    def test_peer_cannot_terminate_peer(self):
        self.make("chair-a", level=Level.EXECUTIVE)
        self.make("chair-b", level=Level.EXECUTIVE)
        with self.assertRaises(PermissionDenied):
            self.registry.terminate("chair-b", by="chair-a", reason="rivalry")

    def test_termination_requires_a_reason(self):
        """The reason check fires before the authority check, by design:
        an unexplained termination is malformed regardless of who sent it."""
        self.make("analyst")
        with self.assertRaises(IncompleteRequest):
            self.registry.terminate("analyst", by="chairman", reason="   ")

    def test_agent_cannot_terminate_itself(self):
        self.make("analyst", level=Level.OPERATOR)
        with self.assertRaises(PermissionDenied):
            self.registry.terminate("analyst", by="analyst", reason="quitting")

    def test_unknown_agent_raises_not_found(self):
        with self.assertRaises(NotFound):
            self.registry.require_agent("ghost")


class TestTasks(RegistryTestCase):
    def test_cannot_assign_work_the_assignee_lacks_tools_for(self):
        self.make("analyst", level=Level.OPERATOR, tools=(Tool.FINANCE,))
        with self.assertRaises(PermissionDenied) as ctx:
            self.registry.assign_task(
                title="Run a penetration test",
                assigned_by="chairman",
                assigned_to="analyst",
                tool=Tool.SECURITY,
                classification=Classification.INTERNAL,
            )
        self.assertIn("not granted", str(ctx.exception))

    def test_cannot_assign_above_assignee_clearance(self):
        self.make("analyst", level=Level.OPERATOR, tools=(Tool.FINANCE,),
                  classification=Classification.INTERNAL)
        with self.assertRaises(PermissionDenied):
            self.registry.assign_task(
                title="Review restricted ledger",
                assigned_by="chairman",
                assigned_to="analyst",
                tool=Tool.FINANCE,
                classification=Classification.RESTRICTED,
            )

    def test_valid_assignment_succeeds_and_is_audited(self):
        self.make("analyst", level=Level.OPERATOR, tools=(Tool.FINANCE,))
        task = self.registry.assign_task(
            title="Daily ledger review",
            assigned_by="chairman",
            assigned_to="analyst",
            tool=Tool.FINANCE,
            classification=Classification.CONFIDENTIAL,
        )
        self.assertEqual(task.title, "Daily ledger review")
        actions = [e.action for e in self.registry.audit_log()]
        self.assertIn("assign_task", actions)

    def test_open_escalations_surface_urgent_unfinished_work(self):
        from chairman import Escalation, TaskStatus

        self.make("analyst", level=Level.OPERATOR, tools=(Tool.FINANCE,))
        task = self.registry.assign_task(
            title="Ledger discrepancy",
            assigned_by="chairman",
            assigned_to="analyst",
            tool=Tool.FINANCE,
            classification=Classification.CONFIDENTIAL,
        )
        self.registry.update_task(
            task.task_id, by="analyst", escalation=Escalation.IMMEDIATE,
            note="Numbers do not reconcile",
        )
        self.assertEqual(len(self.registry.open_escalations()), 1)

        self.registry.update_task(task.task_id, by="analyst", status=TaskStatus.DONE)
        self.assertEqual(len(self.registry.open_escalations()), 0)


class TestAuditIntegration(RegistryTestCase):
    def test_denied_authorization_is_recorded(self):
        self.make("analyst", level=Level.OPERATOR, tools=(Tool.FINANCE,))
        self.registry.authorize("analyst", Tool.SECURITY, Classification.PUBLIC)
        denied = [e for e in self.registry.audit_log() if e.outcome == "denied"]
        self.assertTrue(denied)

    def test_full_lifecycle_leaves_a_verifiable_chain(self):
        self.make("division-chair", level=Level.EXECUTIVE)
        self.make("analyst", level=Level.OPERATOR, parent="division-chair")
        self.registry.assign_task(
            title="Quarterly close", assigned_by="division-chair",
            assigned_to="analyst", tool=Tool.FINANCE,
            classification=Classification.CONFIDENTIAL,
        )
        self.registry.suspend("analyst", by="chairman", reason="audit hold")
        self.registry.terminate("division-chair", by="chairman", reason="restructure")

        ok, problems = self.registry.verify_audit()
        self.assertTrue(ok, problems)

    def test_org_chart_reports_depth(self):
        self.make("division-chair", level=Level.EXECUTIVE)
        self.make("analyst", level=Level.OPERATOR, parent="division-chair")
        chart = {agent.name: depth for depth, agent in self.registry.org_chart()}
        self.assertEqual(chart["chairman"], 0)
        self.assertEqual(chart["division-chair"], 1)
        self.assertEqual(chart["analyst"], 2)


if __name__ == "__main__":
    unittest.main()
