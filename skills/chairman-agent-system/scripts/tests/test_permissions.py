"""Rules tested directly against the pure functions, no database involved."""

from __future__ import annotations

import unittest

from chairman import (
    Agent,
    AgentStatus,
    Classification,
    Level,
    Tool,
    authorize_action,
    can_approve,
    can_create_subagent,
    effective_classification,
)


def make_agent(
    name="agent",
    level=Level.OPERATOR,
    tools=(Tool.DATA_ANALYSIS,),
    classification=Classification.CONFIDENTIAL,
    status=AgentStatus.ACTIVE,
) -> Agent:
    return Agent(
        agent_id=f"agent-{name}",
        name=name,
        level=level,
        tools=frozenset(tools),
        max_classification=classification,
        purpose="test fixture",
        status=status,
    )


class TestEffectiveClassification(unittest.TestCase):
    def test_level_cap_overrides_generous_charter(self):
        # A level 1 agent handed RESTRICTED in its charter is still capped
        # at PUBLIC by its level.
        agent = make_agent(level=Level.READ_ONLY, classification=Classification.RESTRICTED)
        self.assertEqual(effective_classification(agent), Classification.PUBLIC)

    def test_charter_overrides_generous_level(self):
        agent = make_agent(level=Level.EXECUTIVE, classification=Classification.INTERNAL)
        self.assertEqual(effective_classification(agent), Classification.INTERNAL)


class TestAuthorizeAction(unittest.TestCase):
    def test_allows_granted_tool_within_clearance(self):
        agent = make_agent(tools=(Tool.FINANCE,))
        decision = authorize_action(agent, Tool.FINANCE, Classification.INTERNAL)
        self.assertTrue(decision.allowed, decision.reason)

    def test_denies_ungranted_tool(self):
        agent = make_agent(tools=(Tool.FINANCE,))
        decision = authorize_action(agent, Tool.SECURITY, Classification.PUBLIC)
        self.assertFalse(decision.allowed)
        self.assertIn("not granted", decision.reason)

    def test_denies_classification_above_clearance(self):
        agent = make_agent(classification=Classification.INTERNAL)
        decision = authorize_action(
            agent, Tool.DATA_ANALYSIS, Classification.RESTRICTED
        )
        self.assertFalse(decision.allowed)
        self.assertIn("exceeds clearance", decision.reason)

    def test_denies_write_below_operator_level(self):
        agent = make_agent(level=Level.INTERNAL, classification=Classification.INTERNAL)
        read = authorize_action(agent, Tool.DATA_ANALYSIS, Classification.INTERNAL)
        write = authorize_action(
            agent, Tool.DATA_ANALYSIS, Classification.INTERNAL, write=True
        )
        self.assertTrue(read.allowed, read.reason)
        self.assertFalse(write.allowed)
        self.assertIn("write requires", write.reason)

    def test_denies_suspended_agent(self):
        agent = make_agent(status=AgentStatus.SUSPENDED)
        decision = authorize_action(agent, Tool.DATA_ANALYSIS, Classification.PUBLIC)
        self.assertFalse(decision.allowed)
        self.assertIn("suspended", decision.reason)

    def test_decision_is_truthy_in_boolean_context(self):
        agent = make_agent(tools=(Tool.FINANCE,))
        self.assertTrue(bool(authorize_action(agent, Tool.FINANCE, Classification.PUBLIC)))
        self.assertFalse(bool(authorize_action(agent, Tool.SECURITY, Classification.PUBLIC)))


class TestCanCreateSubagent(unittest.TestCase):
    def test_privilege_cannot_escalate_through_delegation(self):
        """The core invariant: a child may not out-rank its parent."""
        parent = make_agent(level=Level.OPERATOR)
        for child_level in (Level.OPERATOR, Level.CROSS_AGENT, Level.EXECUTIVE):
            with self.subTest(child_level=child_level):
                decision = can_create_subagent(
                    parent, child_level, [Tool.DATA_ANALYSIS], Classification.PUBLIC, 0
                )
                self.assertFalse(decision.allowed)
                self.assertIn("must be below", decision.reason)

    def test_cannot_grant_tools_parent_lacks(self):
        parent = make_agent(level=Level.EXECUTIVE, tools=(Tool.FINANCE,))
        decision = can_create_subagent(
            parent, Level.OPERATOR, [Tool.FINANCE, Tool.SECURITY], Classification.PUBLIC, 0
        )
        self.assertFalse(decision.allowed)
        self.assertIn("security", decision.reason)

    def test_cannot_grant_clearance_above_own(self):
        parent = make_agent(level=Level.EXECUTIVE, classification=Classification.INTERNAL)
        decision = can_create_subagent(
            parent,
            Level.OPERATOR,
            [Tool.DATA_ANALYSIS],
            Classification.RESTRICTED,
            0,
        )
        self.assertFalse(decision.allowed)
        self.assertIn("exceeds parent clearance", decision.reason)

    def test_level_one_cannot_delegate_at_all(self):
        parent = make_agent(level=Level.READ_ONLY)
        decision = can_create_subagent(
            parent, Level.READ_ONLY, [Tool.DATA_ANALYSIS], Classification.PUBLIC, 0
        )
        self.assertFalse(decision.allowed)
        self.assertIn("may not create", decision.reason)

    def test_span_of_control_limit_enforced(self):
        parent = make_agent(level=Level.OPERATOR)  # limit is 10
        ok = can_create_subagent(
            parent, Level.INTERNAL, [Tool.DATA_ANALYSIS], Classification.PUBLIC, 9
        )
        full = can_create_subagent(
            parent, Level.INTERNAL, [Tool.DATA_ANALYSIS], Classification.PUBLIC, 10
        )
        self.assertTrue(ok.allowed, ok.reason)
        self.assertFalse(full.allowed)
        self.assertIn("direct reports", full.reason)

    def test_requires_at_least_one_tool(self):
        parent = make_agent(level=Level.EXECUTIVE)
        decision = can_create_subagent(
            parent, Level.OPERATOR, [], Classification.PUBLIC, 0
        )
        self.assertFalse(decision.allowed)
        self.assertIn("at least one tool", decision.reason)

    def test_suspended_parent_cannot_create(self):
        parent = make_agent(level=Level.EXECUTIVE, status=AgentStatus.SUSPENDED)
        decision = can_create_subagent(
            parent, Level.OPERATOR, [Tool.DATA_ANALYSIS], Classification.PUBLIC, 0
        )
        self.assertFalse(decision.allowed)
        self.assertIn("suspended", decision.reason)

    def test_valid_delegation_is_allowed(self):
        parent = make_agent(
            level=Level.EXECUTIVE,
            tools=(Tool.FINANCE, Tool.DATA_ANALYSIS),
            classification=Classification.RESTRICTED,
        )
        decision = can_create_subagent(
            parent, Level.OPERATOR, [Tool.FINANCE], Classification.CONFIDENTIAL, 0
        )
        self.assertTrue(decision.allowed, decision.reason)


class TestCanApprove(unittest.TestCase):
    def test_chairman_approves_anything(self):
        chairman = make_agent(level=Level.CHAIRMAN)
        for level in Level:
            with self.subTest(level=level):
                self.assertTrue(can_approve(chairman, level).allowed)

    def test_operator_level_requires_executive_approver(self):
        manager = make_agent(level=Level.CROSS_AGENT)
        decision = can_approve(manager, Level.OPERATOR)
        self.assertFalse(decision.allowed)
        self.assertIn("executive", decision.reason)

    def test_executive_may_approve_operator(self):
        executive = make_agent(level=Level.EXECUTIVE)
        self.assertTrue(can_approve(executive, Level.OPERATOR).allowed)

    def test_approver_must_outrank_request(self):
        agent = make_agent(level=Level.INTERNAL)
        decision = can_approve(agent, Level.INTERNAL)
        self.assertFalse(decision.allowed)


if __name__ == "__main__":
    unittest.main()
