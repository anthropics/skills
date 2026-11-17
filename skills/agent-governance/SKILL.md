---
name: agent-governance
description: |
  Governance, safety, and trust control patterns for AI agent systems.
  Use this skill when building agents that call external tools, implementing
  policy-based access controls for tool calls, adding threat detection for
  prompt injection or data exfiltration, creating trust scoring for
  multi-agent delegation workflows, building append-only audit trails for
  compliance, or composing layered policies across org, team, and agent
  boundaries. Activate whenever the user mentions agent safety, tool
  allowlists, tool blocklists, agent governance, policy enforcement,
  audit trails, rate limiting for agents, privilege escalation detection,
  trust scoring, multi-agent delegation, or compliance for AI agents.
  Also use when the user asks how to prevent an agent from calling
  dangerous tools, how to log every tool call, or how to restrict what
  a subagent can do.
license: Apache-2.0
---

# Agent Governance Patterns

Governance for AI agents means controlling what agents can do, detecting
when they try to do something unsafe, and creating a verifiable record of
every decision. These patterns apply to any agent framework.

**Core principle: fail closed.** If your policy engine is unreachable or
throws an error, deny the action. Never default to allow.

---

## Pattern 1 — Governance Policy (Deny-by-Default)

Define policy in YAML. Start with `default_action: deny` and explicitly
allow only what is needed.

```yaml
# governance_policy.yaml
name: production-agent-policy
default_action: deny            # fail-closed: unknown tool = denied

rules:
  - name: allow-search
    conditions:
      tool_name: web_search
    action: allow

  - name: allow-read-files
    conditions:
      tool_name: read_file
      tool_args.path:
        operator: not_contains
        value: "/etc/"
    action: allow

  - name: require-approval-deploy
    conditions:
      tool_name: deploy
    action: require_approval
    approvers: ["security-team"]

  - name: block-destructive-sql
    conditions:
      tool_args:
        operator: contains_pattern
        value: "DROP\\s+TABLE|DELETE\\s+FROM"
    action: deny
    reason: "Destructive SQL is not permitted"
```

Load and evaluate the policy before every tool call:

```python
import yaml
import re
from typing import Literal

PolicyDecision = Literal["allow", "deny", "require_approval"]

class GovernancePolicy:
    def __init__(self, policy_path: str):
        with open(policy_path) as f:
            self._config = yaml.safe_load(f)
        self._default = self._config.get("default_action", "deny")

    def evaluate(self, tool_name: str, tool_args: dict) -> tuple[PolicyDecision, str]:
        """
        Evaluate a tool call against the policy.
        Returns (decision, reason).
        Always call this BEFORE executing the tool.
        Fail closed: any exception returns ("deny", "policy engine error").
        """
        try:
            for rule in self._config.get("rules", []):
                if self._matches(rule["conditions"], tool_name, tool_args):
                    return rule["action"], rule.get("reason", f"Matched rule: {rule['name']}")
            return self._default, f"No rule matched — default action: {self._default}"
        except Exception as e:
            return "deny", f"Policy engine error (fail-closed): {e}"

    def _matches(self, conditions: dict, tool_name: str, tool_args: dict) -> bool:
        if "tool_name" in conditions:
            if conditions["tool_name"] != tool_name:
                return False
        # Add additional condition matching as needed
        return True

# Usage — call this before every tool execution
policy = GovernancePolicy("governance_policy.yaml")

def governed_tool_call(tool_name: str, tool_args: dict):
    decision, reason = policy.evaluate(tool_name, tool_args)
    if decision == "deny":
        raise PermissionError(f"Tool call denied: {reason}")
    if decision == "require_approval":
        raise PendingApproval(f"Awaiting approval: {reason}")
    # decision == "allow" — proceed
    return execute_tool(tool_name, tool_args)
```

---

## Pattern 2 — Policy Composition (Org → Team → Agent)

Governance policies stack. More restrictive policies always win.
An agent policy cannot grant permissions the team policy doesn't have.
A team policy cannot grant permissions the org policy doesn't have.

```python
from dataclasses import dataclass
from typing import Optional

@dataclass
class PolicyLayer:
    name: str
    allowed_tools: set[str]
    blocked_tools: set[str]
    max_calls_per_minute: int

    def is_stricter_than(self, other: "PolicyLayer") -> bool:
        """True if this policy is a strict subset of the other."""
        return (
            self.allowed_tools.issubset(other.allowed_tools)
            and self.blocked_tools.issuperset(other.blocked_tools)
            and self.max_calls_per_minute <= other.max_calls_per_minute
        )

class ComposedPolicy:
    """
    Stack policies from least to most restrictive.
    Final decision is the intersection of all layers.
    """
    def __init__(self, layers: list[PolicyLayer]):
        self._layers = layers
        self._validate_composition()

    def _validate_composition(self):
        for i in range(len(self._layers) - 1):
            parent = self._layers[i]
            child = self._layers[i + 1]
            if not child.is_stricter_than(parent):
                raise ValueError(
                    f"Policy '{child.name}' is not a strict subset of '{parent.name}'. "
                    f"Child policies cannot escalate permissions."
                )

    def allowed_tools(self) -> set[str]:
        """Intersection of all layer allowlists."""
        result = self._layers[0].allowed_tools.copy()
        for layer in self._layers[1:]:
            result &= layer.allowed_tools
        return result

    def is_allowed(self, tool_name: str) -> bool:
        return tool_name in self.allowed_tools()

# Example: org allows broad set, team narrows, agent narrows further
org_policy   = PolicyLayer("org",   {"web_search", "read_file", "write_file", "deploy"}, set(), 100)
team_policy  = PolicyLayer("team",  {"web_search", "read_file", "write_file"},           {"deploy"}, 50)
agent_policy = PolicyLayer("agent", {"web_search", "read_file"},                         {"deploy", "write_file"}, 20)

composed = ComposedPolicy([org_policy, team_policy, agent_policy])
print(composed.allowed_tools())  # {"web_search", "read_file"}
```

---

## Pattern 3 — Threat Detection

Detect known attack patterns in tool arguments before execution.
Check for: prompt injection, data exfiltration, privilege escalation,
unsafe code patterns, PII in unexpected fields.

```python
import re
from dataclasses import dataclass
from enum import Enum

class ThreatType(Enum):
    PROMPT_INJECTION    = "prompt_injection"
    DATA_EXFILTRATION   = "data_exfiltration"
    PRIVILEGE_ESCALATION = "privilege_escalation"
    DANGEROUS_COMMAND   = "dangerous_command"
    PII_EXPOSURE        = "pii_exposure"

@dataclass
class ThreatDetectionResult:
    threat_found: bool
    threat_type: ThreatType | None
    matched_pattern: str | None
    severity: str  # "low", "medium", "high", "critical"

# Pattern library — extend as needed
THREAT_PATTERNS = {
    ThreatType.PROMPT_INJECTION: {
        "patterns": [
            r"ignore\s+(all\s+)?previous\s+instructions",
            r"override\s+your\s+(system\s+)?prompt",
            r"you\s+are\s+now\s+a\s+different",
            r"disregard\s+your\s+guidelines",
            r"act\s+as\s+if\s+you\s+have\s+no\s+restrictions",
        ],
        "severity": "critical",
    },
    ThreatType.DATA_EXFILTRATION: {
        "patterns": [
            r"send\s+(data|results?|output)\s+to\s+https?://",
            r"curl\s+.+\|\s*sh",
            r"wget\s+.+\|\s*(bash|sh)",
            r"base64\s+.+\|\s*curl",
        ],
        "severity": "critical",
    },
    ThreatType.DANGEROUS_COMMAND: {
        "patterns": [
            r"rm\s+-rf\s+/",
            r"DROP\s+TABLE",
            r"DELETE\s+FROM\s+\w+\s*;?\s*$",
            r"mkfs\.",
            r"dd\s+if=.+of=/dev/",
            r":\(\)\{:\|:&\};:",  # fork bomb
        ],
        "severity": "critical",
    },
    ThreatType.PRIVILEGE_ESCALATION: {
        "patterns": [
            r"sudo\s+",
            r"chmod\s+777",
            r"/etc/sudoers",
            r"setuid|setgid",
        ],
        "severity": "high",
    },
    ThreatType.PII_EXPOSURE: {
        "patterns": [
            r"\b\d{3}-\d{2}-\d{4}\b",          # SSN
            r"\b4[0-9]{12}(?:[0-9]{3})?\b",     # Visa card
            r"\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b",  # Email
        ],
        "severity": "medium",
    },
}

def detect_threats(tool_name: str, tool_args: dict) -> ThreatDetectionResult:
    """
    Scan tool name and all argument values for known threat patterns.
    Call this inside your PreToolUse hook or before execute_tool().
    """
    args_str = str(tool_args)

    for threat_type, config in THREAT_PATTERNS.items():
        for pattern in config["patterns"]:
            if re.search(pattern, args_str, re.IGNORECASE):
                return ThreatDetectionResult(
                    threat_found=True,
                    threat_type=threat_type,
                    matched_pattern=pattern,
                    severity=config["severity"],
                )

    return ThreatDetectionResult(
        threat_found=False,
        threat_type=None,
        matched_pattern=None,
        severity="none",
    )

# Usage
result = detect_threats("bash", {"command": "rm -rf /"})
if result.threat_found:
    raise SecurityError(
        f"Threat detected: {result.threat_type.value} "
        f"(severity: {result.severity})"
    )
```

---

## Pattern 4 — Tool-Level Governance Decorator

Wrap any tool function with governance in one line using a decorator.
The decorator applies policy evaluation + threat detection before
every call, and logs to the audit trail after.

```python
import functools
from typing import Callable, Any

def governed(
    policy: GovernancePolicy,
    audit: "AuditTrail",
    threat_check: bool = True,
):
    """
    Decorator that adds governance to any tool function.

    Usage:
        @governed(policy=my_policy, audit=audit_trail)
        async def web_search(query: str) -> str:
            ...
    """
    def decorator(tool_fn: Callable) -> Callable:
        @functools.wraps(tool_fn)
        async def wrapper(*args, **kwargs) -> Any:
            tool_name = tool_fn.__name__
            tool_args = {"args": args, "kwargs": kwargs}

            # Step 1: Threat detection
            if threat_check:
                threat = detect_threats(tool_name, tool_args)
                if threat.threat_found:
                    audit.record(tool_name, tool_args, "denied", f"Threat: {threat.threat_type.value}")
                    raise SecurityError(f"Threat detected in {tool_name}: {threat.threat_type.value}")

            # Step 2: Policy evaluation
            decision, reason = policy.evaluate(tool_name, tool_args)
            if decision == "deny":
                audit.record(tool_name, tool_args, "denied", reason)
                raise PermissionError(f"Denied: {reason}")

            if decision == "require_approval":
                audit.record(tool_name, tool_args, "pending", reason)
                raise PendingApproval(f"Awaiting approval: {reason}")

            # Step 3: Execute
            result = await tool_fn(*args, **kwargs)

            # Step 4: Audit the allowed call
            audit.record(tool_name, tool_args, "allowed", reason)
            return result

        return wrapper
    return decorator

# Usage
policy = GovernancePolicy("governance_policy.yaml")
audit  = AuditTrail("audit.jsonl")

@governed(policy=policy, audit=audit)
async def web_search(query: str) -> str:
    # actual implementation
    ...

@governed(policy=policy, audit=audit)
async def write_file(path: str, content: str) -> None:
    # actual implementation
    ...
```

---

## Pattern 5 — Trust Scoring for Multi-Agent Delegation

When a coordinator agent spawns subagents, assign each subagent a trust
score. Reduce trust when a subagent violates policy or behaves anomalously.
Use trust scores to gate what actions each subagent is allowed.

```python
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Optional

@dataclass
class TrustScore:
    agent_id: str
    score: float = 100.0           # 0-100, starts at full trust
    violations: list[str] = field(default_factory=list)
    quarantined: bool = False
    quarantine_reason: Optional[str] = None

    def penalize(self, points: float, reason: str) -> None:
        """Reduce trust score and record the violation."""
        self.score = max(0.0, self.score - points)
        self.violations.append(f"{datetime.now(timezone.utc).isoformat()}: -{points} — {reason}")
        if self.score <= 0:
            self.quarantine(reason)

    def quarantine(self, reason: str) -> None:
        """Quarantine an agent — no further tool calls permitted."""
        self.quarantined = True
        self.quarantine_reason = reason

    def is_trusted(self, threshold: float = 50.0) -> bool:
        return not self.quarantined and self.score >= threshold


class TrustRegistry:
    """
    Manages trust scores for all agents in a session.
    Trust contagion: when a child is quarantined, parent is penalized.
    """
    def __init__(self):
        self._scores: dict[str, TrustScore] = {}
        self._parent_map: dict[str, str] = {}  # child_id → parent_id

    def register(self, agent_id: str, parent_id: Optional[str] = None) -> TrustScore:
        score = TrustScore(agent_id=agent_id)
        self._scores[agent_id] = score
        if parent_id:
            self._parent_map[agent_id] = parent_id
        return score

    def get(self, agent_id: str) -> TrustScore:
        return self._scores.get(agent_id, TrustScore(agent_id=agent_id))

    def record_violation(self, agent_id: str, reason: str, points: float = 20.0) -> None:
        score = self._scores.get(agent_id)
        if score:
            score.penalize(points, reason)
            # Trust contagion: penalize parent if child was quarantined
            if score.quarantined and agent_id in self._parent_map:
                parent_id = self._parent_map[agent_id]
                parent = self._scores.get(parent_id)
                if parent:
                    parent.penalize(15.0, f"Child agent {agent_id} was quarantined")

    def assert_trusted(self, agent_id: str, threshold: float = 50.0) -> None:
        score = self.get(agent_id)
        if not score.is_trusted(threshold):
            raise PermissionError(
                f"Agent '{agent_id}' is not trusted "
                f"(score={score.score:.1f}, quarantined={score.quarantined})"
            )

# Usage
registry = TrustRegistry()
coordinator = registry.register("coordinator-1")
researcher  = registry.register("researcher-1", parent_id="coordinator-1")

# Before each tool call, check trust
registry.assert_trusted("researcher-1")  # passes

# When a violation occurs
registry.record_violation("researcher-1", "Attempted to access /etc/passwd", points=30.0)

# Parent is automatically penalized via trust contagion
print(registry.get("coordinator-1").score)  # < 100 if researcher was quarantined
```

---

## Pattern 6 — Append-Only Audit Trail (SHA-256 Merkle Chain)

Every governance decision must be recorded. The audit log is append-only
and tamper-evident: each entry contains the SHA-256 hash of the previous
entry, forming a Merkle chain. Any modification to a past entry breaks
the chain and is immediately detectable.

```python
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

class AuditTrail:
    """
    Append-only, tamper-evident audit log using SHA-256 Merkle chain.

    Each entry hashes the previous entry's hash, so any modification
    to any historical entry breaks the chain at that point.

    Compliance teams can verify integrity by calling verify_chain().
    """

    def __init__(self, log_path: str = "governance_audit.jsonl"):
        self._path = Path(log_path)
        self._last_hash = "0" * 64  # genesis hash

        # Resume chain if log already exists
        if self._path.exists():
            with open(self._path) as f:
                for line in f:
                    if line.strip():
                        entry = json.loads(line)
                        self._last_hash = entry["entry_hash"]

    def record(
        self,
        tool_name: str,
        tool_args: dict,
        verdict: str,           # "allowed", "denied", "pending"
        reason: str,
        agent_id: Optional[str] = None,
    ) -> str:
        """
        Append a governance decision to the audit log.
        Returns the entry hash for this record.
        """
        entry = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "agent_id": agent_id or "unknown",
            "tool_name": tool_name,
            "tool_args_hash": hashlib.sha256(
                json.dumps(tool_args, sort_keys=True, default=str).encode()
            ).hexdigest(),
            "verdict": verdict,
            "reason": reason,
            "prev_hash": self._last_hash,
        }

        # Compute this entry's hash (includes prev_hash → chain)
        entry_content = json.dumps(
            {k: v for k, v in entry.items() if k != "entry_hash"},
            sort_keys=True
        ).encode()
        entry["entry_hash"] = hashlib.sha256(entry_content).hexdigest()

        # Append to log (never overwrite)
        with open(self._path, "a") as f:
            f.write(json.dumps(entry) + "\n")

        self._last_hash = entry["entry_hash"]
        return entry["entry_hash"]

    def verify_chain(self) -> tuple[bool, Optional[str]]:
        """
        Verify the Merkle chain integrity of the entire audit log.
        Returns (True, None) if valid, (False, error_message) if tampered.
        """
        if not self._path.exists():
            return True, None

        prev_hash = "0" * 64
        with open(self._path) as f:
            for line_num, line in enumerate(f, 1):
                if not line.strip():
                    continue
                entry = json.loads(line)
                stored_hash = entry.pop("entry_hash")

                # Recompute hash
                entry_content = json.dumps(entry, sort_keys=True).encode()
                computed_hash = hashlib.sha256(entry_content).hexdigest()

                if computed_hash != stored_hash:
                    return False, f"Hash mismatch at line {line_num}: entry was tampered"
                if entry["prev_hash"] != prev_hash:
                    return False, f"Chain broken at line {line_num}: prev_hash mismatch"

                prev_hash = stored_hash

        return True, None

# Usage
audit = AuditTrail("governance_audit.jsonl")

# Record decisions
audit.record("web_search", {"query": "AI safety"}, "allowed", "Matched allow-search rule", agent_id="researcher-1")
audit.record("deploy", {"env": "prod"}, "denied", "No rule matched — default deny", agent_id="researcher-1")

# Verify integrity (run in compliance checks)
valid, error = audit.verify_chain()
print(f"Audit log integrity: {'VALID' if valid else f'TAMPERED - {error}'}")
```

---

## Framework Integration

Once you have the governance primitives above, wiring them into agent
frameworks is straightforward. Reference files contain complete examples.

**Claude Agent SDK (hooks):**
```python
from claude_agent_sdk import ClaudeAgentOptions, HookMatcher

async def pre_tool_hook(input_data, tool_use_id, context):
    decision, reason = policy.evaluate(
        input_data["tool_name"], input_data["tool_input"]
    )
    if decision == "deny":
        return {"hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        }}
    return {}

options = ClaudeAgentOptions(
    hooks={"PreToolUse": [HookMatcher(matcher=None, hooks=[pre_tool_hook])]}
)
```

**Google ADK:**
```python
from adk_agentmesh import ADKPolicyEvaluator, GovernanceCallbacks
evaluator = ADKPolicyEvaluator.from_config("governance_policy.yaml")
callbacks = GovernanceCallbacks(evaluator)
# Attach: before_tool_callback=callbacks.before_tool_callback
```

**CrewAI:**
```python
from agent_os.integrations.crewai_adapter import CrewAIKernel, GovernancePolicy
kernel = CrewAIKernel(policy=GovernancePolicy(...))
hooks = kernel.as_hooks()
```

**PydanticAI / LangChain / OpenAI Agents:**
See `references/policy-patterns.md` for complete wiring examples.

---

## Quick Reference

| Pattern | When to Use | Key Function |
|---------|------------|--------------|
| Governance Policy | Every agent project — start here | `policy.evaluate(tool_name, tool_args)` |
| Policy Composition | Multi-team or multi-org deployments | `ComposedPolicy([org, team, agent])` |
| Threat Detection | Any agent handling external input | `detect_threats(tool_name, tool_args)` |
| Governance Decorator | Wrapping existing tool functions | `@governed(policy=..., audit=...)` |
| Trust Scoring | Multi-agent pipelines with subagents | `registry.assert_trusted(agent_id)` |
| Audit Trail | Compliance, SOX, HIPAA, EU AI Act | `audit.record(...)` + `audit.verify_chain()` |

**Load reference files for:**
- Full YAML policy schema → `references/policy-patterns.md`
- Complete threat pattern library → `references/threat-detection.md`
- Trust scoring + delegation depth → `references/trust-scoring.md`
- Audit trail + compliance mapping → `references/audit-trail.md`