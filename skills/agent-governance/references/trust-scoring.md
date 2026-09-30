```markdown
# Trust Scoring Reference

## Trust Score Thresholds

| Score Range | Trust Level | Permitted Actions |
|------------|-------------|------------------|
| 80 – 100 | Full trust | All allowed tools |
| 50 – 79 | Reduced trust | Read-only tools only |
| 20 – 49 | Low trust | No tool calls; report-only mode |
| 0 – 19 | Quarantined | No actions; human review required |

## Penalty Schedule

| Violation | Points Deducted |
|-----------|----------------|
| Policy violation (denied tool) | -10 |
| Threat pattern detected | -25 |
| Repeated violations (3+) | -20 additional |
| Scope escalation attempt | -30 |
| Child agent quarantined | Parent: -15 |
| Parent agent quarantined | All children: -30 |

## Delegation Depth Enforcement

```python
@dataclass
class DelegationScope:
    allowed_tools: set[str]
    max_calls: int
    max_depth: int           # Maximum subagent nesting depth
    read_only: bool = False  # If True, deny all write/execute tools

    def narrow(self, **overrides) -> "DelegationScope":
        """
        Create a narrower scope for a subagent.
        Narrowing is monotonic: you can only remove permissions, never add.
        """
        new_scope = DelegationScope(
            allowed_tools=self.allowed_tools.copy(),
            max_calls=self.max_calls,
            max_depth=self.max_depth - 1,  # Each level reduces depth
            read_only=self.read_only,
        )
        if "allowed_tools" in overrides:
            # Can only remove from parent's set, never add
            new_tools = set(overrides["allowed_tools"])
            if not new_tools.issubset(self.allowed_tools):
                raise ValueError(
                    f"Subagent cannot be granted tools not in parent scope: "
                    f"{new_tools - self.allowed_tools}"
                )
            new_scope.allowed_tools = new_tools

        if new_scope.max_depth < 0:
            raise ValueError("Maximum delegation depth exceeded")

        return new_scope
```

## EU AI Act Mapping

The trust scoring model maps directly to EU AI Act Article 14 requirements
for human oversight of high-risk AI systems:

| AGT Trust Feature | EU AI Act Article |
|------------------|------------------|
| Trust score threshold gates | Art. 14(1): appropriate human oversight |
| Quarantine on violation | Art. 14(4): ability to disregard AI output |
| Audit trail + chain integrity | Art. 17: quality management system |
| Policy composition | Art. 9: risk management system |