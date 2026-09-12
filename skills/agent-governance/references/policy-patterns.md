```yaml
# governance_policy.yaml — complete schema
name: string                    # Policy name (required)
version: "1.0"                  # Semantic version (optional)
default_action: deny            # "allow" | "deny" | "require_approval"

rules:
  - name: string                # Rule identifier (required)
    conditions:
      tool_name: string         # Exact match OR regex if wrapped in /pattern/
      tool_args:
        field_path: string      # Dot-notation path into tool_args dict
        operator: string        # "eq", "not_eq", "contains", "not_contains",
                                # "contains_pattern", "in", "not_in"
        value: any              # Value to compare against
    action: string              # "allow" | "deny" | "require_approval"
    reason: string              # Human-readable reason (optional)
    approvers: [string]         # Required when action is "require_approval"
    priority: integer           # Lower = evaluated first (default: 100)
```

## PydanticAI Integration

```python
from pydantic_ai import Agent
from pydantic_ai.tools import Tool

policy = GovernancePolicy("governance_policy.yaml")
audit  = AuditTrail("audit.jsonl")

def make_governed_tool(tool_fn):
    async def wrapper(**kwargs):
        decision, reason = policy.evaluate(tool_fn.__name__, kwargs)
        if decision != "allow":
            audit.record(tool_fn.__name__, kwargs, decision, reason)
            raise ValueError(f"Tool {tool_fn.__name__} {decision}: {reason}")
        result = await tool_fn(**kwargs)
        audit.record(tool_fn.__name__, kwargs, "allowed", reason)
        return result
    wrapper.__name__ = tool_fn.__name__
    return Tool(wrapper)

agent = Agent(
    model="claude-opus-4-6",
    tools=[make_governed_tool(web_search), make_governed_tool(read_file)]
)
```

## LangChain Integration

```python
from langchain.tools import BaseTool

class GovernedTool(BaseTool):
    name: str
    description: str
    _policy: GovernancePolicy
    _audit: AuditTrail
    _inner_tool: BaseTool

    def _run(self, *args, **kwargs):
        decision, reason = self._policy.evaluate(self.name, kwargs)
        if decision == "deny":
            self._audit.record(self.name, kwargs, "denied", reason)
            raise PermissionError(f"Denied: {reason}")
        result = self._inner_tool._run(*args, **kwargs)
        self._audit.record(self.name, kwargs, "allowed", reason)
        return result
```

## OpenAI Agents SDK Integration

```python
from agents import function_tool

def governed_function_tool(policy, audit):
    def decorator(fn):
        @function_tool
        async def wrapper(**kwargs):
            decision, reason = policy.evaluate(fn.__name__, kwargs)
            if decision != "allow":
                audit.record(fn.__name__, kwargs, decision, reason)
                raise PermissionError(f"{fn.__name__} {decision}: {reason}")
            result = await fn(**kwargs)
            audit.record(fn.__name__, kwargs, "allowed", reason)
            return result
        return wrapper
    return decorator