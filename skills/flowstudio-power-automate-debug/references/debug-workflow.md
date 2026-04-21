# FlowStudio MCP — Debug Workflow

End-to-end decision tree for diagnosing Power Automate flow failures.

---

## Top-Level Decision Tree

```
Flow is failing
│
├── Flow never starts / no runs appear
│   └── ► Check flow State: get_live_flow → properties.state
│       ├── "Stopped" → flow is disabled; enable in PA designer
│       └── "Started" + no runs → trigger condition not met (check trigger config)
│
├── Flow run shows "Failed"
│   ├── Step A: get_live_flow_run_error  → read error.code + error.message
│   │
│   ├── error.code = "InvalidTemplate"
│   │   └── ► Expression error (null value, wrong type, bad path)
│   │       └── See: Expression Error Workflow below
│   │
│   ├── error.code = "ConnectionAuthorizationFailed"
│   │   └── ► Connection owned by different user; fix in PA designer
│   │
│   ├── error.code = "ActionFailed" + message mentions HTTP
│   │   └── ► See: HTTP Action Workflow below
│   │
│   └── Unknown / generic error
│       └── ► Walk actions backwards (Step B below)
│
└── Flow Succeeds but output is wrong
    └── ► Inspect intermediate actions with get_live_flow_run_action_outputs
        └── See: Data Quality Workflow below
```

---

## Expression Error Workflow

```
InvalidTemplate error
│
├── 1. Read error.message — identifies the action name and function
│
├── 2. Get flow definition: get_live_flow
│   └── Find that action in definition["actions"][action_name]["inputs"]
│       └── Identify what upstream value the expression reads
│
├── 3. get_live_flow_run_action_outputs for the action BEFORE the failing one
│   └── Look for null / wrong type in that action's output
│       ├── Null string field → wrap with coalesce(): @coalesce(field, '')
│       ├── Null object → add empty check condition before the action
│       └── Wrong field name → correct the key (case-sensitive)
│
└── 4. Apply fix with update_live_flow, then resubmit
```

---

## HTTP Action Workflow

```
ActionFailed on HTTP action
│
├── 1. get_live_flow_run_action_outputs on the HTTP action
│   └── Read: outputs.statusCode, outputs.body
│
├── statusCode = 401
│   └── ► Auth header missing or expired OAuth token
│       Check: action inputs.authentication block
│
├── statusCode = 403
│   └── ► Insufficient permission on target resource
│       Check: service principal / user has access
│
├── statusCode = 400
│   └── ► Malformed request body
│       Check: action inputs.body expression; parse errors often in nested JSON
│
├── statusCode = 404
│   └── ► Wrong URL or resource deleted/renamed
│       Check: action inputs.uri expression
│
└── statusCode = 500 / timeout
    └── ► Target system error; retry policy may help
        Add: "retryPolicy": {"type": "Fixed", "count": 3, "interval": "PT10S"}
```

---

## Data Quality Workflow

```
Flow succeeds but output data is wrong
│
├── 1. Identify the first "wrong" output — which action produces it?
│
├── 2. get_live_flow_run_action_outputs on that action
│   └── Compare actual output body vs expected
│
├── Source array has nulls / unexpected values
│   ├── Check the trigger data — get_live_flow_run_action_outputs on trigger
│   └── Trace forward action by action until the value corrupts
│
├── Merge/union has wrong values
│   └── Check union argument order:
│       union(NEW, old) = new wins  ✓
│       union(OLD, new) = old wins  ← common bug
│
├── Foreach output missing items
│   ├── Check foreach condition — filter may be too strict
│   └── Check if parallel foreach caused race condition (add Sequential)
│
└── Date/time values wrong timezone
    └── Use convertTimeZone() — utcNow() is always UTC
```

---

## Walk-Back Analysis (Unknown Failure)

When the error message doesn't clearly name a root cause:

```python
# 1. Get all action names from definition
defn = mcp("get_live_flow", environmentName=ENV, flowName=FLOW_ID)
actions = list(defn["properties"]["definition"]["actions"].keys())

# 2. Check status of each action in the failed run
for action in actions:
    actions_out = mcp("get_live_flow_run_action_outputs",
        environmentName=ENV, flowName=FLOW_ID, runName=RUN_ID,
        actionName=action)
    # Returns an array of action objects
    item = actions_out[0] if actions_out else {}
    status = item.get("status", "unknown")
    print(f"{action}: {status}")

# 3. Find the boundary between Succeeded and Failed/Skipped
# The first Failed action is likely the root cause (unless skipped by design)
```

Actions inside Foreach / Condition branches may appear nested —
check the parent action first to confirm the branch ran at all.

---

## Post-Fix Verification Checklist

1. `update_live_flow` returns `error: null` — definition accepted  
2. `resubmit_live_flow_run` confirms new run started  
3. Wait for run completion (poll `get_live_flow_runs` every 15 s)  
4. Confirm new run `status = "Succeeded"`  
5. If flow has downstream consumers (child flows, emails, SharePoint writes),
   spot-check those too
