---
name: flowstudio-power-automate-debug
description: >-
  Debug failing Power Automate cloud flows using the FlowStudio MCP server.
  Load this skill when asked to: debug a flow, investigate a failed run, why is
  this flow failing, inspect action outputs, find the root cause of a flow error,
  fix a broken Power Automate flow, diagnose a timeout, trace a DynamicOperationRequestFailure,
  check connector auth errors, read error details from a run, or troubleshoot
  expression failures. Requires a FlowStudio MCP subscription — see https://mcp.flowstudio.app
metadata:
  openclaw:
    requires:
      env:
        - FLOWSTUDIO_MCP_TOKEN
    primaryEnv: FLOWSTUDIO_MCP_TOKEN
    homepage: https://mcp.flowstudio.app
---

# Power Automate Debugging with FlowStudio MCP

A step-by-step diagnostic process for investigating failing Power Automate
cloud flows through the FlowStudio MCP server.

**Prerequisite**: A FlowStudio MCP server must be reachable with a valid JWT.
See the `power-automate-mcp` skill for connection setup.  
Subscribe at https://mcp.flowstudio.app

---

## Source of Truth

> **Always call `tools/list` first** to confirm available tool names and their
> parameter schemas. Tool names and parameters may change between server versions.
> This skill covers response shapes, behavioral notes, and diagnostic patterns —
> things `tools/list` cannot tell you. If this document disagrees with `tools/list`
> or a real API response, the API wins.

---

## Python Helper

```python
import json, urllib.request

MCP_URL   = "https://mcp.flowstudio.app/mcp"
MCP_TOKEN = "<YOUR_JWT_TOKEN>"

def mcp(tool, **kwargs):
    payload = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "tools/call",
                          "params": {"name": tool, "arguments": kwargs}}).encode()
    req = urllib.request.Request(MCP_URL, data=payload,
        headers={"x-api-key": MCP_TOKEN, "Content-Type": "application/json",
                 "User-Agent": "FlowStudio-MCP/1.0"})
    try:
        resp = urllib.request.urlopen(req, timeout=120)
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"MCP HTTP {e.code}: {body[:200]}") from e
    raw = json.loads(resp.read())
    if "error" in raw:
        raise RuntimeError(f"MCP error: {json.dumps(raw['error'])}")
    return json.loads(raw["result"]["content"][0]["text"])

ENV = "<environment-id>"   # e.g. Default-xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx
```

---

## FlowStudio for Teams: Fast-Path Diagnosis (Skip Steps 2–4)

If you have a FlowStudio for Teams subscription, `get_store_flow_errors`
returns per-run failure data including action names and remediation hints
in a single call — no need to walk through live API steps.

```python
# Quick failure summary
summary = mcp("get_store_flow_summary", environmentName=ENV, flowName=FLOW_ID)
# {"totalRuns": 100, "failRuns": 10, "failRate": 0.1,
#  "averageDurationSeconds": 29.4, "maxDurationSeconds": 158.9,
#  "firstFailRunRemediation": "<hint or null>"}
print(f"Fail rate: {summary['failRate']:.0%} over {summary['totalRuns']} runs")

# Per-run error details (requires active monitoring to be configured)
errors = mcp("get_store_flow_errors", environmentName=ENV, flowName=FLOW_ID)
if errors:
    for r in errors[:3]:
        print(r["startTime"], "|", r.get("failedActions"), "|", r.get("remediationHint"))
    # If errors confirms the failing action → jump to Step 6 (apply fix)
else:
    # Store doesn't have run-level detail for this flow — use live tools (Steps 2–5)
    pass
```

For the full governance record (description, complexity, tier, connector list):
```python
record = mcp("get_store_flow", environmentName=ENV, flowName=FLOW_ID)
# {"displayName": "My Flow", "state": "Started",
#  "runPeriodTotal": 100, "runPeriodFailRate": 0.1, "runPeriodFails": 10,
#  "runPeriodDurationAverage": 29410.8,   ← milliseconds
#  "runError": "{\"code\": \"EACCES\", ...}",  ← JSON string, parse it
#  "description": "...", "tier": "Premium", "complexity": "{...}"}
if record.get("runError"):
    last_err = json.loads(record["runError"])
    print("Last run error:", last_err)
```

---

## Step 1 — Locate the Flow

```python
result = mcp("list_live_flows", environmentName=ENV)
# Returns a wrapper object: {mode, flows, totalCount, error}
target = next(f for f in result["flows"] if "My Flow Name" in f["displayName"])
FLOW_ID = target["id"]   # plain UUID — use directly as flowName
print(FLOW_ID)
```

---

## Step 2 — Find the Failing Run

```python
runs = mcp("get_live_flow_runs", environmentName=ENV, flowName=FLOW_ID, top=5)
# Returns direct array (newest first):
# [{"name": "08584296068667933411438594643CU15",
#   "status": "Failed",
#   "startTime": "2026-02-25T06:13:38.6910688Z",
#   "endTime": "2026-02-25T06:15:24.1995008Z",
#   "triggerName": "manual",
#   "error": {"code": "ActionFailed", "message": "An action failed..."}},
#  {"name": "...", "status": "Succeeded", "error": null, ...}]

for r in runs:
    print(r["name"], r["status"], r["startTime"])

RUN_ID = next(r["name"] for r in runs if r["status"] == "Failed")
```

---

## Step 3 — Get the Top-Level Error

```python
err = mcp("get_live_flow_run_error",
    environmentName=ENV, flowName=FLOW_ID, runName=RUN_ID)
# Returns:
# {
#   "runName": "08584296068667933411438594643CU15",
#   "failedActions": [
#     {"actionName": "Apply_to_each_prepare_workers", "status": "Failed",
#      "error": {"code": "ActionFailed", "message": "An action failed..."},
#      "startTime": "...", "endTime": "..."},
#     {"actionName": "HTTP_find_AD_User_by_Name", "status": "Failed",
#      "code": "NotSpecified", "startTime": "...", "endTime": "..."}
#   ],
#   "allActions": [
#     {"actionName": "Apply_to_each", "status": "Skipped"},
#     {"actionName": "Compose_WeekEnd", "status": "Succeeded"},
#     ...
#   ]
# }

# failedActions is ordered outer-to-inner. The ROOT cause is the LAST entry:
root = err["failedActions"][-1]
print(f"Root action: {root['actionName']} → code: {root.get('code')}")

# allActions shows every action's status — useful for spotting what was Skipped
# See common-errors.md to decode the error code.
```

---

## Step 4 — Read the Flow Definition

```python
defn = mcp("get_live_flow", environmentName=ENV, flowName=FLOW_ID)
actions = defn["properties"]["definition"]["actions"]
print(list(actions.keys()))
```

Find the failing action in the definition. Inspect its `inputs` expression
to understand what data it expects.

---

## Step 5 — Inspect Action Outputs (Walk Back from Failure)

For each action **leading up to** the failure, inspect its runtime output:

```python
for action_name in ["Compose_WeekEnd", "HTTP_Get_Data", "Parse_JSON"]:
    result = mcp("get_live_flow_run_action_outputs",
        environmentName=ENV,
        flowName=FLOW_ID,
        runName=RUN_ID,
        actionName=action_name)
    # Returns an array — single-element when actionName is provided
    out = result[0] if result else {}
    print(action_name, out.get("status"))
    print(json.dumps(out.get("outputs", {}), indent=2)[:500])
```

> ⚠️ Output payloads from array-processing actions can be very large.
> Always slice (e.g. `[:500]`) before printing.

---

## Step 6 — Pinpoint the Root Cause

### Expression Errors (e.g. `split` on null)
If the error mentions `InvalidTemplate` or a function name:
1. Find the action in the definition
2. Check what upstream action/expression it reads
3. Inspect that upstream action's output for null / missing fields

```python
# Example: action uses split(item()?['Name'], ' ')
# → null Name in the source data
result = mcp("get_live_flow_run_action_outputs", ..., actionName="Compose_Names")
# Returns a single-element array; index [0] to get the action object
if not result:
    print("No outputs returned for Compose_Names")
    names = []
else:
    names = result[0].get("outputs", {}).get("body") or []
nulls = [x for x in names if x.get("Name") is None]
print(f"{len(nulls)} records with null Name")
```

### Wrong Field Path
Expression `triggerBody()?['fieldName']` returns null → `fieldName` is wrong.
Check the trigger output shape with:
```python
mcp("get_live_flow_run_action_outputs", ..., actionName="<trigger-action-name>")
```

### Connection / Auth Failures
Look for `ConnectionAuthorizationFailed` — the connection owner must match the
service account running the flow. Cannot fix via API; fix in PA designer.

---

## Step 7 — Apply the Fix

**For expression/data issues**:
```python
defn = mcp("get_live_flow", environmentName=ENV, flowName=FLOW_ID)
acts = defn["properties"]["definition"]["actions"]

# Example: fix split on potentially-null Name
acts["Compose_Names"]["inputs"] = \
    "@coalesce(item()?['Name'], 'Unknown')"

conn_refs = defn["properties"]["connectionReferences"]
result = mcp("update_live_flow",
    environmentName=ENV,
    flowName=FLOW_ID,
    definition=defn["properties"]["definition"],
    connectionReferences=conn_refs)

print(result.get("error"))  # None = success
```

> ⚠️ `update_live_flow` always returns an `error` key.
> A value of `null` (Python `None`) means success.

---

## Step 8 — Verify the Fix

```python
# Resubmit the failed run
resubmit = mcp("resubmit_live_flow_run",
    environmentName=ENV, flowName=FLOW_ID, runName=RUN_ID)
print(resubmit)

# Wait ~30 s then check
import time; time.sleep(30)
new_runs = mcp("get_live_flow_runs", environmentName=ENV, flowName=FLOW_ID, top=3)
print(new_runs[0]["status"])   # Succeeded = done
```

### Testing HTTP-Triggered Flows

For flows with a `Request` (HTTP) trigger, use `trigger_live_flow` instead
of `resubmit_live_flow_run` to test with custom payloads:

```python
# First inspect what the trigger expects
schema = mcp("get_live_flow_http_schema",
    environmentName=ENV, flowName=FLOW_ID)
print("Expected body schema:", schema.get("triggerSchema"))
print("Response schemas:", schema.get("responseSchemas"))

# Trigger with a test payload
result = mcp("trigger_live_flow",
    environmentName=ENV,
    flowName=FLOW_ID,
    body={"name": "Test User", "value": 42})
print(f"Status: {result['status']}, Body: {result.get('body')}")
```

> `trigger_live_flow` handles AAD-authenticated triggers automatically.
> Only works for flows with a `Request` (HTTP) trigger type.

---

## Quick-Reference Diagnostic Decision Tree

| Symptom | First Tool to Call | What to Look For |
|---|---|---|
| Flow shows as Failed | `get_live_flow_run_error` | `failedActions[-1]["actionName"]` = root cause |
| Expression crash | `get_live_flow_run_action_outputs` on prior action | null / wrong-type fields in output body |
| Flow never starts | `get_live_flow` | check `properties.state` = "Started" |
| Action returns wrong data | `get_live_flow_run_action_outputs` | actual output body vs expected |
| Fix applied but still fails | `get_live_flow_runs` after resubmit | new run `status` field |

---

## Reference Files

- [common-errors.md](references/common-errors.md) — Error codes, likely causes, and fixes
- [debug-workflow.md](references/debug-workflow.md) — Full decision tree for complex failures

## Related Skills

- `power-automate-mcp` — Core connection setup and operation reference
- `power-automate-build` — Build and deploy new flows
