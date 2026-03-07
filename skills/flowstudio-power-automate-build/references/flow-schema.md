# FlowStudio MCP — Flow Definition Schema

The full JSON structure expected by `update_live_flow` (and returned by `get_live_flow`).

---

## Top-Level Shape

```json
{
  "$schema": "https://schema.management.azure.com/providers/Microsoft.Logic/schemas/2016-06-01/workflowdefinition.json#",
  "contentVersion": "1.0.0.0",
  "parameters": {
    "$connections": {
      "defaultValue": {},
      "type": "Object"
    }
  },
  "triggers": {
    "<TriggerName>": { ... }
  },
  "actions": {
    "<ActionName>": { ... }
  },
  "outputs": {}
}
```

---

## `triggers`

Exactly one trigger per flow definition. The key name is arbitrary but
conventional names are used (e.g. `Recurrence`, `manual`, `When_a_new_email_arrives`).

See [trigger-types.md](trigger-types.md) for all trigger templates.

---

## `actions`

Dictionary of action definitions keyed by unique action name.
Key names may not contain spaces — use underscores.

Each action must include:
- `type` — action type identifier
- `runAfter` — map of upstream action names → status conditions array
- `inputs` — action-specific input configuration

See [action-patterns-core.md](action-patterns-core.md), [action-patterns-data.md](action-patterns-data.md),
and [action-patterns-connectors.md](action-patterns-connectors.md) for templates.

### Optional Action Properties

Beyond the required `type`, `runAfter`, and `inputs`, actions can include:

| Property | Purpose |
|---|---|
| `runtimeConfiguration` | Pagination, concurrency, secure data, chunked transfer |
| `operationOptions` | `"Sequential"` for Foreach, `"DisableAsyncPattern"` for HTTP |
| `limit` | Timeout override (e.g. `{"timeout": "PT2H"}`) |

#### `runtimeConfiguration` Variants

**Pagination** (SharePoint Get Items with large lists):
```json
"runtimeConfiguration": {
  "paginationPolicy": {
    "minimumItemCount": 5000
  }
}
```
> Without this, Get Items silently caps at 256 results. Set `minimumItemCount`
> to the maximum rows you expect. Required for any SharePoint list over 256 items.

**Concurrency** (parallel Foreach):
```json
"runtimeConfiguration": {
  "concurrency": {
    "repetitions": 20
  }
}
```

**Secure inputs/outputs** (mask values in run history):
```json
"runtimeConfiguration": {
  "secureData": {
    "properties": ["inputs", "outputs"]
  }
}
```
> Use on actions that handle credentials, tokens, or PII. Masked values show
> as `"<redacted>"` in the flow run history UI and API responses.

**Chunked transfer** (large HTTP payloads):
```json
"runtimeConfiguration": {
  "contentTransfer": {
    "transferMode": "Chunked"
  }
}
```
> Enable on HTTP actions sending or receiving bodies >100 KB (e.g. parent→child
> flow calls with large arrays).

---

## `runAfter` Rules

The first action in a branch has `"runAfter": {}` (empty — runs after trigger).

Subsequent actions declare their dependency:

```json
"My_Action": {
  "runAfter": {
    "Previous_Action": ["Succeeded"]
  }
}
```

Multiple upstream dependencies:
```json
"runAfter": {
  "Action_A": ["Succeeded"],
  "Action_B": ["Succeeded", "Skipped"]
}
```

Error-handling action (runs when upstream failed):
```json
"Log_Error": {
  "runAfter": {
    "Risky_Action": ["Failed"]
  }
}
```

---

## `parameters` (Flow-Level Input Parameters)

Optional. Define reusable values at the flow level:

```json
"parameters": {
  "listName": {
    "type": "string",
    "defaultValue": "MyList"
  },
  "maxItems": {
    "type": "integer",
    "defaultValue": 100
  }
}
```

Reference: `@parameters('listName')` in expression strings.

---

## `outputs`

Rarely used in cloud flows. Leave as `{}` unless the flow is called
as a child flow and needs to return values.

For child flows that return data:

```json
"outputs": {
  "resultData": {
    "type": "object",
    "value": "@outputs('Compose_Result')"
  }
}
```

---

## Scoped Actions (Inside Scope Block)

Actions that need to be grouped for error handling or clarity:

```json
"Scope_Main_Process": {
  "type": "Scope",
  "runAfter": {},
  "actions": {
    "Step_One": { ... },
    "Step_Two": { "runAfter": { "Step_One": ["Succeeded"] }, ... }
  }
}
```

---

## Full Minimal Example

```json
{
  "$schema": "https://schema.management.azure.com/providers/Microsoft.Logic/schemas/2016-06-01/workflowdefinition.json#",
  "contentVersion": "1.0.0.0",
  "triggers": {
    "Recurrence": {
      "type": "Recurrence",
      "recurrence": {
        "frequency": "Week",
        "interval": 1,
        "schedule": { "weekDays": ["Monday"] },
        "startTime": "2026-01-05T09:00:00Z",
        "timeZone": "AUS Eastern Standard Time"
      }
    }
  },
  "actions": {
    "Compose_Greeting": {
      "type": "Compose",
      "runAfter": {},
      "inputs": "Good Monday!"
    }
  },
  "outputs": {}
}
```
