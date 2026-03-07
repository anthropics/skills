# FlowStudio MCP — Tool Response Catalog

Response shapes and behavioral notes for the FlowStudio Power Automate MCP server.

> **For tool names and parameters**: Always call `tools/list` on the server.
> It returns the authoritative, up-to-date schema for every tool.
> This document covers what `tools/list` does NOT tell you: **response shapes**
> and **non-obvious behaviors** discovered through real usage.

---

## Source of Truth

| Priority | Source | Covers |
|----------|--------|--------|
| 1 | **Real API response** | Always trust what the server actually returns |
| 2 | **`tools/list`** | Tool names, parameter names, types, required flags |
| 3 | **This document** | Response shapes, behavioral notes, gotchas |

> If this document disagrees with `tools/list` or real API behavior,
> the API wins. Update this document accordingly.

---

## Environment & Tenant Discovery

### `list_live_environments`

Response: direct array of environments.
```json
[
  {
    "id": "Default-26e65220-5561-46ef-9783-ce5f20489241",
    "displayName": "FlowStudio (default)",
    "sku": "Production",
    "location": "australia",
    "state": "Enabled",
    "isDefault": true,
    "isAdmin": true,
    "isMember": true,
    "createdTime": "2023-08-18T00:41:05Z"
  }
]
```

> Use the `id` value as `environmentName` in all other tools.

### `list_store_environments`

Same shape as `list_live_environments` but read from cache (faster).

---

## Connection Discovery

### `list_live_connections`

Response: wrapper object with `connections` array.
```json
{
  "connections": [
    {
      "id": "shared-office365-9f9d2c8e-55f1-49c9-9f9c-1c45d1fbbdce",
      "displayName": "user@contoso.com",
      "connectorName": "shared_office365",
      "createdBy": "User Name",
      "statuses": [{"status": "Connected"}],
      "createdTime": "2024-03-12T21:23:55.206815Z"
    }
  ],
  "totalCount": 56,
  "error": null
}
```

> **Key field**: `id` is the `connectionName` value used in `connectionReferences`.
>
> **Key field**: `connectorName` maps to apiId:
> `"/providers/Microsoft.PowerApps/apis/" + connectorName`
>
> Filter by status: `statuses[0].status == "Connected"`.
>
> **Note**: `tools/list` marks `environmentName` as optional, but the server
> returns `MissingEnvironmentFilter` (HTTP 400) if you omit it. Always pass
> `environmentName`.

### `list_store_connections`

Same connection data from cache.

---

## Flow Discovery & Listing

### `list_live_flows`

Response: wrapper object with `flows` array.
```json
{
  "mode": "owner",
  "flows": [
    {
      "id": "0757041a-8ef2-cf74-ef06-06881916f371",
      "displayName": "My Flow",
      "state": "Started",
      "triggerType": "Request",
      "triggerKind": "Http",
      "createdTime": "2023-08-18T01:18:17Z",
      "lastModifiedTime": "2023-08-18T12:47:42Z",
      "owners": "<aad-object-id>",
      "definitionAvailable": true
    }
  ],
  "totalCount": 100,
  "error": null
}
```

> Access via `result["flows"]`. `id` is a plain UUID --- use directly as `flowName`.
>
> `mode` indicates the access scope used (`"owner"` or `"admin"`).

### `list_store_flows`

Response: **direct array** (no wrapper).
```json
[
  {
    "id": "3991358a-f603-e49d-b1ed-a9e4f72e2dcb.0757041a-8ef2-cf74-ef06-06881916f371",
    "displayName": "Admin | Sync Template v3 (Solutions)",
    "state": "Started",
    "triggerType": "OpenApiConnectionWebhook",
    "environmentName": "3991358a-f603-e49d-b1ed-a9e4f72e2dcb",
    "runPeriodTotal": 100,
    "createdTime": "2023-08-18T01:18:17Z",
    "lastModifiedTime": "2023-08-18T12:47:42Z"
  }
]
```

> **`id` format**: `envId.flowId` --- split on the first `.` to extract the flow UUID:
> `flow_id = item["id"].split(".", 1)[1]`

### `get_store_flow`

Response: single flow metadata from cache (selected fields).
```json
{
  "id": "envId.flowId",
  "displayName": "My Flow",
  "state": "Started",
  "triggerType": "Recurrence",
  "runPeriodTotal": 100,
  "runPeriodFailRate": 0.1,
  "runPeriodSuccessRate": 0.9,
  "runPeriodFails": 10,
  "runPeriodSuccess": 90,
  "runPeriodDurationAverage": 29410.8,
  "runPeriodDurationMax": 158900.0,
  "runError": "{\"code\": \"EACCES\", ...}",
  "description": "Flow description",
  "tier": "Premium",
  "complexity": "{...}",
  "actions": 42,
  "connections": ["sharepointonline", "office365"],
  "owners": ["user@contoso.com"],
  "createdBy": "user@contoso.com"
}
```

> `runPeriodDurationAverage` / `runPeriodDurationMax` are in **milliseconds** (divide by 1000).
> `runError` is a **JSON string** --- parse with `json.loads()`.

---

## Flow Definition (Live API)

### `get_live_flow`

Response: full flow definition from PA API.
```json
{
  "name": "<flow-guid>",
  "properties": {
    "displayName": "My Flow",
    "state": "Started",
    "definition": {
      "triggers": { "..." },
      "actions": { "..." },
      "parameters": { "..." }
    },
    "connectionReferences": { "..." }
  }
}
```

### `update_live_flow`

**Create mode**: Omit `flowName` --- creates a new flow. `definition` and `displayName` required.

**Update mode**: Provide `flowName` --- PATCHes existing flow.

Response:
```json
{
  "created": false,
  "flowKey": "envId.flowId",
  "updated": ["definition", "connectionReferences"],
  "displayName": "My Flow",
  "state": "Started",
  "definition": { "...full definition..." },
  "error": null
}
```

> `error` is **always present** but may be `null`. Check `result.get("error") is not None`.
>
> On create: `created` is the new flow GUID (string). On update: `created` is `false`.
>
> `description` is **always required** (create and update).

### `add_live_flow_to_solution`

Migrates a non-solution flow into a solution. Returns error if already in a solution.

---

## Run History & Monitoring

### `get_live_flow_runs`

Response: direct array of runs (newest first).
```json
[{
  "name": "<run-id>",
  "status": "Succeeded|Failed|Running|Cancelled",
  "startTime": "2026-02-25T06:13:38Z",
  "endTime": "2026-02-25T06:14:02Z",
  "triggerName": "Recurrence",
  "error": null
}]
```

> `top` defaults to **30** and auto-paginates for higher values. Set `top: 300`
> for 24-hour coverage on flows running every 5 minutes.
>
> Run ID field is **`name`** (not `runName`). Use this value as the `runName`
> parameter in other tools.

### `get_live_flow_run_error`

Response: structured error breakdown for a failed run.
```json
{
  "runName": "08584296068667933411438594643CU15",
  "failedActions": [
    {
      "actionName": "Apply_to_each_prepare_workers",
      "status": "Failed",
      "error": {"code": "ActionFailed", "message": "An action failed."},
      "code": "ActionFailed",
      "startTime": "2026-02-25T06:13:52Z",
      "endTime": "2026-02-25T06:15:24Z"
    },
    {
      "actionName": "HTTP_find_AD_User_by_Name",
      "status": "Failed",
      "code": "NotSpecified",
      "startTime": "2026-02-25T06:14:01Z",
      "endTime": "2026-02-25T06:14:05Z"
    }
  ],
  "allActions": [
    {"actionName": "Apply_to_each", "status": "Skipped"},
    {"actionName": "Compose_WeekEnd", "status": "Succeeded"},
    {"actionName": "HTTP_find_AD_User_by_Name", "status": "Failed"}
  ]
}
```

> `failedActions` is ordered outer-to-inner --- the **last entry is the root cause**.
> Use `failedActions[-1]["actionName"]` as the starting point for diagnosis.

### `get_live_flow_run_action_outputs`

Response: array of action detail objects.
```json
[
  {
    "actionName": "Compose_WeekEnd_now",
    "status": "Succeeded",
    "startTime": "2026-02-25T06:13:52Z",
    "endTime": "2026-02-25T06:13:52Z",
    "error": null,
    "inputs": "Mon, 25 Feb 2026 06:13:52 GMT",
    "outputs": "Mon, 25 Feb 2026 06:13:52 GMT"
  }
]
```

> **`actionName` is optional**: omit it to return ALL actions in the run;
> provide it to return a single-element array for that action only.
>
> Outputs can be very large (50 MB+) for bulk-data actions. Use 120s+ timeout.

---

## Run Control

### `resubmit_live_flow_run`

Response: `{ flowKey, resubmitted: true, runName, triggerName }`

### `cancel_live_flow_run`

Cancels a `Running` flow run.

> Do NOT cancel runs waiting for an adaptive card response --- status `Running`
> is normal while a Teams card is awaiting user input.

---

## HTTP Trigger Tools

### `get_live_flow_http_schema`

Response keys:
```
flowKey            - Flow GUID
displayName        - Flow display name
triggerName        - Trigger action name (e.g. "manual")
triggerType        - Trigger type (e.g. "Request")
triggerKind        - Trigger kind (e.g. "Http")
requestMethod      - HTTP method (e.g. "POST")
relativePath       - Relative path configured on the trigger (if any)
requestSchema      - JSON schema the trigger expects as POST body
requestHeaders     - Headers the trigger expects
responseSchemas    - Array of JSON schemas defined on Response action(s)
responseSchemaCount - Number of Response actions that define output schemas
```

> The request body schema is in `requestSchema` (not `triggerSchema`).

### `get_live_flow_trigger_url`

Returns the signed callback URL for HTTP-triggered flows. Response includes
`flowKey`, `triggerName`, `triggerType`, `triggerKind`, `triggerMethod`, `triggerUrl`.

### `trigger_live_flow`

Response keys: `flowKey`, `triggerName`, `triggerUrl`, `requiresAadAuth`, `authType`,
`responseStatus`, `responseBody`.

> **Only works for `Request` (HTTP) triggers.** Returns an error for Recurrence
> and other trigger types: `"only HTTP Request triggers can be invoked via this tool"`.
>
> `responseStatus` + `responseBody` contain the flow's Response action output.
> AAD-authenticated triggers are handled automatically.

---

## Flow State Management

### `set_store_flow_state`

Start or stop a flow. Pass `state: "Started"` or `state: "Stopped"`.

---

## Store Tools --- FlowStudio for Teams Only

### `get_store_flow_summary`

Response: aggregated run statistics.
```json
{
  "totalRuns": 100,
  "failRuns": 10,
  "failRate": 0.1,
  "averageDurationSeconds": 29.4,
  "maxDurationSeconds": 158.9,
  "firstFailRunRemediation": "<hint or null>"
}
```

### `get_store_flow_runs`

Cached run history for the last N days with duration and remediation hints.

### `get_store_flow_errors`

Cached failed-only runs with failed action names and remediation hints.

### `get_store_flow_trigger_url`

Trigger URL from cache (instant, no PA API call).

### `update_store_flow`

Update governance metadata (description, tags, monitor flag, notification rules, business impact).

### `list_store_makers` / `get_store_maker`

Maker (citizen developer) discovery and detail.

### `list_store_power_apps`

List all Power Apps canvas apps from the cache.

---

## Behavioral Notes

Non-obvious behaviors discovered through real API usage. These are things
`tools/list` cannot tell you.

### `get_live_flow_run_action_outputs`
- **`actionName` is optional**: omit to get all actions, provide to get one.
  This changes the response from N elements to 1 element (still an array).
- Outputs can be 50 MB+ for bulk-data actions --- always use 120s+ timeout.

### `update_live_flow`
- `description` is **always required** (create and update modes).
- `error` key is **always present** in response --- `null` means success.
  Do NOT check `if "error" in result`; check `result.get("error") is not None`.
- On create, `created` = new flow GUID (string). On update, `created` = `false`.

### `trigger_live_flow`
- **Only works for HTTP Request triggers.** Returns error for Recurrence, connector,
  and other trigger types.
- AAD-authenticated triggers are handled automatically (impersonated Bearer token).

### `get_live_flow_runs`
- `top` defaults to **30** with automatic pagination for higher values.
- Run ID field is `name`, not `runName`. Use this value as `runName` in other tools.
- Runs are returned newest-first.

### Teams `PostMessageToConversation` (via `update_live_flow`)
- **"Chat with Flow bot"**: `body/recipient` = `"user@domain.com;"` (string with trailing semicolon).
- **"Channel"**: `body/recipient` = `{"groupId": "...", "channelId": "..."}` (object).
- `poster`: `"Flow bot"` for Workflows bot identity, `"User"` for user identity.

### `list_live_connections`
- `id` is the value you need for `connectionName` in `connectionReferences`.
- `connectorName` maps to apiId: `"/providers/Microsoft.PowerApps/apis/" + connectorName`.
