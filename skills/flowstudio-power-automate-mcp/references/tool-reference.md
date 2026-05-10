# FlowStudio MCP — Tool Response Catalog

Response shapes and behavioral notes for the FlowStudio Power Automate MCP server.

> **For tool names and parameters**: Prefer `list_skills` and `tool_search`.
> They return focused, up-to-date schemas without loading every MCP tool at once.
> Use `tools/list` only as a low-level fallback when the meta-tools are not available.
> This document covers what tool schemas do NOT tell you: **response shapes**
> and **non-obvious behaviors** discovered through real usage.

---

## Source of Truth

| Priority | Source | Covers |
|----------|--------|--------|
| 1 | **Real API response** | Always trust what the server actually returns |
| 2 | **`list_skills` / `tool_search`** | Tool names, parameter names, types, required flags |
| 3 | **This document** | Response shapes, behavioral notes, gotchas |

> If this document disagrees with `tool_search`, `tools/list`, or real API
> behavior, the API wins. Update this document accordingly.

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
      "environment": "Default-26e65220-...",
      "createdBy": "User Name",
      "authenticatedUser": "user@contoso.com",
      "overallStatus": "Connected",
      "statuses": [{"status": "Connected"}],
      "createdTime": "2024-03-12T21:23:55.206815Z",
      "connectionReferenceTemplate": {
        "connectionName": "shared-office365-9f9d2c8e-55f1-49c9-9f9c-1c45d1fbbdce",
        "source": "Invoker",
        "id": "/providers/Microsoft.PowerApps/apis/shared_office365"
      },
      "hostTemplate": {
        "connectionName": "shared_office365"
      }
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
> Filter by status: prefer `overallStatus == "Connected"` when present; otherwise
> check `statuses[0].status == "Connected"`.
>
> For build workflows, pass `environmentName` to avoid using a connection from
> the wrong environment. Omit it only when intentionally inventorying connections
> across all environments.
>
> Pass `search=<connector or account>` to narrow output and receive
> `connectionReferenceTemplate` plus `hostTemplate` values that can be copied
> directly into `update_live_flow`.

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
  "nextLink": null,
  "error": null
}
```

> Access via `result["flows"]`. `id` is a plain UUID --- use directly as `flowName`.
>
> `mode` indicates the access scope used (`"owner"` or `"admin"`).
>
> Parameters added in newer server versions:
> - `search`: filter by display name server-side.
> - `mode`: `owner` for flows owned by the MCP identity; `admin` for all flows
>   visible to an admin account.
> - `timeoutSeconds`: return partial results with `nextLink` instead of waiting
>   on very large environments.
> - `continuationUrl`: pass the previous `nextLink` to continue the same query.

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

> **`id` format**: `<environmentId>.<flowId>` --- split on the first `.` to extract the flow UUID:
> `flow_id = item["id"].split(".", 1)[1]`

### `get_store_flow`

Response: single flow metadata from cache (selected fields).
```json
{
  "id": "<environmentId>.<flowId>",
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
  "flowKey": "<environmentId>.<flowId>",
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
> Required fields can vary by server version. Use `tool_search` with
> `select:update_live_flow` before creating or patching a flow; if a description
> is required, include either the new description or the existing one from
> `get_live_flow`.
>
> The flow description is part of the workflow definition (`definition.description`),
> not a top-level tool argument in current schemas.

### `add_live_flow_to_solution`

Migrates a non-solution flow into a solution. Returns error if already in a solution.

Use this after creating a Copilot Studio Skills-triggered flow that must be
discoverable as an agent tool. Pass `solutionId` for the target solution. If the
server supports omitting `solutionId`, it uses the environment's default solution;
prefer an explicit unmanaged solution for production ALM.

This tool changes solution membership only. It does not validate the trigger
schema, publish a Copilot Studio agent, or prove that the flow is callable by the
agent.

---

## Connector Operation Discovery

### `describe_live_connector`

Describes a connector/API and its operations. Use it before creating connector
actions instead of guessing operation JSON.

Common modes:

| Call shape | Use |
|---|---|
| `search="send email"` without `connectorName` | Search operations across connectors |
| `connectorName="shared_sharepointonline"` | Compact operation catalog for one connector |
| `operationId="GetItems"` | Expanded schema for one operation |
| `variant="flowbot_chat"` | Authored example for one operation variant |

The operation detail can include:
- `hint`: authored guidance from the connector hints table.
- `exampleDefinition`: copy-ready action/trigger shape when available.
- Dynamic metadata with `nextTool=get_live_dynamic_options` or
  `nextTool=get_live_dynamic_properties`.

### `get_live_dynamic_options`

Resolves live dropdown/list options for connector parameters. Use this for
IDs selected from lists, such as SharePoint sites/lists, Teams teams/channels,
or other `x-ms-dynamic-list` / `x-ms-dynamic-values` parameters.

Pass the `dynamicMetadata` object returned by `describe_live_connector`, the
connection id from `list_live_connections`, and any already-resolved dependent
parameters.

### `get_live_dynamic_properties`

Resolves live schema/field properties for connector parameters. Use this for
dynamic field sets such as SharePoint list item columns after the site and list
are known.

Useful parameters:
- `parameters`: dependent values, for example `{ "dataset": "<site-url>",
  "table": "<list-id>" }`.
- `propertyName`: request one field after inspecting the compact response.
- `includeRaw`: include raw connector schema only when needed; it can be large.

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

> **`actionName` is optional**: omit it to return top-level actions in the run.
> Provide it for a specific action. If that action runs inside a foreach, the
> tool can return every repetition of that action across iterations; pass
> `iterationIndex` to pin to one zero-based iteration.
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

Deprecated. Prefer `get_live_flow` and inspect the `Request` trigger's
`inputs.schema` plus any `Response` actions directly from the definition.

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

Deprecated. Prefer `trigger_live_flow` when you need to invoke an HTTP-triggered
flow; it fetches the current callback URL internally.

Returns the signed callback URL for HTTP-triggered flows. Response includes
`flowKey`, `triggerName`, `triggerType`, `triggerKind`, `triggerMethod`, `triggerUrl`.

### `trigger_live_flow`

Response keys: `flowKey`, `triggerName`, `triggerUrl`, `requiresAadAuth`, `authType`,
`responseStatus`, `responseBody`.

> **Only works for `Request` (HTTP) triggers.** Returns an error for Recurrence
> and other trigger types: `"only HTTP Request triggers can be invoked via this tool"`.
> `Button`-kind triggers return `ListCallbackUrlOperationBlocked`.
>
> `responseStatus` + `responseBody` contain the flow's Response action output.
> AAD-authenticated triggers are handled automatically.
>
> **Content-type note**: The body is sent as `application/octet-stream` (raw),
> not `application/json`. Flows with a trigger schema that has `required` fields
> will reject the request with `InvalidRequestContent` (400) because PA validates
> `Content-Type` before parsing against the schema. Flows without a schema, or
> flows designed to accept raw input (e.g. Baker-pattern flows that parse the body
> internally), will work fine. The flow receives the JSON as base64-encoded
> `$content` with `$content-type: application/octet-stream`.

---

## Flow State Management

### `set_live_flow_state`

Start or stop a Power Automate flow via the live PA API. Does **not** require
a Power Clarity workspace — works for any flow the impersonated account can access.
Reads the current state first and only issues the start/stop call if a change is
actually needed.

Parameters: `environmentName`, `flowName`, `state` (`"Started"` | `"Stopped"`) — all required.

Response:
```json
{
  "flowName": "6321ab25-7eb0-42df-b977-e97d34bcb272",
  "environmentName": "Default-26e65220-...",
  "requestedState": "Started",
  "actualState": "Started"
}
```

> **Use this tool** — not `update_live_flow` — to start or stop a flow.
> `update_live_flow` only changes displayName/definition; the PA API ignores
> state passed through that endpoint.

### `set_store_flow_state`

Start or stop a flow via the live PA API **and** persist the updated state back
to the Power Clarity cache. Same parameters as `set_live_flow_state` but requires
a Power Clarity workspace.

Response (different shape from `set_live_flow_state`):
```json
{
  "flowKey": "<environmentId>.<flowId>",
  "requestedState": "Stopped",
  "currentState": "Stopped",
  "flow": { /* full gFlows record, same shape as get_store_flow */ }
}
```

> Prefer `set_live_flow_state` when you only need to toggle state — it's
> simpler and has no subscription requirement.
>
> Use `set_store_flow_state` when you need the cache updated immediately
> (without waiting for the next daily scan) AND want the full updated
> governance record back in the same call — useful for workflows that
> stop a flow and immediately tag or inspect it.

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
tool schemas cannot tell you.

### `get_live_flow_run_action_outputs`
- **`actionName` is optional**: omit to get top-level actions, provide to get one
  action. For actions inside foreach loops, a named action may return multiple
  repetitions; use `iterationIndex` to pin to one iteration.
- Outputs can be 50 MB+ for bulk-data actions --- always use 120s+ timeout.

### `update_live_flow`
- Required fields can vary by server version; confirm with `tool_search`
  (`select:update_live_flow`) before create/update. If `description` is required,
  preserve the existing description when patching.
- `error` key is **always present** in response --- `null` means success.
  Do NOT check `if "error" in result`; check `result.get("error") is not None`.
- On create, `created` = new flow GUID (string). On update, `created` = `false`.
- **Cannot change flow state.** Only updates displayName, definition, and
  connectionReferences. Use `set_live_flow_state` to start/stop a flow.

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
- For build workflows, pass `environmentName`; omitting it inventories
  connections across environments.
- Use `search=<connector/account>` to get smaller output and paste-ready
  `connectionReferenceTemplate` / `hostTemplate` values.
- `id` is the value you need for `connectionName` in `connectionReferences`.
- `connectorName` maps to apiId: `"/providers/Microsoft.PowerApps/apis/" + connectorName`.
