# FlowStudio MCP — Common Power Automate Errors

Reference for error codes, likely causes, and recommended fixes when debugging
Power Automate flows via the FlowStudio MCP server.

---

## Expression / Template Errors

### `InvalidTemplate` — Function Applied to Null

**Full message pattern**: `"Unable to process template language expressions... function 'split' expects its first argument 'text' to be of type string"`

**Root cause**: An expression like `@split(item()?['Name'], ' ')` received a null value.

**Diagnosis**:
1. Note the action name in the error message
2. Call `get_live_flow_run_action_outputs` on the action that produces the array
3. Find items where `Name` (or the referenced field) is `null`

**Fixes**:
```
Before: @split(item()?['Name'], ' ')
After:  @split(coalesce(item()?['Name'], ''), ' ')

Or guard the whole foreach body with a condition:
  expression: "@not(empty(item()?['Name']))"
```

---

### `InvalidTemplate` — Wrong Expression Path

**Full message pattern**: `"Unable to process template language expressions... 'triggerBody()?['FieldName']' is of type 'Null'"`

**Root cause**: The field name in the expression doesn't match the actual payload schema.

**Diagnosis**:
```python
# Check trigger output shape
mcp("get_live_flow_run_action_outputs",
    environmentName=ENV, flowName=FLOW_ID, runName=RUN_ID,
    actionName="<trigger-name>")
# Compare actual keys vs expression
```

**Fix**: Update expression to use the correct key name. Common mismatches:
- `triggerBody()?['body']` vs `triggerBody()?['Body']` (case-sensitive)
- `triggerBody()?['Subject']` vs `triggerOutputs()?['body/Subject']`

---

### `InvalidTemplate` — Type Mismatch

**Full message pattern**: `"... expected type 'Array' but got type 'Object'"`

**Root cause**: Passing an object where the expression expects an array (e.g. a single item HTTP response vs a list response).

**Fix**:
```
Before: @outputs('HTTP')?['body']
After:  @outputs('HTTP')?['body/value']    ← for OData list responses
        @createArray(outputs('HTTP')?['body'])  ← wrap single object in array
```

---

## Connection / Auth Errors

### `ConnectionAuthorizationFailed`

**Full message**: `"The API connection ... is not authorized."`

**Root cause**: The connection referenced in the flow is owned by a different
user/service account than the one whose JWT is being used.

**Diagnosis**: Check `properties.connectionReferences` — the `connectionName` GUID
identifies the owner. Cannot be fixed via API.

**Fix options**:
1. Open flow in Power Automate designer → re-authenticate the connection
2. Use a connection owned by the service account whose token you hold
3. Share the connection with the service account in PA admin

---

### `InvalidConnectionCredentials`

**Root cause**: The underlying OAuth token for the connection has expired or
the user's credentials changed.

**Fix**: Owner must sign in to Power Automate and refresh the connection.

---

## HTTP Action Errors

### `ActionFailed` — HTTP 4xx/5xx

**Full message pattern**: `"An HTTP request to... failed with status code '400'"`

**Diagnosis**:
```python
actions_out = mcp("get_live_flow_run_action_outputs", ..., actionName="HTTP_My_Call")
item = actions_out[0]   # first entry in the returned array
print(item["outputs"]["statusCode"])   # 400, 401, 403, 500...
print(item["outputs"]["body"])         # error details from target API
```

**Common causes**:
- 401 — missing or expired auth header
- 403 — permission denied on target resource
- 404 — wrong URL / resource deleted
- 400 — malformed JSON body (check expression that builds the body)

---

### `ActionFailed` — HTTP Timeout

**Root cause**: Target endpoint did not respond within the connector's timeout
(default 90 s for HTTP action).

**Fix**: Add retry policy to the HTTP action, or split the payload into smaller
batches to reduce per-request processing time.

---

## Control Flow Errors

### `ActionSkipped` Instead of Running

**Root cause**: The `runAfter` condition wasn't met. E.g. an action set to
`runAfter: { "Prev": ["Succeeded"] }` won't run if `Prev` failed or was skipped.

**Diagnosis**: Check the preceding action's status. Deliberately skipped
(e.g. inside a false branch) is intentional — unexpected skip is a logic gap.

**Fix**: Add `"Failed"` or `"Skipped"` to the `runAfter` status array if the
action should run on those outcomes too.

---

### Foreach Runs in Wrong Order / Race Condition

**Root cause**: `Foreach` without `operationOptions: "Sequential"` runs
iterations in parallel, causing write conflicts or undefined ordering.

**Fix**: Add `"operationOptions": "Sequential"` to the Foreach action.

---

### Foreach Parent Failed After Handled Inner Failure

**Symptom**: Inner actions have failure handlers, but the parent `Foreach` still
shows `Failed`, and downstream actions such as `Response` are skipped.

**Root cause**: A handled child failure can still mark the loop container as
failed. Downstream `runAfter` that only accepts `Succeeded` will not run.

**Diagnosis**: Inspect the parent foreach with `get_live_flow_run_error`, then
inspect child action outputs for the iteration that failed.

**Fix**: If partial success is acceptable, allow the downstream join/response to
run after `Succeeded` and `Failed`, and include an explicit error summary in the
payload. If the loop must be all-or-nothing, wrap risky inner work in a Scope and
handle success/failure at the Scope boundary.

---

## Update / Deploy Errors

### `update_live_flow` Returns No-Op

**Symptom**: `result["updated"]` is empty list or `result["created"]` is empty.

**Likely cause**: Passing wrong parameter name. The required key is `definition`
(object), not `flowDefinition` or `body`.

---

### `update_live_flow` — `"Supply connectionReferences"`

**Root cause**: The definition contains `OpenApiConnection` or
`OpenApiConnectionWebhook` actions but `connectionReferences` was not passed.

**Fix**: Fetch the existing connection references with `get_live_flow` and pass
them as the `connectionReferences` argument.

---

## Data Logic Errors

### `union()` Overriding Correct Records with Nulls

**Symptom**: After merging two arrays, some records have null fields that existed
in one of the source arrays.

**Root cause**: `union(old_data, new_data)` — `union()` first-wins, so old_data
values override new_data for matching records.

**Fix**: Swap argument order: `union(new_data, old_data)`

```
Before: @sort(union(outputs('Old_Array'), body('New_Array')), 'Date')
After:  @sort(union(body('New_Array'), outputs('Old_Array')), 'Date')
```

---

### Null Cascade in Filter Array / Query

**Symptom**: A lookup/filter step returns the wrong record or a later expression
fails on null even though the filter action itself succeeded.

**Root cause**: The lookup key is null or empty. A condition such as
`equals(item()?['Email'], outputs('Lookup_Email'))` can accidentally match rows
where both sides are null, or can pass an empty array downstream.

**Diagnosis**: Inspect the action that creates the lookup key and the filter
output length. Confirm the key is non-empty before trusting the filter result.

**Fix**: Add a non-empty guard before the filter, normalize comparison values
with `trim()`/`toLower()`, and branch explicitly when no match is found.
