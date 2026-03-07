# FlowStudio MCP — Action Patterns: Data Transforms

Array operations, HTTP calls, parsing, and data transformation patterns.

> All examples assume `"runAfter"` is set appropriately.
> `<connectionName>` is the **key** in `connectionReferences` (e.g. `shared_sharepointonline`), not the GUID.
> The GUID goes in the map value's `connectionName` property.

---

## Array Operations

### Select (Reshape / Project an Array)

Transforms each item in an array, keeping only the columns you need or renaming them.
Avoids carrying large objects through the rest of the flow.

```json
"Select_Needed_Columns": {
  "type": "Select",
  "runAfter": {},
  "inputs": {
    "from": "@outputs('HTTP_Get_Subscriptions')?['body/data']",
    "select": {
      "id":           "@item()?['id']",
      "status":       "@item()?['status']",
      "trial_end":    "@item()?['trial_end']",
      "cancel_at":    "@item()?['cancel_at']",
      "interval":     "@item()?['plan']?['interval']"
    }
  }
}
```

Result reference: `@body('Select_Needed_Columns')` — returns a direct array of reshaped objects.

> Use Select before looping or filtering to reduce payload size and simplify
> downstream expressions. Works on any array — SP results, HTTP responses, variables.
>
> **Tips:**
> - **Single-to-array coercion:** When an API returns a single object but you need
>   Select (which requires an array), wrap it: `@array(body('Get_Employee')?['data'])`.
>   The output is a 1-element array — access results via `?[0]?['field']`.
> - **Null-normalize optional fields:** Use `@if(empty(item()?['field']), null, item()?['field'])`
>   on every optional field to normalize empty strings, missing properties, and empty
>   objects to explicit `null`. Ensures consistent downstream `@equals(..., @null)` checks.
> - **Flatten nested objects:** Project nested properties into flat fields:
>   ```
>   "manager_name": "@if(empty(item()?['manager']?['name']), null, item()?['manager']?['name'])"
>   ```
>   This enables direct field-level comparison with a flat schema from another source.

---

### Filter Array (Query)

Filters an array to items matching a condition. Use the action form (not the `filter()`
expression) for complex multi-condition logic — it's clearer and easier to maintain.

```json
"Filter_Active_Subscriptions": {
  "type": "Query",
  "runAfter": {},
  "inputs": {
    "from": "@body('Select_Needed_Columns')",
    "where": "@and(or(equals(item().status, 'trialing'), equals(item().status, 'active')), equals(item().cancel_at, null))"
  }
}
```

Result reference: `@body('Filter_Active_Subscriptions')` — direct filtered array.

> Tip: run multiple Filter Array actions on the same source array to create
> named buckets (e.g. active, being-canceled, fully-canceled), then use
> `coalesce(first(body('Filter_A')), first(body('Filter_B')), ...)` to pick
> the highest-priority match without any loops.

---

### Create CSV Table (Array → CSV String)

Converts an array of objects into a CSV-formatted string — no connector call, no code.
Use after a `Select` or `Filter Array` to export data or pass it to a file-write action.

```json
"Create_CSV": {
  "type": "Table",
  "runAfter": {},
  "inputs": {
    "from": "@body('Select_Output_Columns')",
    "format": "CSV"
  }
}
```

Result reference: `@body('Create_CSV')` — a plain string with header row + data rows.

```json
// Custom column order / renamed headers:
"Create_CSV_Custom": {
  "type": "Table",
  "inputs": {
    "from": "@body('Select_Output_Columns')",
    "format": "CSV",
    "columns": [
      { "header": "Date",        "value": "@item()?['transactionDate']" },
      { "header": "Amount",      "value": "@item()?['amount']" },
      { "header": "Description", "value": "@item()?['description']" }
    ]
  }
}
```

> Without `columns`, headers are taken from the object property names in the source array.
> With `columns`, you control header names and column order explicitly.
>
> The output is a raw string. Write it to a file with `CreateFile` or `UpdateFile`
> (set `body` to `@body('Create_CSV')`), or store in a variable with `SetVariable`.
>
> If source data came from Power BI's `ExecuteDatasetQuery`, column names will be
> wrapped in square brackets (e.g. `[Amount]`). Strip them before writing:
> `@replace(replace(body('Create_CSV'),'[',''),']','')`

---

### range() + Select for Array Generation

`range(0, N)` produces an integer sequence `[0, 1, 2, …, N-1]`. Pipe it through
a Select action to generate date series, index grids, or any computed array
without a loop:

```json
// Generate 14 consecutive dates starting from a base date
"Generate_Date_Series": {
  "type": "Select",
  "inputs": {
    "from": "@range(0, 14)",
    "select": "@addDays(outputs('Base_Date'), item(), 'yyyy-MM-dd')"
  }
}
```

Result: `@body('Generate_Date_Series')` → `["2025-01-06", "2025-01-07", …, "2025-01-19"]`

```json
// Flatten a 2D array (rows × cols) into 1D using arithmetic indexing
"Flatten_Grid": {
  "type": "Select",
  "inputs": {
    "from": "@range(0, mul(length(outputs('Rows')), length(outputs('Cols'))))",
    "select": {
      "row": "@outputs('Rows')[div(item(), length(outputs('Cols')))]",
      "col": "@outputs('Cols')[mod(item(), length(outputs('Cols')))]"
    }
  }
}
```

> `range()` is zero-based. The Cartesian product pattern above uses `div(i, cols)`
> for the row index and `mod(i, cols)` for the column index — equivalent to a
> nested for-loop flattened into a single pass. Useful for generating time-slot ×
> date grids, shift × location assignments, etc.

---

### Dynamic Dictionary via json(concat(join()))

When you need O(1) key→value lookups at runtime and Power Automate has no native
dictionary type, build one from an array using Select + join + json:

```json
"Build_Key_Value_Pairs": {
  "type": "Select",
  "inputs": {
    "from": "@body('Get_Lookup_Items')?['value']",
    "select": "@concat('\"', item()?['Key'], '\":\"', item()?['Value'], '\"')"
  }
},
"Assemble_Dictionary": {
  "type": "Compose",
  "inputs": "@json(concat('{', join(body('Build_Key_Value_Pairs'), ','), '}'))"
}
```

Lookup: `@outputs('Assemble_Dictionary')?['myKey']`

```json
// Practical example: date → rate-code lookup for business rules
"Build_Holiday_Rates": {
  "type": "Select",
  "inputs": {
    "from": "@body('Get_Holidays')?['value']",
    "select": "@concat('\"', formatDateTime(item()?['Date'], 'yyyy-MM-dd'), '\":\"', item()?['RateCode'], '\"')"
  }
},
"Holiday_Dict": {
  "type": "Compose",
  "inputs": "@json(concat('{', join(body('Build_Holiday_Rates'), ','), '}'))"
}
```

Then inside a loop: `@coalesce(outputs('Holiday_Dict')?[item()?['Date']], 'Standard')`

> The `json(concat('{', join(...), '}'))` pattern works for string values. For numeric
> or boolean values, omit the inner escaped quotes around the value portion.
> Keys must be unique — duplicate keys silently overwrite earlier ones.
> This replaces deeply nested `if(equals(key,'A'),'X', if(equals(key,'B'),'Y', ...))` chains.

---

### union() for Changed-Field Detection

When you need to find records where *any* of several fields has changed, run one
`Filter Array` per field and `union()` the results. This avoids a complex
multi-condition filter and produces a clean deduplicated set:

```json
"Filter_Name_Changed": {
  "type": "Query",
  "inputs": { "from": "@body('Existing_Records')",
              "where": "@not(equals(item()?['name'], item()?['dest_name']))" }
},
"Filter_Status_Changed": {
  "type": "Query",
  "inputs": { "from": "@body('Existing_Records')",
              "where": "@not(equals(item()?['status'], item()?['dest_status']))" }
},
"All_Changed": {
  "type": "Compose",
  "inputs": "@union(body('Filter_Name_Changed'), body('Filter_Status_Changed'))"
}
```

Reference: `@outputs('All_Changed')` — deduplicated array of rows where anything changed.

> `union()` deduplicates by object identity, so a row that changed in both fields
> appears once. Add more `Filter_*_Changed` inputs to `union()` as needed:
> `@union(body('F1'), body('F2'), body('F3'))`

---

### File-Content Change Gate

Before running expensive processing on a file or blob, compare its current content
to a stored baseline. Skip entirely if nothing has changed — makes sync flows
idempotent and safe to re-run or schedule aggressively.

```json
"Get_File_From_Source": { ... },
"Get_Stored_Baseline": { ... },
"Condition_File_Changed": {
  "type": "If",
  "expression": {
    "not": {
      "equals": [
        "@base64(body('Get_File_From_Source'))",
        "@body('Get_Stored_Baseline')"
      ]
    }
  },
  "actions": {
    "Update_Baseline": { "...": "overwrite stored copy with new content" },
    "Process_File":    { "...": "all expensive work goes here" }
  },
  "else": { "actions": {} }
}
```

> Store the baseline as a file in SharePoint or blob storage — `base64()`-encode the
> live content before comparing so binary and text files are handled uniformly.
> Write the new baseline **before** processing so a re-run after a partial failure
> does not re-process the same file again.

---

### Set-Join for Sync (Update Detection without Nested Loops)

When syncing a source collection into a destination (e.g. API response → SharePoint list,
CSV → database), avoid nested `Apply to each` loops to find changed records.
Instead, **project flat key arrays** and use `contains()` to perform set operations —
zero nested loops, and the final loop only touches changed items.

**Full insert/update/delete sync pattern:**

```json
// Step 1 — Project a flat key array from the DESTINATION (e.g. SharePoint)
"Select_Dest_Keys": {
  "type": "Select",
  "inputs": {
    "from": "@outputs('Get_Dest_Items')?['body/value']",
    "select": "@item()?['Title']"
  }
}
// → ["KEY1", "KEY2", "KEY3", ...]

// Step 2 — INSERT: source rows whose key is NOT in destination
"Filter_To_Insert": {
  "type": "Query",
  "inputs": {
    "from": "@body('Source_Array')",
    "where": "@not(contains(body('Select_Dest_Keys'), item()?['key']))"
  }
}
// → Apply to each Filter_To_Insert → CreateItem

// Step 3 — INNER JOIN: source rows that exist in destination
"Filter_Already_Exists": {
  "type": "Query",
  "inputs": {
    "from": "@body('Source_Array')",
    "where": "@contains(body('Select_Dest_Keys'), item()?['key'])"
  }
}

// Step 4 — UPDATE: one Filter per tracked field, then union them
"Filter_Field1_Changed": {
  "type": "Query",
  "inputs": {
    "from": "@body('Filter_Already_Exists')",
    "where": "@not(equals(item()?['field1'], item()?['dest_field1']))"
  }
}
"Filter_Field2_Changed": {
  "type": "Query",
  "inputs": {
    "from": "@body('Filter_Already_Exists')",
    "where": "@not(equals(item()?['field2'], item()?['dest_field2']))"
  }
}
"Union_Changed": {
  "type": "Compose",
  "inputs": "@union(body('Filter_Field1_Changed'), body('Filter_Field2_Changed'))"
}
// → rows where ANY tracked field differs

// Step 5 — Resolve destination IDs for changed rows (no nested loop)
"Select_Changed_Keys": {
  "type": "Select",
  "inputs": { "from": "@outputs('Union_Changed')", "select": "@item()?['key']" }
}
"Filter_Dest_Items_To_Update": {
  "type": "Query",
  "inputs": {
    "from": "@outputs('Get_Dest_Items')?['body/value']",
    "where": "@contains(body('Select_Changed_Keys'), item()?['Title'])"
  }
}
// Step 6 — Single loop over changed items only
"Apply_to_each_Update": {
  "type": "Foreach",
  "foreach": "@body('Filter_Dest_Items_To_Update')",
  "actions": {
    "Get_Source_Row": {
      "type": "Query",
      "inputs": {
        "from": "@outputs('Union_Changed')",
        "where": "@equals(item()?['key'], items('Apply_to_each_Update')?['Title'])"
      }
    },
    "Update_Item": {
      "...": "...",
      "id": "@items('Apply_to_each_Update')?['ID']",
      "item/field1": "@first(body('Get_Source_Row'))?['field1']"
    }
  }
}

// Step 7 — DELETE: destination keys NOT in source
"Select_Source_Keys": {
  "type": "Select",
  "inputs": { "from": "@body('Source_Array')", "select": "@item()?['key']" }
}
"Filter_To_Delete": {
  "type": "Query",
  "inputs": {
    "from": "@outputs('Get_Dest_Items')?['body/value']",
    "where": "@not(contains(body('Select_Source_Keys'), item()?['Title']))"
  }
}
// → Apply to each Filter_To_Delete → DeleteItem
```

> **Why this beats nested loops**: the naive approach (for each dest item, scan source)
> is O(n × m) and hits Power Automate's 100k-action run limit fast on large lists.
> This pattern is O(n + m): one pass to build key arrays, one pass per filter.
> The update loop in Step 6 only iterates *changed* records — often a tiny fraction
> of the full collection. Run Steps 2/4/7 in **parallel Scopes** for further speed.

---

### First-or-Null Single-Row Lookup

Use `first()` on the result array to extract one record without a loop.
Then null-check the output to guard downstream actions.

```json
"Get_First_Match": {
  "type": "Compose",
  "runAfter": { "Get_SP_Items": ["Succeeded"] },
  "inputs": "@first(outputs('Get_SP_Items')?['body/value'])"
}
```

In a Condition, test for no-match with the **`@null` literal** (not `empty()`):

```json
"Condition": {
  "type": "If",
  "expression": {
    "not": {
      "equals": [
        "@outputs('Get_First_Match')",
        "@null"
      ]
    }
  }
}
```

Access fields on the matched row: `@outputs('Get_First_Match')?['FieldName']`

> Use this instead of `Apply to each` when you only need one matching record.
> `first()` on an empty array returns `null`; `empty()` is for arrays/strings,
> not scalars — using it on a `first()` result causes a runtime error.

---

## HTTP & Parsing

### HTTP Action (External API)

```json
"Call_External_API": {
  "type": "Http",
  "runAfter": {},
  "inputs": {
    "method": "POST",
    "uri": "https://api.example.com/endpoint",
    "headers": {
      "Content-Type": "application/json",
      "Authorization": "Bearer @{variables('apiToken')}"
    },
    "body": {
      "data": "@outputs('Compose_Payload')"
    },
    "retryPolicy": {
      "type": "Fixed",
      "count": 3,
      "interval": "PT10S"
    }
  }
}
```

Response reference: `@outputs('Call_External_API')?['body']`

#### Variant: ActiveDirectoryOAuth (Service-to-Service)

For calling APIs that require Azure AD client-credentials (e.g., Microsoft Graph),
use in-line OAuth instead of a Bearer token variable:

```json
"Call_Graph_API": {
  "type": "Http",
  "runAfter": {},
  "inputs": {
    "method": "GET",
    "uri": "https://graph.microsoft.com/v1.0/users?$search=\"employeeId:@{variables('Code')}\"&$select=id,displayName",
    "headers": {
      "Content-Type": "application/json",
      "ConsistencyLevel": "eventual"
    },
    "authentication": {
      "type": "ActiveDirectoryOAuth",
      "authority": "https://login.microsoftonline.com",
      "tenant": "<tenant-id>",
      "audience": "https://graph.microsoft.com",
      "clientId": "<app-registration-id>",
      "secret": "@parameters('graphClientSecret')"
    }
  }
}
```

> **When to use:** Calling Microsoft Graph, Azure Resource Manager, or any
> Azure AD-protected API from a flow without a premium connector.
>
> The `authentication` block handles the entire OAuth client-credentials flow
> transparently — no manual token acquisition step needed.
>
> `ConsistencyLevel: eventual` is required for Graph `$search` queries.
> Without it, `$search` returns 400.
>
> For PATCH/PUT writes, the same `authentication` block works — just change
> `method` and add a `body`.
>
> ⚠️ **Never hardcode `secret` inline.** Use `@parameters('graphClientSecret')`
> and declare it in the flow's `parameters` block (type `securestring`). This
> prevents the secret from appearing in run history or being readable via
> `get_live_flow`. Declare the parameter like:
> ```json
> "parameters": {
>   "graphClientSecret": { "type": "securestring", "defaultValue": "" }
> }
> ```
> Then pass the real value via the flow's connections or environment variables
> — never commit it to source control.

---

### HTTP Response (Return to Caller)

Used in HTTP-triggered flows to send a structured reply back to the caller.
Must run before the flow times out (default 2 min for synchronous HTTP).

```json
"Response": {
  "type": "Response",
  "runAfter": {},
  "inputs": {
    "statusCode": 200,
    "headers": {
      "Content-Type": "application/json"
    },
    "body": {
      "status": "success",
      "message": "@{outputs('Compose_Result')}"
    }
  }
}
```

> **PowerApps / low-code caller pattern**: always return `statusCode: 200` with a
> `status` field in the body (`"success"` / `"error"`). PowerApps HTTP actions
> do not handle non-2xx responses gracefully — the caller should inspect
> `body.status` rather than the HTTP status code.
>
> Use multiple Response actions — one per branch — so each path returns
> an appropriate message. Only one will execute per run.

---

### Child Flow Call (Parent→Child via HTTP POST)

Power Automate supports parent→child orchestration by calling a child flow's
HTTP trigger URL directly. The parent sends an HTTP POST and blocks until the
child returns a `Response` action. The child flow uses a `manual` (Request) trigger.

```json
// PARENT — call child flow and wait for its response
"Call_Child_Flow": {
  "type": "Http",
  "inputs": {
    "method": "POST",
    "uri": "https://prod-XX.australiasoutheast.logic.azure.com:443/workflows/<workflowId>/triggers/manual/paths/invoke?api-version=2016-06-01&sp=%2Ftriggers%2Fmanual%2Frun&sv=1.0&sig=<SAS>",
    "headers": { "Content-Type": "application/json" },
    "body": {
      "ID": "@triggerBody()?['ID']",
      "WeekEnd": "@triggerBody()?['WeekEnd']",
      "Payload": "@variables('dataArray')"
    },
    "retryPolicy": { "type": "none" }
  },
  "operationOptions": "DisableAsyncPattern",
  "runtimeConfiguration": {
    "contentTransfer": { "transferMode": "Chunked" }
  },
  "limit": { "timeout": "PT2H" }
}
```

```json
// CHILD — manual trigger receives the JSON body
// (trigger definition)
"manual": {
  "type": "Request",
  "kind": "Http",
  "inputs": {
    "schema": {
      "type": "object",
      "properties": {
        "ID": { "type": "string" },
        "WeekEnd": { "type": "string" },
        "Payload": { "type": "array" }
      }
    }
  }
}

// CHILD — return result to parent
"Response_Success": {
  "type": "Response",
  "inputs": {
    "statusCode": 200,
    "headers": { "Content-Type": "application/json" },
    "body": { "Result": "Success", "Count": "@length(variables('processed'))" }
  }
}
```

> **`retryPolicy: none`** — critical on the parent's HTTP call. Without it, a child
> flow timeout triggers retries, spawning duplicate child runs.
>
> **`DisableAsyncPattern`** — prevents the parent from treating a 202 Accepted as
> completion. The parent will block until the child sends its `Response`.
>
> **`transferMode: Chunked`** — enable when passing large arrays (>100 KB) to the child;
> avoids request-size limits.
>
> **`limit.timeout: PT2H`** — raise the default 2-minute HTTP timeout for long-running
> children. Max is PT24H.
>
> The child flow's trigger URL contains a SAS token (`sig=...`) that authenticates
> the call. Copy it from the child flow's trigger properties panel. The URL changes
> if the trigger is deleted and re-created.

---

### Parse JSON

```json
"Parse_Response": {
  "type": "ParseJson",
  "runAfter": {},
  "inputs": {
    "content": "@outputs('Call_External_API')?['body']",
    "schema": {
      "type": "object",
      "properties": {
        "id": { "type": "integer" },
        "name": { "type": "string" },
        "items": {
          "type": "array",
          "items": { "type": "object" }
        }
      }
    }
  }
}
```

Access parsed values: `@body('Parse_Response')?['name']`

---

### Manual CSV → JSON (No Premium Action)

Parse a raw CSV string into an array of objects using only built-in expressions.
Avoids the premium "Parse CSV" connector action.

```json
"Delimiter": {
  "type": "Compose",
  "inputs": ","
},
"Strip_Quotes": {
  "type": "Compose",
  "inputs": "@replace(body('Get_File_Content'), '\"', '')"
},
"Detect_Line_Ending": {
  "type": "Compose",
  "inputs": "@if(equals(indexOf(outputs('Strip_Quotes'), decodeUriComponent('%0D%0A')), -1), if(equals(indexOf(outputs('Strip_Quotes'), decodeUriComponent('%0A')), -1), decodeUriComponent('%0D'), decodeUriComponent('%0A')), decodeUriComponent('%0D%0A'))"
},
"Headers": {
  "type": "Compose",
  "inputs": "@split(first(split(outputs('Strip_Quotes'), outputs('Detect_Line_Ending'))), outputs('Delimiter'))"
},
"Data_Rows": {
  "type": "Compose",
  "inputs": "@skip(split(outputs('Strip_Quotes'), outputs('Detect_Line_Ending')), 1)"
},
"Select_CSV_Body": {
  "type": "Select",
  "inputs": {
    "from": "@outputs('Data_Rows')",
    "select": {
      "@{outputs('Headers')[0]}": "@split(item(), outputs('Delimiter'))[0]",
      "@{outputs('Headers')[1]}": "@split(item(), outputs('Delimiter'))[1]",
      "@{outputs('Headers')[2]}": "@split(item(), outputs('Delimiter'))[2]"
    }
  }
},
"Filter_Empty_Rows": {
  "type": "Query",
  "inputs": {
    "from": "@body('Select_CSV_Body')",
    "where": "@not(equals(item()?[outputs('Headers')[0]], null))"
  }
}
```

Result: `@body('Filter_Empty_Rows')` — array of objects with header names as keys.

> **`Detect_Line_Ending`** handles CRLF (Windows), LF (Unix), and CR (old Mac) automatically
> using `indexOf()` with `decodeUriComponent('%0D%0A' / '%0A' / '%0D')`.
>
> **Dynamic key names in `Select`**: `@{outputs('Headers')[0]}` as a JSON key in a
> `Select` shape sets the output property name at runtime from the header row —
> this works as long as the expression is in `@{...}` interpolation syntax.
>
> **Columns with embedded commas**: if field values can contain the delimiter,
> use `length(split(row, ','))` in a Switch to detect the column count and manually
> reassemble the split fragments: `@concat(split(item(),',')[1],',',split(item(),',')[2])`

---

### ConvertTimeZone (Built-in, No Connector)

Converts a timestamp between timezones with no API call or connector licence cost.
Format string `"g"` produces short locale date+time (`M/d/yyyy h:mm tt`).

```json
"Convert_to_Local_Time": {
  "type": "Expression",
  "kind": "ConvertTimeZone",
  "runAfter": {},
  "inputs": {
    "baseTime": "@{outputs('UTC_Timestamp')}",
    "sourceTimeZone": "UTC",
    "destinationTimeZone": "Taipei Standard Time",
    "formatString": "g"
  }
}
```

Result reference: `@body('Convert_to_Local_Time')` — **not** `outputs()`, unlike most actions.

Common `formatString` values: `"g"` (short), `"f"` (full), `"yyyy-MM-dd"`, `"HH:mm"`

Common timezone strings: `"UTC"`, `"AUS Eastern Standard Time"`, `"Taipei Standard Time"`,
`"Singapore Standard Time"`, `"GMT Standard Time"`

> This is `type: Expression, kind: ConvertTimeZone` — a built-in Logic Apps action,
> not a connector. No connection reference needed. Reference the output via
> `body()` (not `outputs()`), otherwise the expression returns null.
