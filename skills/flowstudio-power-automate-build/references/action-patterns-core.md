# FlowStudio MCP — Action Patterns: Core

Variables, control flow, and expression patterns for Power Automate flow definitions.

> All examples assume `"runAfter"` is set appropriately.
> Replace `<connectionName>` with the **key** you used in your `connectionReferences` map
> (e.g. `shared_teams`, `shared_office365`) — NOT the connection GUID.

---

## Data & Variables

### Compose (Store a Value)

```json
"Compose_My_Value": {
  "type": "Compose",
  "runAfter": {},
  "inputs": "@variables('myVar')"
}
```

Reference: `@outputs('Compose_My_Value')`

---

### Initialize Variable

```json
"Init_Counter": {
  "type": "InitializeVariable",
  "runAfter": {},
  "inputs": {
    "variables": [{
      "name": "counter",
      "type": "Integer",
      "value": 0
    }]
  }
}
```

Types: `"Integer"`, `"Float"`, `"Boolean"`, `"String"`, `"Array"`, `"Object"`

---

### Set Variable

```json
"Set_Counter": {
  "type": "SetVariable",
  "runAfter": {},
  "inputs": {
    "name": "counter",
    "value": "@add(variables('counter'), 1)"
  }
}
```

---

### Append to Array Variable

```json
"Collect_Item": {
  "type": "AppendToArrayVariable",
  "runAfter": {},
  "inputs": {
    "name": "resultArray",
    "value": "@item()"
  }
}
```

---

### Increment Variable

```json
"Increment_Counter": {
  "type": "IncrementVariable",
  "runAfter": {},
  "inputs": {
    "name": "counter",
    "value": 1
  }
}
```

> Use `IncrementVariable` (not `SetVariable` with `add()`) for counters inside loops —
> it is atomic and avoids expression errors when the variable is used elsewhere in the
> same iteration. `value` can be any integer or expression, e.g. `@mul(item()?['Interval'], 60)`
> to advance a Unix timestamp cursor by N minutes.

---

## Control Flow

### Condition (If/Else)

```json
"Check_Status": {
  "type": "If",
  "runAfter": {},
  "expression": {
    "and": [{ "equals": ["@item()?['Status']", "Active"] }]
  },
  "actions": {
    "Handle_Active": {
      "type": "Compose",
      "runAfter": {},
      "inputs": "Active user: @{item()?['Name']}"
    }
  },
  "else": {
    "actions": {
      "Handle_Inactive": {
        "type": "Compose",
        "runAfter": {},
        "inputs": "Inactive user"
      }
    }
  }
}
```

Comparison operators: `equals`, `not`, `greater`, `greaterOrEquals`, `less`, `lessOrEquals`, `contains`  
Logical: `and: [...]`, `or: [...]`

---

### Switch

```json
"Route_By_Type": {
  "type": "Switch",
  "runAfter": {},
  "expression": "@triggerBody()?['type']",
  "cases": {
    "Case_Email": {
      "case": "email",
      "actions": { "Process_Email": { "type": "Compose", "runAfter": {}, "inputs": "email" } }
    },
    "Case_Teams": {
      "case": "teams",
      "actions": { "Process_Teams": { "type": "Compose", "runAfter": {}, "inputs": "teams" } }
    }
  },
  "default": {
    "actions": { "Unknown_Type": { "type": "Compose", "runAfter": {}, "inputs": "unknown" } }
  }
}
```

---

### Scope (Grouping / Try-Catch)

Wrap related actions in a Scope to give them a shared name, collapse them in the
designer, and — most importantly — handle their errors as a unit.

```json
"Scope_Get_Customer": {
  "type": "Scope",
  "runAfter": {},
  "actions": {
    "HTTP_Get_Customer": {
      "type": "Http",
      "runAfter": {},
      "inputs": {
        "method": "GET",
        "uri": "https://api.example.com/customers/@{variables('customerId')}"
      }
    },
    "Compose_Email": {
      "type": "Compose",
      "runAfter": { "HTTP_Get_Customer": ["Succeeded"] },
      "inputs": "@outputs('HTTP_Get_Customer')?['body/email']"
    }
  }
},
"Handle_Scope_Error": {
  "type": "Compose",
  "runAfter": { "Scope_Get_Customer": ["Failed", "TimedOut"] },
  "inputs": "Scope failed: @{result('Scope_Get_Customer')?[0]?['error']?['message']}"
}
```

> Reference scope results: `@result('Scope_Get_Customer')` returns an array of action
> outcomes. Use `runAfter: {"MyScope": ["Failed", "TimedOut"]}` on a follow-up action
> to create try/catch semantics without a Terminate.

---

### Foreach (Sequential)

```json
"Process_Each_Item": {
  "type": "Foreach",
  "runAfter": {},
  "foreach": "@outputs('Get_Items')?['body/value']",
  "operationOptions": "Sequential",
  "actions": {
    "Handle_Item": {
      "type": "Compose",
      "runAfter": {},
      "inputs": "@item()?['Title']"
    }
  }
}
```

> Always include `"operationOptions": "Sequential"` unless parallel is intentional.

---

### Foreach (Parallel with Concurrency Limit)

```json
"Process_Each_Item_Parallel": {
  "type": "Foreach",
  "runAfter": {},
  "foreach": "@body('Get_SP_Items')?['value']",
  "runtimeConfiguration": {
    "concurrency": {
      "repetitions": 20
    }
  },
  "actions": {
    "HTTP_Upsert": {
      "type": "Http",
      "runAfter": {},
      "inputs": {
        "method": "POST",
        "uri": "https://api.example.com/contacts/@{item()?['Email']}"
      }
    }
  }
}
```

> Set `repetitions` to control how many items are processed simultaneously.
> Practical values: `5–10` for external API calls (respect rate limits),
> `20–50` for internal/fast operations.
> Omit `runtimeConfiguration.concurrency` entirely for the platform default
> (currently 50). Do NOT use `"operationOptions": "Sequential"` and concurrency together.

---

### Wait (Delay)

```json
"Delay_10_Minutes": {
  "type": "Wait",
  "runAfter": {},
  "inputs": {
    "interval": {
      "count": 10,
      "unit": "Minute"
    }
  }
}
```

Valid `unit` values: `"Second"`, `"Minute"`, `"Hour"`, `"Day"`

> Use a Delay + re-fetch as a deduplication guard: wait for any competing process
> to complete, then re-read the record before acting. This avoids double-processing
> when multiple triggers or manual edits can race on the same item.

---

### Terminate (Success or Failure)

```json
"Terminate_Success": {
  "type": "Terminate",
  "runAfter": {},
  "inputs": {
    "runStatus": "Succeeded"
  }
},
"Terminate_Failure": {
  "type": "Terminate",
  "runAfter": { "Risky_Action": ["Failed"] },
  "inputs": {
    "runStatus": "Failed",
    "runError": {
      "code": "StepFailed",
      "message": "@{outputs('Get_Error_Message')}"
    }
  }
}
```

---

### Do Until (Loop Until Condition)

Repeats a block of actions until an exit condition becomes true.
Use when the number of iterations is not known upfront (e.g. paginating an API,
walking a time range, polling until a status changes).

```json
"Do_Until_Done": {
  "type": "Until",
  "runAfter": {},
  "expression": "@greaterOrEquals(variables('cursor'), variables('endValue'))",
  "limit": {
    "count": 5000,
    "timeout": "PT5H"
  },
  "actions": {
    "Do_Work": {
      "type": "Compose",
      "runAfter": {},
      "inputs": "@variables('cursor')"
    },
    "Advance_Cursor": {
      "type": "IncrementVariable",
      "runAfter": { "Do_Work": ["Succeeded"] },
      "inputs": {
        "name": "cursor",
        "value": 1
      }
    }
  }
}
```

> Always set `limit.count` and `limit.timeout` explicitly — the platform defaults are
> low (60 iterations, 1 hour). For time-range walkers use `limit.count: 5000` and
> `limit.timeout: "PT5H"` (ISO 8601 duration).
>
> The exit condition is evaluated **before** each iteration. Initialise your cursor
> variable before the loop so the condition can evaluate correctly on the first pass.

---

### Async Polling with RequestId Correlation

When an API starts a long-running job asynchronously (e.g. Power BI dataset refresh,
report generation, batch export), the trigger call returns a request ID. Capture it
from the **response header**, then poll a status endpoint filtering by that exact ID:

```json
"Start_Job": {
  "type": "Http",
  "inputs": { "method": "POST", "uri": "https://api.example.com/jobs" }
},
"Capture_Request_ID": {
  "type": "Compose",
  "runAfter": { "Start_Job": ["Succeeded"] },
  "inputs": "@outputs('Start_Job')?['headers/X-Request-Id']"
},
"Initialize_Status": {
  "type": "InitializeVariable",
  "inputs": { "variables": [{ "name": "jobStatus", "type": "String", "value": "Running" }] }
},
"Poll_Until_Done": {
  "type": "Until",
  "expression": "@not(equals(variables('jobStatus'), 'Running'))",
  "limit": { "count": 60, "timeout": "PT30M" },
  "actions": {
    "Delay": { "type": "Wait", "inputs": { "interval": { "count": 20, "unit": "Second" } } },
    "Get_History": {
      "type": "Http",
      "runAfter": { "Delay": ["Succeeded"] },
      "inputs": { "method": "GET", "uri": "https://api.example.com/jobs/history" }
    },
    "Filter_This_Job": {
      "type": "Query",
      "runAfter": { "Get_History": ["Succeeded"] },
      "inputs": {
        "from": "@outputs('Get_History')?['body/items']",
        "where": "@equals(item()?['requestId'], outputs('Capture_Request_ID'))"
      }
    },
    "Set_Status": {
      "type": "SetVariable",
      "runAfter": { "Filter_This_Job": ["Succeeded"] },
      "inputs": {
        "name": "jobStatus",
        "value": "@first(body('Filter_This_Job'))?['status']"
      }
    }
  }
},
"Handle_Failure": {
  "type": "If",
  "runAfter": { "Poll_Until_Done": ["Succeeded"] },
  "expression": { "equals": ["@variables('jobStatus')", "Failed"] },
  "actions": { "Terminate_Failed": { "type": "Terminate", "inputs": { "runStatus": "Failed" } } },
  "else": { "actions": {} }
}
```

Access response headers: `@outputs('Start_Job')?['headers/X-Request-Id']`

> **Status variable initialisation**: set a sentinel value (`"Running"`, `"Unknown"`) before
> the loop. The exit condition tests for any value other than the sentinel.
> This way an empty poll result (job not yet in history) leaves the variable unchanged
> and the loop continues — it doesn't accidentally exit on null.
>
> **Filter before extracting**: always `Filter Array` the history to your specific
> request ID before calling `first()`. History endpoints return all jobs; without
> filtering, status from a different concurrent job can corrupt your poll.

---

### runAfter Fallback (Failed → Alternative Action)

Route to a fallback action when a primary action fails — without a Condition block.
Simply set `runAfter` on the fallback to accept `["Failed"]` from the primary:

```json
"HTTP_Get_Hi_Res": {
  "type": "Http",
  "runAfter": {},
  "inputs": { "method": "GET", "uri": "https://api.example.com/data?resolution=hi-res" }
},
"HTTP_Get_Low_Res": {
  "type": "Http",
  "runAfter": { "HTTP_Get_Hi_Res": ["Failed"] },
  "inputs": { "method": "GET", "uri": "https://api.example.com/data?resolution=low-res" }
}
```

> Actions that follow can use `runAfter` accepting both `["Succeeded", "Skipped"]` to
> handle either path — see **Fan-In Join Gate** below.

---

### Fan-In Join Gate (Merge Two Mutually Exclusive Branches)

When two branches are mutually exclusive (only one can succeed per run), use a single
downstream action that accepts `["Succeeded", "Skipped"]` from **both** branches.
The gate fires exactly once regardless of which branch ran:

```json
"Increment_Count": {
  "type": "IncrementVariable",
  "runAfter": {
    "Update_Hi_Res_Metadata":  ["Succeeded", "Skipped"],
    "Update_Low_Res_Metadata": ["Succeeded", "Skipped"]
  },
  "inputs": { "name": "LoopCount", "value": 1 }
}
```

> This avoids duplicating the downstream action in each branch. The key insight:
> whichever branch was skipped reports `Skipped` — the gate accepts that state and
> fires once. Only works cleanly when the two branches are truly mutually exclusive
> (e.g. one is `runAfter: [...Failed]` of the other).

---

## Expressions

### Common Expression Patterns

```
Null-safe field access:    @item()?['FieldName']
Null guard:                @coalesce(item()?['Name'], 'Unknown')
String format:             @{variables('firstName')} @{variables('lastName')}
Date today:                @utcNow()
Formatted date:            @formatDateTime(utcNow(), 'dd/MM/yyyy')
Add days:                  @addDays(utcNow(), 7)
Array length:              @length(variables('myArray'))
Filter array:              Use the "Filter array" action (no inline filter expression exists in PA)
Union (new wins):          @union(body('New_Data'), outputs('Old_Data'))
Sort:                      @sort(variables('myArray'), 'Date')
Unix timestamp → date:     @formatDateTime(addseconds('1970-1-1', triggerBody()?['created']), 'yyyy-MM-dd')
Date → Unix milliseconds:  @div(sub(ticks(startOfDay(item()?['Created'])), ticks(formatDateTime('1970-01-01Z','o'))), 10000)
Date → Unix seconds:       @div(sub(ticks(item()?['Start']), ticks('1970-01-01T00:00:00Z')), 10000000)
Unix seconds → datetime:   @addSeconds('1970-01-01T00:00:00Z', int(variables('Unix')))
Coalesce as no-else:       @coalesce(outputs('Optional_Step'), outputs('Default_Step'))
Flow elapsed minutes:      @div(float(sub(ticks(utcNow()), ticks(outputs('Flow_Start')))), 600000000)
HH:mm time string:         @formatDateTime(outputs('Local_Datetime'), 'HH:mm')
Response header:           @outputs('HTTP_Action')?['headers/X-Request-Id']
Array max (by field):      @reverse(sort(body('Select_Items'), 'Date'))[0]
Integer day span:          @int(split(dateDifference(outputs('Start'), outputs('End')), '.')[0])
ISO week number:           @div(add(dayofyear(addDays(subtractFromTime(date, sub(dayofweek(date),1), 'Day'), 3)), 6), 7)
Join errors to string:     @if(equals(length(variables('Errors')),0), null, concat(join(variables('Errors'),', '),' not found.'))
Normalize before compare:  @replace(coalesce(outputs('Value'),''),'_',' ')
Robust non-empty check:    @greater(length(trim(coalesce(string(outputs('Val')), ''))), 0)
```

### Newlines in Expressions

> **`\n` does NOT produce a newline inside Power Automate expressions.** It is
> treated as a literal backslash + `n` and will either appear verbatim or cause
> a validation error.

Use `decodeUriComponent('%0a')` wherever you need a newline character:

```
Newline (LF):   decodeUriComponent('%0a')
CRLF:           decodeUriComponent('%0d%0a')
```

Example — multi-line Teams or email body via `concat()`:
```json
"Compose_Message": {
  "type": "Compose",
  "inputs": "@concat('Hi ', outputs('Get_User')?['body/displayName'], ',', decodeUriComponent('%0a%0a'), 'Your report is ready.', decodeUriComponent('%0a'), '- The Team')"
}
```

Example — `join()` with newline separator:
```json
"Compose_List": {
  "type": "Compose",
  "inputs": "@join(body('Select_Names'), decodeUriComponent('%0a'))"
}
```

> This is the only reliable way to embed newlines in dynamically built strings
> in Power Automate flow definitions (confirmed against Logic Apps runtime).

---

### Sum an array (XPath trick)

Power Automate has no native `sum()` function. Use XPath on XML instead:

```json
"Prepare_For_Sum": {
  "type": "Compose",
  "runAfter": {},
  "inputs": { "root": { "numbers": "@body('Select_Amounts')" } }
},
"Sum": {
  "type": "Compose",
  "runAfter": { "Prepare_For_Sum": ["Succeeded"] },
  "inputs": "@xpath(xml(outputs('Prepare_For_Sum')), 'sum(/root/numbers)')"
}
```

`Select_Amounts` must output a flat array of numbers (use a **Select** action to extract a single numeric field first). The result is a number you can use directly in conditions or calculations.

> This is the only way to aggregate (sum/min/max) an array without a loop in Power Automate.
