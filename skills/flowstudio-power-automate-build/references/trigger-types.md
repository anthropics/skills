# FlowStudio MCP — Trigger Types

Copy-paste trigger definitions for Power Automate flow definitions.

---

## Recurrence

Run on a schedule.

```json
"Recurrence": {
  "type": "Recurrence",
  "recurrence": {
    "frequency": "Day",
    "interval": 1,
    "startTime": "2026-01-01T08:00:00Z",
    "timeZone": "AUS Eastern Standard Time"
  }
}
```

Weekly on specific days:
```json
"Recurrence": {
  "type": "Recurrence",
  "recurrence": {
    "frequency": "Week",
    "interval": 1,
    "schedule": {
      "weekDays": ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    },
    "startTime": "2026-01-05T09:00:00Z",
    "timeZone": "AUS Eastern Standard Time"
  }
}
```

Common `timeZone` values:
- `"AUS Eastern Standard Time"` — Sydney/Melbourne (UTC+10/+11)
- `"UTC"` — Universal time
- `"E. Australia Standard Time"` — Brisbane (UTC+10 no DST)
- `"New Zealand Standard Time"` — Auckland (UTC+12/+13)
- `"Pacific Standard Time"` — Los Angeles (UTC-8/-7)
- `"GMT Standard Time"` — London (UTC+0/+1)

---

## Manual (HTTP Request / Power Apps)

Receive an HTTP POST with a JSON body.

```json
"manual": {
  "type": "Request",
  "kind": "Http",
  "inputs": {
    "schema": {
      "type": "object",
      "properties": {
        "name": { "type": "string" },
        "value": { "type": "integer" }
      },
      "required": ["name"]
    }
  }
}
```

Access values: `@triggerBody()?['name']`  
Trigger URL available after saving: `@listCallbackUrl()`

#### No-Schema Variant (Accept Arbitrary JSON)

When the incoming payload structure is unknown or varies, omit the schema
to accept any valid JSON body without validation:

```json
"manual": {
  "type": "Request",
  "kind": "Http",
  "inputs": {
    "schema": {}
  }
}
```

Access any field dynamically: `@triggerBody()?['anyField']`

> Use this for external webhooks (Stripe, GitHub, Employment Hero, etc.) where the
> payload shape may change or is not fully documented. The flow accepts any
> JSON without returning 400 for unexpected properties.

---

## Automated (SharePoint Item Created)

```json
"When_an_item_is_created": {
  "type": "OpenApiConnectionNotification",
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "OnNewItem"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "table": "MyList"
    },
    "subscribe": {
      "body": { "notificationUrl": "@listCallbackUrl()" },
      "queries": {
        "dataset": "https://mytenant.sharepoint.com/sites/mysite",
        "table": "MyList"
      }
    }
  }
}
```

Access trigger data: `@triggerBody()?['ID']`, `@triggerBody()?['Title']`, etc.

---

## Automated (SharePoint Item Modified)

```json
"When_an_existing_item_is_modified": {
  "type": "OpenApiConnectionNotification",
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "OnUpdatedItem"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "table": "MyList"
    },
    "subscribe": {
      "body": { "notificationUrl": "@listCallbackUrl()" },
      "queries": {
        "dataset": "https://mytenant.sharepoint.com/sites/mysite",
        "table": "MyList"
      }
    }
  }
}
```

---

## Automated (Outlook: When New Email Arrives)

```json
"When_a_new_email_arrives": {
  "type": "OpenApiConnectionNotification",
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_office365",
      "connectionName": "<connectionName>",
      "operationId": "OnNewEmail"
    },
    "parameters": {
      "folderId": "Inbox",
      "to": "monitored@contoso.com",
      "isHTML": true
    },
    "subscribe": {
      "body": { "notificationUrl": "@listCallbackUrl()" }
    }
  }
}
```

---

## Child Flow (Called by Another Flow)

```json
"manual": {
  "type": "Request",
  "kind": "Button",
  "inputs": {
    "schema": {
      "type": "object",
      "properties": {
        "items": {
          "type": "array",
          "items": { "type": "object" }
        }
      }
    }
  }
}
```

Access parent-supplied data: `@triggerBody()?['items']`

To return data to the parent, add a `Response` action:
```json
"Respond_to_Parent": {
  "type": "Response",
  "runAfter": { "Compose_Result": ["Succeeded"] },
  "inputs": {
    "statusCode": 200,
    "body": "@outputs('Compose_Result')"
  }
}
```
