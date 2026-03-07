# Common Build Patterns

Complete flow definition templates ready to copy and customize.

---

## Pattern: Recurrence + SharePoint list read + Teams notification

```json
{
  "triggers": {
    "Recurrence": {
      "type": "Recurrence",
      "recurrence": { "frequency": "Day", "interval": 1,
                       "startTime": "2026-01-01T08:00:00Z",
                       "timeZone": "AUS Eastern Standard Time" }
    }
  },
  "actions": {
    "Get_SP_Items": {
      "type": "OpenApiConnection",
      "runAfter": {},
      "inputs": {
        "host": {
          "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
          "connectionName": "shared_sharepointonline",
          "operationId": "GetItems"
        },
        "parameters": {
          "dataset": "https://mytenant.sharepoint.com/sites/mysite",
          "table": "MyList",
          "$filter": "Status eq 'Active'",
          "$top": 500
        }
      }
    },
    "Apply_To_Each": {
      "type": "Foreach",
      "runAfter": { "Get_SP_Items": ["Succeeded"] },
      "foreach": "@outputs('Get_SP_Items')?['body/value']",
      "actions": {
        "Post_Teams_Message": {
          "type": "OpenApiConnection",
          "runAfter": {},
          "inputs": {
            "host": {
              "apiId": "/providers/Microsoft.PowerApps/apis/shared_teams",
              "connectionName": "shared_teams",
              "operationId": "PostMessageToConversation"
            },
            "parameters": {
              "poster": "Flow bot",
              "location": "Channel",
              "body/recipient": {
                "groupId": "<team-id>",
                "channelId": "<channel-id>"
              },
              "body/messageBody": "Item: @{items('Apply_To_Each')?['Title']}"
            }
          }
        }
      },
      "operationOptions": "Sequential"
    }
  }
}
```

---

## Pattern: HTTP trigger (webhook / Power App call)

```json
{
  "triggers": {
    "manual": {
      "type": "Request",
      "kind": "Http",
      "inputs": {
        "schema": {
          "type": "object",
          "properties": {
            "name": { "type": "string" },
            "value": { "type": "number" }
          }
        }
      }
    }
  },
  "actions": {
    "Compose_Response": {
      "type": "Compose",
      "runAfter": {},
      "inputs": "Received: @{triggerBody()?['name']} = @{triggerBody()?['value']}"
    },
    "Response": {
      "type": "Response",
      "runAfter": { "Compose_Response": ["Succeeded"] },
      "inputs": {
        "statusCode": 200,
        "body": { "status": "ok", "message": "@{outputs('Compose_Response')}" }
      }
    }
  }
}
```

Access body values: `@triggerBody()?['name']`
