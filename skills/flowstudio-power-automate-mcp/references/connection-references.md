# FlowStudio MCP — Connection References

Connection references wire a flow's connector actions to real authenticated
connections in the Power Platform. They are required whenever you call
`update_live_flow` with a definition that uses connector actions.

---

## Structure in a Flow Definition

```json
{
  "properties": {
    "definition": { ... },
    "connectionReferences": {
      "shared_sharepointonline": {
        "connectionName": "shared-sharepointonl-eeeeeeeeee-eeee-eeee-eeee-eeeeeeeeeeee",
        "id": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
        "displayName": "SharePoint"
      },
      "shared_office365": {
        "connectionName": "shared-office365-xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx",
        "id": "/providers/Microsoft.PowerApps/apis/shared_office365",
        "displayName": "Office 365 Outlook"
      }
    }
  }
}
```

Keys are **logical reference names** (e.g. `shared_sharepointonline`).
These match the `connectionName` field inside each action's `host` block.

---

## Finding Connection References

Preferred method: call `list_live_connections` in the target environment. Use
`search` to narrow results to the connector you need; newer MCP server versions
return paste-ready templates.

```python
matches = mcp("list_live_connections",
    environmentName=ENV,
    search="shared_sharepointonline")

conn = next(c for c in matches["connections"]
            if c.get("overallStatus") == "Connected"
            or c.get("statuses", [{}])[0].get("status") == "Connected")

conn_refs = {
    "shared_sharepointonline": conn.get("connectionReferenceTemplate") or {
        "connectionName": conn["id"],
        "id": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
        "source": "Invoker"
    }
}
host = conn.get("hostTemplate") or {"connectionName": "shared_sharepointonline"}
```

Use `host` as the action-side `inputs.host`. Use `conn_refs` as
`update_live_flow(connectionReferences=conn_refs)`.

Fallback method: copy from an existing flow.

Call `get_live_flow` on **any existing flow** that uses the same connection
and copy the `connectionReferences` block. The GUID after the connector prefix is
the connection instance owned by the authenticating user.

```python
flow = mcp("get_live_flow", environmentName=ENV, flowName=EXISTING_FLOW_ID)
conn_refs = flow["properties"]["connectionReferences"]
# conn_refs["shared_sharepointonline"]["connectionName"]
# → "shared-sharepointonl-eeeeeeeeee-eeee-eeee-eeee-eeeeeeeeeeee"
```

> ⚠️ Connection references are **user-scoped**. If a connection is owned
> by another account, `update_live_flow` will return 403
> `ConnectionAuthorizationFailed`. You must use a connection belonging to
> the account whose token is in the `x-api-key` header.

---

## Passing `connectionReferences` to `update_live_flow`

```python
result = mcp("update_live_flow",
    environmentName=ENV,
    flowName=FLOW_ID,
    definition=modified_definition,
    connectionReferences={
        "shared_sharepointonline": {
            "connectionName": "shared-sharepointonl-eeeeeeeeee-eeee-eeee-eeee-eeeeeeeeeeee",
            "id": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline"
        }
    }
)
```

Only include connections that the definition actually uses.

---

## Common Connector API IDs

| Service | API ID |
|---|---|
| SharePoint Online | `/providers/Microsoft.PowerApps/apis/shared_sharepointonline` |
| Office 365 Outlook | `/providers/Microsoft.PowerApps/apis/shared_office365` |
| Microsoft Teams | `/providers/Microsoft.PowerApps/apis/shared_teams` |
| OneDrive for Business | `/providers/Microsoft.PowerApps/apis/shared_onedriveforbusiness` |
| Azure AD | `/providers/Microsoft.PowerApps/apis/shared_azuread` |
| HTTP with Azure AD | `/providers/Microsoft.PowerApps/apis/shared_webcontents` |
| SQL Server | `/providers/Microsoft.PowerApps/apis/shared_sql` |
| Dataverse | `/providers/Microsoft.PowerApps/apis/shared_commondataserviceforapps` |
| Azure Blob Storage | `/providers/Microsoft.PowerApps/apis/shared_azureblob` |
| Approvals | `/providers/Microsoft.PowerApps/apis/shared_approvals` |
| Office 365 Users | `/providers/Microsoft.PowerApps/apis/shared_office365users` |
| Flow Management | `/providers/Microsoft.PowerApps/apis/shared_flowmanagement` |

---

## Teams Adaptive Card Dual-Connection Requirement

Flows that send adaptive cards **and** post follow-up messages require two
separate Teams connections:

```json
"connectionReferences": {
  "shared_teams": {
    "connectionName": "shared-teams-xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx",
    "id": "/providers/Microsoft.PowerApps/apis/shared_teams"
  },
  "shared_teams_1": {
    "connectionName": "shared-teams-yyyyyyyy-yyyy-yyyy-yyyy-yyyyyyyyyyyy",
    "id": "/providers/Microsoft.PowerApps/apis/shared_teams"
  }
}
```

Both can point to the **same underlying Teams account** but must be registered
as two distinct connection references. The webhook (`OpenApiConnectionWebhook`)
uses `shared_teams` and subsequent message actions use `shared_teams_1`.
