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
        "connectionName": "shared-sharepointonl-62599557c-1f33-4aec-b4c0-a6e4afcae3be",
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

## Finding Connection GUIDs

Call `get_live_flow` on **any existing flow** that uses the same connection
and copy the `connectionReferences` block. The GUID after the connector prefix is
the connection instance owned by the authenticating user.

```python
flow = mcp("get_live_flow", environmentName=ENV, flowName=EXISTING_FLOW_ID)
conn_refs = flow["properties"]["connectionReferences"]
# conn_refs["shared_sharepointonline"]["connectionName"]
# → "shared-sharepointonl-62599557c-1f33-4aec-b4c0-a6e4afcae3be"
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
            "connectionName": "shared-sharepointonl-62599557c-1f33-4aec-b4c0-a6e4afcae3be",
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
