# FlowStudio MCP — Action Patterns: Connectors

SharePoint, Outlook, Teams, and Approvals connector action patterns.

> All examples assume `"runAfter"` is set appropriately.
> Replace `<connectionName>` with the **key** you used in `connectionReferences`
> (e.g. `shared_sharepointonline`, `shared_teams`). This is NOT the connection
> GUID — it is the logical reference name that links the action to its entry in
> the `connectionReferences` map.

---

## SharePoint

### SharePoint — Get Items

```json
"Get_SP_Items": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "GetItems"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "table": "MyList",
      "$filter": "Status eq 'Active'",
      "$top": 500
    }
  }
}
```

Result reference: `@outputs('Get_SP_Items')?['body/value']`

> **Dynamic OData filter with string interpolation**: inject a runtime value
> directly into the `$filter` string using `@{...}` syntax:
> ```
> "$filter": "Title eq '@{outputs('ConfirmationCode')}'"  
> ```
> Note the single-quotes inside double-quotes — correct OData string literal
> syntax. Avoids a separate variable action.

> **Pagination for large lists**: by default, GetItems stops at `$top`. To auto-paginate
> beyond that, enable the pagination policy on the action. In the flow definition this
> appears as:
> ```json
> "paginationPolicy": { "minimumItemCount": 10000 }
> ```
> Set `minimumItemCount` to the maximum number of items you expect. The connector will
> keep fetching pages until that count is reached or the list is exhausted. Without this,
> flows silently return a capped result on lists with >5,000 items.

---

### SharePoint — Get Item (Single Row by ID)

```json
"Get_SP_Item": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "GetItem"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "table": "MyList",
      "id": "@triggerBody()?['ID']"
    }
  }
}
```

Result reference: `@body('Get_SP_Item')?['FieldName']`

> Use `GetItem` (not `GetItems` with a filter) when you already have the ID.
> Re-fetching after a trigger gives you the **current** row state, not the
> snapshot captured at trigger time — important if another process may have
> modified the item since the flow started.

---

### SharePoint — Create Item

```json
"Create_SP_Item": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "PostItem"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "table": "MyList",
      "item/Title": "@variables('myTitle')",
      "item/Status": "Active"
    }
  }
}
```

---

### SharePoint — Update Item

```json
"Update_SP_Item": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "PatchItem"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "table": "MyList",
      "id": "@item()?['ID']",
      "item/Status": "Processed"
    }
  }
}
```

---

### SharePoint — File Upsert (Create or Overwrite in Document Library)

SharePoint's `CreateFile` fails if the file already exists. To upsert (create or overwrite)
without a prior existence check, use `GetFileMetadataByPath` on **both Succeeded and Failed**
from `CreateFile` — if create failed because the file exists, the metadata call still
returns its ID, which `UpdateFile` can then overwrite:

```json
"Create_File": {
  "type": "OpenApiConnection",
  "inputs": {
    "host": { "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
              "connectionName": "<connectionName>", "operationId": "CreateFile" },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "folderPath": "/My Library/Subfolder",
      "name": "@{variables('filename')}",
      "body": "@outputs('Compose_File_Content')"
    }
  }
},
"Get_File_Metadata_By_Path": {
  "type": "OpenApiConnection",
  "runAfter": { "Create_File": ["Succeeded", "Failed"] },
  "inputs": {
    "host": { "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
              "connectionName": "<connectionName>", "operationId": "GetFileMetadataByPath" },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "path": "/My Library/Subfolder/@{variables('filename')}"
    }
  }
},
"Update_File": {
  "type": "OpenApiConnection",
  "runAfter": { "Get_File_Metadata_By_Path": ["Succeeded", "Skipped"] },
  "inputs": {
    "host": { "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
              "connectionName": "<connectionName>", "operationId": "UpdateFile" },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "id": "@outputs('Get_File_Metadata_By_Path')?['body/{Identifier}']",
      "body": "@outputs('Compose_File_Content')"
    }
  }
}
```

> If `Create_File` succeeds, `Get_File_Metadata_By_Path` is `Skipped` and `Update_File`
> still fires (accepting `Skipped`), harmlessly overwriting the file just created.
> If `Create_File` fails (file exists), the metadata call retrieves the existing file's ID
> and `Update_File` overwrites it. Either way you end with the latest content.
>
> **Document library system properties** — when iterating a file library result (e.g.
> from `ListFolder` or `GetFilesV2`), use curly-brace property names to access
> SharePoint's built-in file metadata. These are different from list field names:
> ```
> @item()?['{Name}']                  — filename without path (e.g. "report.csv")
> @item()?['{FilenameWithExtension}'] — same as {Name} in most connectors
> @item()?['{Identifier}']            — internal file ID for use in UpdateFile/DeleteFile
> @item()?['{FullPath}']              — full server-relative path
> @item()?['{IsFolder}']             — boolean, true for folder entries
> ```

---

### SharePoint — GetItemChanges Column Gate

When a SharePoint "item modified" trigger fires, it doesn't tell you WHICH
column changed. Use `GetItemChanges` to get per-column change flags, then gate
downstream logic on specific columns:

```json
"Get_Changes": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "GetItemChanges"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "table": "<list-guid>",
      "id": "@triggerBody()?['ID']",
      "since": "@triggerBody()?['Modified']",
      "includeDrafts": false
    }
  }
}
```

Gate on a specific column:

```json
"expression": {
  "and": [{
    "equals": [
      "@body('Get_Changes')?['Column']?['hasChanged']",
      true
    ]
  }]
}
```

> **New-item detection:** On the very first modification (version 1.0),
> `GetItemChanges` may report no prior version. Check
> `@equals(triggerBody()?['OData__UIVersionString'], '1.0')` to detect
> newly created items and skip change-gate logic for those.

---

### SharePoint — REST MERGE via HttpRequest

For cross-list updates or advanced operations not supported by the standard
Update Item connector (e.g., updating a list in a different site), use the
SharePoint REST API via the `HttpRequest` operation:

```json
"Update_Cross_List_Item": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "HttpRequest"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/target-site",
      "parameters/method": "POST",
      "parameters/uri": "/_api/web/lists(guid'<list-guid>')/items(@{variables('ItemId')})",
      "parameters/headers": {
        "Accept": "application/json;odata=nometadata",
        "Content-Type": "application/json;odata=nometadata",
        "X-HTTP-Method": "MERGE",
        "IF-MATCH": "*"
      },
      "parameters/body": "{ \"Title\": \"@{variables('NewTitle')}\", \"Status\": \"@{variables('NewStatus')}\" }"
    }
  }
}
```

> **Key headers:**
> - `X-HTTP-Method: MERGE` — tells SharePoint to do a partial update (PATCH semantics)
> - `IF-MATCH: *` — overwrites regardless of current ETag (no conflict check)
>
> The `HttpRequest` operation reuses the existing SharePoint connection — no extra
> authentication needed. Use this when the standard Update Item connector can't
> reach the target list (different site collection, or you need raw REST control).

---

### SharePoint — File as JSON Database (Read + Parse)

Use a SharePoint document library JSON file as a queryable "database" of
last-known-state records. A separate process (e.g., Power BI dataflow) maintains
the file; the flow downloads and filters it for before/after comparisons.

```json
"Get_File": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_sharepointonline",
      "connectionName": "<connectionName>",
      "operationId": "GetFileContent"
    },
    "parameters": {
      "dataset": "https://mytenant.sharepoint.com/sites/mysite",
      "id": "%252fShared%2bDocuments%252fdata.json",
      "inferContentType": false
    }
  }
},
"Parse_JSON_File": {
  "type": "Compose",
  "runAfter": { "Get_File": ["Succeeded"] },
  "inputs": "@json(decodeBase64(body('Get_File')?['$content']))"
},
"Find_Record": {
  "type": "Query",
  "runAfter": { "Parse_JSON_File": ["Succeeded"] },
  "inputs": {
    "from": "@outputs('Parse_JSON_File')",
    "where": "@equals(item()?['id'], variables('RecordId'))"
  }
}
```

> **Decode chain:** `GetFileContent` returns base64-encoded content in
> `body(...)?['$content']`. Apply `decodeBase64()` then `json()` to get a
> usable array. `Filter Array` then acts as a WHERE clause.
>
> **When to use:** When you need a lightweight "before" snapshot to detect field
> changes from a webhook payload (the "after" state). Simpler than maintaining
> a full SharePoint list mirror — works well for up to ~10K records.
>
> **File path encoding:** In the `id` parameter, SharePoint URL-encodes paths
> twice. Spaces become `%2b` (plus sign), slashes become `%252f`.

---

## Outlook

### Outlook — Send Email

```json
"Send_Email": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_office365",
      "connectionName": "<connectionName>",
      "operationId": "SendEmailV2"
    },
    "parameters": {
      "emailMessage/To": "recipient@contoso.com",
      "emailMessage/Subject": "Automated notification",
      "emailMessage/Body": "<p>@{outputs('Compose_Message')}</p>",
      "emailMessage/IsHtml": true
    }
  }
}
```

---

### Outlook — Get Emails (Read Template from Folder)

```json
"Get_Email_Template": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_office365",
      "connectionName": "<connectionName>",
      "operationId": "GetEmailsV3"
    },
    "parameters": {
      "folderPath": "Id::<outlook-folder-id>",
      "fetchOnlyUnread": false,
      "includeAttachments": false,
      "top": 1,
      "importance": "Any",
      "fetchOnlyWithAttachment": false,
      "subjectFilter": "My Email Template Subject"
    }
  }
}
```

Access subject and body:
```
@first(outputs('Get_Email_Template')?['body/value'])?['subject']
@first(outputs('Get_Email_Template')?['body/value'])?['body']
```

> **Outlook-as-CMS pattern**: store a template email in a dedicated Outlook folder.
> Set `fetchOnlyUnread: false` so the template persists after first use.
> Non-technical users can update subject and body by editing that email —
> no flow changes required. Pass subject and body directly into `SendEmailV2`.
>
> To get a folder ID: in Outlook on the web, right-click the folder → open in
> new tab — the folder GUID is in the URL. Prefix it with `Id::` in `folderPath`.

---

## Teams

### Teams — Post Message

```json
"Post_Teams_Message": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_teams",
      "connectionName": "<connectionName>",
      "operationId": "PostMessageToConversation"
    },
    "parameters": {
      "poster": "Flow bot",
      "location": "Channel",
      "body/recipient": {
        "groupId": "<team-id>",
        "channelId": "<channel-id>"
      },
      "body/messageBody": "@outputs('Compose_Message')"
    }
  }
}
```

#### Variant: Group Chat (1:1 or Multi-Person)

To post to a group chat instead of a channel, use `"location": "Group chat"` with
a thread ID as the recipient:

```json
"Post_To_Group_Chat": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_teams",
      "connectionName": "<connectionName>",
      "operationId": "PostMessageToConversation"
    },
    "parameters": {
      "poster": "Flow bot",
      "location": "Group chat",
      "body/recipient": "19:<thread-hash>@thread.v2",
      "body/messageBody": "@outputs('Compose_Message')"
    }
  }
}
```

For 1:1 ("Chat with Flow bot"), use `"location": "Chat with Flow bot"` and set
`body/recipient` to the user's email address.

> **Active-user gate:** When sending notifications in a loop, check the recipient's
> Azure AD account is enabled before posting — avoids failed deliveries to departed
> staff:
> ```json
> "Check_User_Active": {
>   "type": "OpenApiConnection",
>   "inputs": {
>     "host": { "apiId": "/providers/Microsoft.PowerApps/apis/shared_office365users",
>               "operationId": "UserProfile_V2" },
>     "parameters": { "id": "@{item()?['Email']}" }
>   }
> }
> ```
> Then gate: `@equals(body('Check_User_Active')?['accountEnabled'], true)`

---

## Approvals

### Split Approval (Create → Wait)

The standard "Start and wait for an approval" is a single blocking action.
For more control (e.g., posting the approval link in Teams, or adding a timeout
scope), split it into two actions: `CreateAnApproval` (fire-and-forget) then
`WaitForAnApproval` (webhook pause).

```json
"Create_Approval": {
  "type": "OpenApiConnection",
  "runAfter": {},
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_approvals",
      "connectionName": "<connectionName>",
      "operationId": "CreateAnApproval"
    },
    "parameters": {
      "approvalType": "CustomResponse/Result",
      "ApprovalCreationInput/title": "Review: @{variables('ItemTitle')}",
      "ApprovalCreationInput/assignedTo": "approver@contoso.com",
      "ApprovalCreationInput/details": "Please review and select an option.",
      "ApprovalCreationInput/responseOptions": ["Approve", "Reject", "Defer"],
      "ApprovalCreationInput/enableNotifications": true,
      "ApprovalCreationInput/enableReassignment": true
    }
  }
},
"Wait_For_Approval": {
  "type": "OpenApiConnectionWebhook",
  "runAfter": { "Create_Approval": ["Succeeded"] },
  "inputs": {
    "host": {
      "apiId": "/providers/Microsoft.PowerApps/apis/shared_approvals",
      "connectionName": "<connectionName>",
      "operationId": "WaitForAnApproval"
    },
    "parameters": {
      "approvalName": "@body('Create_Approval')?['name']"
    }
  }
}
```

> **`approvalType` options:**
> - `"Approve/Reject - First to respond"` — binary, first responder wins
> - `"Approve/Reject - Everyone must approve"` — requires all assignees
> - `"CustomResponse/Result"` — define your own response buttons
>
> After `Wait_For_Approval`, read the outcome:
> ```
> @body('Wait_For_Approval')?['outcome']          → "Approve", "Reject", or custom
> @body('Wait_For_Approval')?['responses'][0]?['responder']?['displayName']
> @body('Wait_For_Approval')?['responses'][0]?['comments']
> ```
>
> The split pattern lets you insert actions between create and wait — e.g.,
> posting the approval link to Teams, starting a timeout scope, or logging
> the pending approval to a tracking list.
