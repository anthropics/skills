---
name: n8n-builder
description: Expert in building n8n workflows from scratch. Use when creating new n8n workflows, adding nodes, connecting APIs, setting up webhooks, transforming data, or implementing automation patterns. Focuses on workflow structure, node configuration, best practices, and clean architecture.
license: Complete terms in LICENSE.txt
---

# n8n Workflow Builder

## What is n8n?

n8n is a fair-code workflow automation platform that connects apps, APIs, and services. It uses a visual node-based interface to build complex automations without writing code (though code is fully supported when needed).

**Core Concepts:**
- **Workflows** - Automated sequences of tasks (nodes)
- **Nodes** - Individual steps (HTTP Request, Webhook, Code, etc.)
- **Connections** - Links between nodes that pass data
- **Credentials** - Stored authentication for services
- **Expressions** - Dynamic data using `{{ $json.fieldName }}`

## When to Use This Skill

Activate this skill when:
- Creating or editing n8n workflows (.json files)
- Building HTTP API integrations
- Setting up webhooks (incoming/outgoing)
- Transforming data between services
- Writing JavaScript in Code nodes
- Debugging workflow errors
- Optimizing workflow performance
- Handling credentials and authentication
- Batch processing or looping over data
- Error handling and retry logic

## n8n Workflow Structure (JSON)

### Basic Workflow Template

```json
{
  "name": "My Workflow",
  "nodes": [
    {
      "parameters": {},
      "id": "unique-id-1",
      "name": "Start",
      "type": "n8n-nodes-base.manualTrigger",
      "typeVersion": 1,
      "position": [250, 300]
    }
  ],
  "connections": {},
  "active": false,
  "settings": {
    "executionOrder": "v1"
  },
  "versionId": "1",
  "meta": {
    "instanceId": "your-instance-id"
  }
}
```

### Node Structure

Every node has these required fields:
- `parameters` - Node configuration (URLs, methods, data, etc.)
- `id` - Unique identifier (UUID format)
- `name` - Display name (must be unique in workflow)
- `type` - Node type (e.g., `n8n-nodes-base.httpRequest`)
- `typeVersion` - Node version (usually 1-4)
- `position` - [x, y] coordinates on canvas

## Common Node Types

### 1. HTTP Request Node
```json
{
  "parameters": {
    "method": "POST",
    "url": "https://api.example.com/endpoint",
    "authentication": "genericCredentialType",
    "genericAuthType": "httpHeaderAuth",
    "sendHeaders": true,
    "headerParameters": {
      "parameters": [
        {
          "name": "Content-Type",
          "value": "application/json"
        }
      ]
    },
    "sendBody": true,
    "bodyParameters": {
      "parameters": [
        {
          "name": "key",
          "value": "={{ $json.value }}"
        }
      ]
    },
    "options": {
      "timeout": 30000,
      "retry": {
        "enabled": true,
        "maxRetries": 3,
        "retryInterval": 1000
      }
    }
  },
  "type": "n8n-nodes-base.httpRequest",
  "typeVersion": 4.2
}
```

### 2. Webhook Node (Trigger)
```json
{
  "parameters": {
    "httpMethod": "POST",
    "path": "my-webhook",
    "responseMode": "onReceived",
    "options": {}
  },
  "type": "n8n-nodes-base.webhook",
  "typeVersion": 2
}
```

### 3. Code Node (JavaScript)
```json
{
  "parameters": {
    "mode": "runOnceForAllItems",
    "jsCode": "// Process all items\nconst items = $input.all();\nconst processed = items.map(item => ({\n  json: {\n    ...item.json,\n    processed: true,\n    timestamp: new Date().toISOString()\n  }\n}));\nreturn processed;"
  },
  "type": "n8n-nodes-base.code",
  "typeVersion": 2
}
```

### 4. IF Node (Conditional)
```json
{
  "parameters": {
    "conditions": {
      "options": {
        "caseSensitive": true,
        "leftValue": "",
        "typeValidation": "strict"
      },
      "conditions": [
        {
          "id": "condition-1",
          "leftValue": "={{ $json.status }}",
          "rightValue": "success",
          "operator": {
            "type": "string",
            "operation": "equals"
          }
        }
      ],
      "combinator": "and"
    },
    "options": {}
  },
  "type": "n8n-nodes-base.if",
  "typeVersion": 2
}
```

### 5. Split In Batches (Loop)
```json
{
  "parameters": {
    "batchSize": 10,
    "options": {}
  },
  "type": "n8n-nodes-base.splitInBatches",
  "typeVersion": 3
}
```

### 6. Set Node (Transform Data)
```json
{
  "parameters": {
    "mode": "manual",
    "duplicateItem": false,
    "assignments": {
      "assignments": [
        {
          "id": "assignment-1",
          "name": "userId",
          "value": "={{ $json.user.id }}",
          "type": "string"
        },
        {
          "id": "assignment-2",
          "name": "createdAt",
          "value": "={{ $now }}",
          "type": "string"
        }
      ]
    },
    "options": {}
  },
  "type": "n8n-nodes-base.set",
  "typeVersion": 3.4
}
```

## Connections Between Nodes

### Simple Connection
```json
"connections": {
  "Start": {
    "main": [
      [
        {
          "node": "HTTP Request",
          "type": "main",
          "index": 0
        }
      ]
    ]
  },
  "HTTP Request": {
    "main": [
      [
        {
          "node": "Process Data",
          "type": "main",
          "index": 0
        }
      ]
    ]
  }
}
```

### Conditional Connections (IF node)
```json
"connections": {
  "IF": {
    "main": [
      [
        {
          "node": "Success Path",
          "type": "main",
          "index": 0
        }
      ],
      [
        {
          "node": "Failure Path",
          "type": "main",
          "index": 0
        }
      ]
    ]
  }
}
```

## n8n Expressions & Data Access

### Accessing Data from Previous Nodes

```javascript
// Current item data
{{ $json.fieldName }}
{{ $json['field-with-dashes'] }}
{{ $json.nested.object.value }}

// Previous node data
{{ $('Node Name').item.json.fieldName }}

// All items from previous node
{{ $('Node Name').all() }}

// First/last item
{{ $('Node Name').first().json.fieldName }}
{{ $('Node Name').last().json.fieldName }}

// Item by index
{{ $('Node Name').item.json[0].fieldName }}
```

### Built-in Functions

```javascript
// Date/Time
{{ $now }}                          // Current timestamp
{{ $today }}                        // Today's date
{{ DateTime.now().toISO() }}        // ISO format

// String manipulation
{{ $json.text.toUpperCase() }}
{{ $json.text.toLowerCase() }}
{{ $json.text.trim() }}
{{ $json.text.replace('old', 'new') }}

// JSON operations
{{ JSON.stringify($json) }}
{{ JSON.parse($json.stringData) }}

// Math
{{ Math.round($json.value) }}
{{ Math.floor($json.value) }}
{{ Math.ceil($json.value) }}

// Arrays
{{ $json.array.length }}
{{ $json.array.join(',') }}
{{ $json.array.map(item => item.id) }}
```

## Best Practices

### 1. Error Handling

**Always add error handling for critical nodes:**

```json
{
  "parameters": {
    "rules": {
      "values": [
        {
          "conditions": {
            "options": {
              "caseSensitive": true,
              "leftValue": "",
              "typeValidation": "strict"
            },
            "conditions": [
              {
                "leftValue": "={{ $json.error }}",
                "rightValue": "",
                "operator": {
                  "type": "any",
                  "operation": "exists",
                  "singleValue": true
                }
              }
            ],
            "combinator": "and"
          },
          "renameOutput": true,
          "outputKey": "error"
        }
      ]
    },
    "options": {
      "fallbackOutput": "extra"
    }
  },
  "type": "n8n-nodes-base.switch",
  "name": "Error Check"
}
```

### 2. Credential Management

**Never hardcode credentials in workflows:**

✅ **Correct:**
```json
{
  "parameters": {
    "authentication": "genericCredentialType",
    "genericAuthType": "httpHeaderAuth"
  }
}
```

❌ **Wrong:**
```json
{
  "parameters": {
    "headerParameters": {
      "parameters": [
        {
          "name": "Authorization",
          "value": "Bearer hardcoded-token-123"
        }
      ]
    }
  }
}
```

### 3. HTTP Request Best Practices

**Timeouts and Retries:**
```json
{
  "parameters": {
    "options": {
      "timeout": 30000,
      "retry": {
        "enabled": true,
        "maxRetries": 3,
        "retryInterval": 1000
      },
      "response": {
        "response": {
          "responseFormat": "json"
        }
      }
    }
  }
}
```

### 4. Data Transformation

**Use Set node for clean data:**
```json
{
  "parameters": {
    "mode": "manual",
    "assignments": {
      "assignments": [
        {
          "name": "cleanName",
          "value": "={{ $json.firstName + ' ' + $json.lastName }}",
          "type": "string"
        },
        {
          "name": "email",
          "value": "={{ $json.email.toLowerCase() }}",
          "type": "string"
        },
        {
          "name": "timestamp",
          "value": "={{ $now }}",
          "type": "string"
        }
      ]
    }
  },
  "type": "n8n-nodes-base.set"
}
```

### 5. Code Node Tips

**Run once vs. Run once for each item:**

```javascript
// Run once for all items
const items = $input.all();
const processed = items.map(item => ({
  json: {
    ...item.json,
    processed: true
  }
}));
return processed;

// Run once for each item
return {
  json: {
    ...$input.item.json,
    processed: true,
    timestamp: new Date().toISOString()
  }
};
```

### 6. Batch Processing

**Use Split In Batches for large datasets:**

```
[Trigger] → [Split In Batches] → [Process Items] → [Loop Back to Split]
                                        ↓
                                  [After Loop]
```

## Common Patterns

### Pattern 1: API Pagination

```
[Trigger] → [HTTP Request] → [Code: Check if more pages] → [IF]
                                                              ↓ true
                                                         [Loop back]
                                                              ↓ false
                                                         [Continue]
```

### Pattern 2: Webhook → Process → Respond

```
[Webhook] → [Process Data] → [HTTP Request] → [Respond to Webhook]
```

### Pattern 3: Error Handling

```
[HTTP Request] → [Switch: Check for errors] → [true] → [Log Error] → [Send Alert]
                                            → [false] → [Success Path]
```

### Pattern 4: Parallel Processing

```
[Trigger] → [Split] → [Branch 1: API A]
                   → [Branch 2: API B]  → [Merge] → [Combine Results]
                   → [Branch 3: API C]
```

## Troubleshooting Guide

### Common Issues

**1. Expression Errors**
- Check for missing closing brackets: `{{ }}`
- Use quotes for strings: `{{ "text" }}`
- Access nested objects: `{{ $json.level1.level2 }}`

**2. Connection Issues**
- Verify node names match exactly (case-sensitive)
- Check connection indices (0 = first output)
- Ensure all required nodes are connected

**3. Data Not Flowing**
- Check IF conditions are evaluating correctly
- Verify expressions are returning expected data
- Use "Execute Workflow" to test node by node

**4. HTTP Request Failures**
- Check URL is valid and accessible
- Verify authentication credentials
- Add timeout and retry options
- Check response format (JSON vs. text)

**5. Code Node Errors**
- Always return an array of objects with `json` property
- Use `$input.all()` to access all items
- Check for undefined values before accessing properties
- Test code logic outside n8n first

## Performance Tips

### 1. Minimize HTTP Requests
- Batch API calls when possible
- Use pagination instead of loading all data
- Cache frequently accessed data

### 2. Optimize Code Nodes
- Process items in batches
- Avoid nested loops when possible
- Use built-in array methods (map, filter, reduce)

### 3. Error Recovery
- Add retry logic to HTTP nodes
- Use error workflows for critical failures
- Log errors for debugging

### 4. Workflow Organization
- Use descriptive node names
- Group related nodes visually
- Add notes for complex logic
- Keep workflows focused (one purpose per workflow)

## Node Positioning

**Visual layout best practices:**
```json
"position": [x, y]
```

- Start node: `[250, 300]`
- Space nodes horizontally: 300-400px apart
- Space nodes vertically: 200-250px apart
- Align nodes on same path vertically
- Offset parallel branches horizontally

## Workflow Settings

### Execution Order
```json
"settings": {
  "executionOrder": "v1"  // v0 (old) or v1 (new)
}
```

### Timezone
```json
"settings": {
  "timezone": "America/New_York"
}
```

### Error Workflow
```json
"settings": {
  "errorWorkflow": "workflow-id-here"
}
```

## Testing & Debugging

### 1. Test Individual Nodes
- Use "Execute Node" to test single nodes
- Check input/output data in node view
- Verify expressions evaluate correctly

### 2. Test Full Workflow
- Use "Execute Workflow" with test data
- Check execution path (green connections)
- Review output data at each step

### 3. Error Debugging
- Check error messages in execution view
- Review node configuration
- Test with simplified data first
- Add Code nodes to log intermediate values

## Resources

- **n8n Docs**: https://docs.n8n.io
- **Community Forum**: https://community.n8n.io
- **Workflow Templates**: https://n8n.io/workflows
- **Node Reference**: https://docs.n8n.io/integrations/builtin/

---

## Skill Control

**To disable this skill temporarily:**
```bash
mv ~/.claude/skills/n8n ~/.claude/skills/n8n.disabled
```

**To re-enable:**
```bash
mv ~/.claude/skills/n8n.disabled ~/.claude/skills/n8n
```

---

*Made with 🧡 by wolfejam.dev*
*Automate ALL the things!* 🤖✨
