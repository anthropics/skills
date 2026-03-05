---
name: n8n-debugger
description: Expert in debugging and fixing broken n8n workflows. Use when troubleshooting workflow errors, fixing failed executions, resolving expression issues, debugging HTTP requests, handling credential problems, or optimizing slow workflows. Focuses on error messages, execution logs, and systematic debugging.
license: Complete terms in LICENSE.txt
---

# n8n Workflow Debugger

## When to Use This Skill

Activate this skill when:
- Workflows are failing or throwing errors
- Nodes are not executing as expected
- Expressions are not evaluating correctly
- HTTP requests are failing (401, 403, 404, 500 errors)
- Data is not flowing between nodes
- Credentials are not working
- Workflows are running slowly or timing out
- Webhooks are not triggering
- Code nodes are throwing JavaScript errors
- Loop logic is not working correctly

## Systematic Debugging Approach

### Step 1: Identify the Error
1. Check execution view for red error indicators
2. Read the full error message carefully
3. Note which node failed and at what step
4. Check if error is consistent or intermittent

### Step 2: Isolate the Problem
1. Test the failing node individually (Execute Node)
2. Check the input data to that node
3. Verify previous nodes are outputting expected data
4. Test with simplified/minimal data first

### Step 3: Fix and Verify
1. Apply the fix
2. Test with original failing data
3. Test with edge cases
4. Re-run full workflow to ensure no side effects

## Common Error Types & Fixes

### 1. Expression Errors

**Error:** `ERROR: Cannot read property 'X' of undefined`

**Causes:**
- Accessing a field that doesn't exist
- Trying to read data from disconnected node
- Incorrect node name in expression

**Fixes:**
```javascript
// ❌ Wrong - will fail if field doesn't exist
{{ $json.user.email }}

// ✅ Correct - use optional chaining
{{ $json.user?.email }}

// ✅ Correct - provide fallback
{{ $json.user?.email || 'no-email@example.com' }}

// ✅ Correct - check existence first
{{ $json.user && $json.user.email ? $json.user.email : 'default' }}
```

**Error:** `ERROR: [invalid] is not a valid expression`

**Causes:**
- Missing closing brackets `{{ }}`
- Unmatched quotes
- Invalid JavaScript syntax in expression

**Fixes:**
```javascript
// ❌ Wrong - missing closing bracket
{{ $json.name }

// ✅ Correct
{{ $json.name }}

// ❌ Wrong - unmatched quotes
{{ "text' }}

// ✅ Correct
{{ "text" }}
```

### 2. HTTP Request Errors

**Error:** `401 Unauthorized`

**Debug Steps:**
1. Check credentials are configured and selected
2. Verify API key/token is valid and not expired
3. Test authentication outside n8n (Postman/curl)
4. Check if authentication type matches API requirements

**Fix:**
```json
{
  "parameters": {
    "authentication": "genericCredentialType",
    "genericAuthType": "httpHeaderAuth",
    "url": "https://api.example.com/endpoint"
  }
}
```

**Error:** `403 Forbidden`

**Debug Steps:**
1. Check if API key has required permissions
2. Verify you're accessing allowed resources
3. Check rate limits haven't been exceeded
4. Verify IP whitelisting if applicable

**Error:** `404 Not Found`

**Debug Steps:**
1. Check URL is correct (spelling, case-sensitivity)
2. Verify dynamic URL parts are evaluated correctly
3. Test URL in browser/Postman
4. Check if resource ID is valid

**Fix:**
```javascript
// ❌ Wrong - expression not evaluated
url: "https://api.example.com/users/{{ $json.userId }}"

// ✅ Correct - use proper expression syntax
url: "=https://api.example.com/users/{{ $json.userId }}"
```

**Error:** `500 Internal Server Error`

**Debug Steps:**
1. Check request body format (JSON syntax)
2. Verify all required fields are included
3. Check data types match API expectations
4. Look at response body for detailed error message

**Error:** `Timeout Error` or `ETIMEDOUT`

**Debug Steps:**
1. Check if API endpoint is responding (test externally)
2. Increase timeout in node options
3. Check network connectivity
4. Verify no rate limiting

**Fix:**
```json
{
  "parameters": {
    "options": {
      "timeout": 60000,  // Increase from default 30000ms
      "retry": {
        "enabled": true,
        "maxRetries": 3,
        "retryInterval": 2000
      }
    }
  }
}
```

### 3. Data Flow Errors

**Error:** Node receives empty data or wrong data

**Debug Steps:**
1. Execute previous node and inspect output
2. Check connections are correct (right output index)
3. Verify node name in expressions matches exactly
4. Check IF/Switch conditions are evaluating correctly

**Fix Conditional Logic:**
```json
{
  "parameters": {
    "conditions": {
      "conditions": [
        {
          "leftValue": "={{ $json.status }}",
          "rightValue": "active",
          "operator": {
            "type": "string",
            "operation": "equals",
            "caseSensitive": false  // Add this if case matters
          }
        }
      ]
    }
  }
}
```

**Error:** Data from wrong node/step

**Fix:**
```javascript
// ❌ Wrong - using wrong node name
{{ $('HTTP Request').item.json.data }}

// ✅ Correct - verify exact node name (case-sensitive)
{{ $('HTTP Request 1').item.json.data }}

// Alternative - use item index
{{ $input.item.json.data }}
```

### 4. Code Node Errors

**Error:** `TypeError: Cannot read property 'X' of undefined`

**Debug Steps:**
1. Add console.log() to check variable values
2. Check if $input.all() returns expected data
3. Verify array/object structure matches expectations
4. Add null/undefined checks

**Fix:**
```javascript
// ❌ Wrong - assumes data exists
const items = $input.all();
const processed = items.map(item => ({
  json: {
    email: item.json.user.email  // Fails if user doesn't exist
  }
}));

// ✅ Correct - check existence
const items = $input.all();
const processed = items.map(item => ({
  json: {
    email: item.json.user?.email || 'no-email'
  }
}));
```

**Error:** `Code doesn't return proper items`

**Fix:**
```javascript
// ❌ Wrong - returning wrong format
return {
  name: 'test',
  value: 123
};

// ✅ Correct - must return array of objects with json property
return [{
  json: {
    name: 'test',
    value: 123
  }
}];

// ✅ Correct - for multiple items
return $input.all().map(item => ({
  json: {
    ...item.json,
    processed: true
  }
}));
```

### 5. Credential Errors

**Error:** `Credentials not found` or `Credential type 'X' not supported`

**Debug Steps:**
1. Verify credential is created in n8n settings
2. Check credential type matches node requirements
3. Ensure credential is not expired
4. Test credential with simple API call

**Fix:**
1. Go to Settings → Credentials
2. Create new credential of correct type
3. Test credential
4. Select in node dropdown

### 6. Loop/Batch Errors

**Error:** Loop runs forever or doesn't loop

**Debug Steps:**
1. Check Split In Batches is connected correctly
2. Verify loop-back connection goes to Split node
3. Check batch size is reasonable
4. Add counter to track iterations

**Fix:**
```
[Trigger] → [Get All Items] → [Split In Batches] → [Process Batch] → [Loop Back]
                                        ↓ (done output)
                                   [After Loop Done]
```

**Connections must be:**
```json
{
  "connections": {
    "Split In Batches": {
      "main": [
        [
          {
            "node": "Process Batch",
            "type": "main",
            "index": 0
          }
        ]
      ]
    },
    "Process Batch": {
      "main": [
        [
          {
            "node": "Split In Batches",  // Loop back here!
            "type": "main",
            "index": 0
          }
        ]
      ]
    }
  }
}
```

### 7. Webhook Errors

**Error:** Webhook not triggering

**Debug Steps:**
1. Check webhook URL is correct
2. Verify workflow is active (not just saved)
3. Check webhook method matches (GET/POST)
4. Test with curl/Postman
5. Check firewall/network access

**Test Webhook:**
```bash
# Test webhook with curl
curl -X POST https://your-n8n.com/webhook/your-path \
  -H "Content-Type: application/json" \
  -d '{"test": "data"}'
```

**Error:** Webhook receives data but doesn't process

**Debug Steps:**
1. Check response mode setting
2. Verify workflow executes after webhook
3. Check for errors in downstream nodes
4. Review webhook execution logs

### 8. Variable/Context Errors

**Error:** Can't access data from earlier in workflow

**Fix:**
```javascript
// ❌ Wrong - only accesses current item
{{ $json.value }}

// ✅ Correct - access specific previous node
{{ $('Node Name').item.json.value }}

// ✅ Correct - access all items from previous node
{{ $('Node Name').all() }}

// ✅ Correct - access first item
{{ $('Node Name').first().json.value }}
```

## Debugging Tools & Techniques

### 1. Enable Detailed Logging

Add Code nodes to log data:
```javascript
// Log current item
console.log('Current item:', JSON.stringify($input.item.json, null, 2));

// Log all items
console.log('All items:', JSON.stringify($input.all(), null, 2));

// Return data unchanged
return $input.all();
```

### 2. Use Set Node for Debugging

Add a Set node to inspect data structure:
```json
{
  "parameters": {
    "mode": "manual",
    "assignments": {
      "assignments": [
        {
          "name": "debug_input",
          "value": "={{ JSON.stringify($json) }}",
          "type": "string"
        },
        {
          "name": "debug_keys",
          "value": "={{ Object.keys($json).join(', ') }}",
          "type": "string"
        }
      ]
    }
  }
}
```

### 3. Test with Minimal Data

Create a Set node with test data:
```json
{
  "parameters": {
    "mode": "manual",
    "assignments": {
      "assignments": [
        {
          "name": "id",
          "value": "123",
          "type": "string"
        },
        {
          "name": "name",
          "value": "Test User",
          "type": "string"
        }
      ]
    }
  }
}
```

### 4. Binary Search Debugging

1. Disable half the workflow
2. Execute to find which half has the error
3. Re-enable and disable half of the problematic half
4. Repeat until you find the exact failing node

### 5. Check Execution History

1. Go to Executions tab
2. Find the failed execution
3. Click to view details
4. Review each node's input/output
5. Check error messages

## Performance Debugging

### Slow Workflow Execution

**Debug Steps:**
1. Check execution time for each node
2. Identify bottleneck nodes
3. Look for unnecessary loops
4. Check for large data transfers

**Optimizations:**
```javascript
// ❌ Slow - processing items one at a time
// (Run once for each item mode)

// ✅ Faster - batch processing
// (Run once for all items mode)
const items = $input.all();
const processed = items.map(item => ({
  json: { ...item.json, processed: true }
}));
return processed;
```

### Memory Issues

**Symptoms:**
- Workflow crashes mid-execution
- Browser becomes unresponsive
- Long delays between node executions

**Fixes:**
1. Use Split In Batches for large datasets
2. Reduce batch sizes (try 10-50 items per batch)
3. Clear unnecessary data with Set node
4. Avoid storing large binary files in workflow

## Quick Diagnostic Checklist

**When a workflow fails, check:**
- [ ] Error message in execution view
- [ ] Previous node's output data
- [ ] Expression syntax (brackets, quotes)
- [ ] Node names are correct (case-sensitive)
- [ ] Connections are correct (right output index)
- [ ] Credentials are configured and valid
- [ ] HTTP URLs are correct and accessible
- [ ] Required fields are populated
- [ ] Data types match expectations
- [ ] IF/Switch conditions evaluate correctly
- [ ] Code node returns proper format
- [ ] Workflow is active (for webhooks)

## Common Fixes Quick Reference

| Error Type | Quick Fix |
|-----------|-----------|
| `undefined` | Add null checks: `?.` or `\|\|` |
| 401/403 | Check credentials & permissions |
| 404 | Verify URL and resource ID |
| 500 | Check request body format |
| Timeout | Increase timeout & add retries |
| Expression error | Check brackets `{{ }}` |
| Wrong data | Verify node names in expressions |
| Code error | Return `[{ json: {...} }]` format |
| Loop stuck | Check loop-back connection |
| Webhook not firing | Activate workflow |

---

## Skill Control

**To disable this skill temporarily:**
```bash
mv ~/.claude/skills/n8n-debugger ~/.claude/skills/n8n-debugger.disabled
```

**To re-enable:**
```bash
mv ~/.claude/skills/n8n-debugger.disabled ~/.claude/skills/n8n-debugger
```

---

*Made with 🧡 by wolfejam.dev*
*Fix ALL the bugs!* 🐛✨
