---
name: feishu-doc-api-guide
description: Battle-tested guide for using Feishu Document HTTP API directly. Use when working with Feishu documents via REST API calls (not MCP tools), debugging API errors like "invalid param" (code 1770001), implementing custom Feishu integrations, or needing Python examples for document creation and content manipulation. Covers critical gotchas including required document_revision_id parameter, block_type field mappings, and style field requirements.
---

# Feishu Document API Guide

Practical guide for working directly with Feishu Document HTTP APIs, based on real-world debugging and validation.

## When to Use This Skill

Use this skill when:
- Implementing Feishu document operations via HTTP API
- Debugging "invalid param" errors (error code 1770001)
- Creating custom Python integrations with Feishu documents
- Need to understand block creation API requirements
- Working around MCP tool limitations

**NOT for**: High-level MCP tool usage (see `feishu-doc` skill instead)

## Quick Start

### Prerequisites

1. **Get Feishu App Credentials**
   - Create enterprise app at https://open.feishu.cn/app
   - Note your `App ID` (starts with `cli_`)
   - Note your `App Secret`

2. **Grant Required Permissions**
   - `docx:document` - View, comment, edit, and manage cloud documents
   - `docx:document:readonly` - View cloud documents
   - `drive:drive` - View, download, upload, edit files in cloud drive
   - Publish app version to activate permissions

3. **Load Config from ~/.openclaw/openclaw.json**
```json
{
  "channels": {
    "feishu": {
      "appId": "cli_xxx",
      "appSecret": "xxx"
    }
  }
}
```

### Minimal Working Example

```python
import requests

APP_ID = "cli_xxx"
APP_SECRET = "xxx"

# 1. Get access token
token_response = requests.post(
    "https://open.feishu.cn/open-apis/auth/v3/tenant_access_token/internal",
    json={"app_id": APP_ID, "app_secret": APP_SECRET}
)
token = token_response.json()["tenant_access_token"]

# 2. Create document
doc_response = requests.post(
    "https://open.feishu.cn/open-apis/docx/v1/documents",
    headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
    json={"title": "My Document"}
)
doc_id = doc_response.json()["data"]["document"]["document_id"]
print(f"Document: https://feishu.cn/docx/{doc_id}")

# 3. Get revision_id (CRITICAL: Required for adding content)
info_response = requests.get(
    f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}",
    headers={"Authorization": f"Bearer {token}"}
)
revision_id = info_response.json()["data"]["document"]["revision_id"]

# 4. Add content blocks (NOTE: document_revision_id query parameter is REQUIRED)
blocks = [{
    "block_type": 2,  # Text block
    "text": {
        "elements": [{"text_run": {"content": "Hello World"}}],
        "style": {}  # REQUIRED even if empty
    }
}]

add_response = requests.post(
    f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}/blocks/{doc_id}/children?document_revision_id={revision_id}",
    headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
    json={"children": blocks}
)
result = add_response.json()
print(f"Success: {result['code'] == 0}")
```

## Critical Gotchas (Must Know)

### 1. Missing document_revision_id Parameter

**Symptom**: `{"code": 1770001, "msg": "invalid param"}`

**Cause**: URL missing required `document_revision_id` query parameter

**Fix**:
```python
# ❌ WRONG - Missing revision_id
url = f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}/blocks/{doc_id}/children"

# ✅ CORRECT - Include revision_id
url = f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}/blocks/{doc_id}/children?document_revision_id={revision_id}"
```

Get revision_id from document info endpoint:
```python
response = requests.get(
    f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}",
    headers={"Authorization": f"Bearer {token}"}
)
revision_id = response.json()["data"]["document"]["revision_id"]
```

### 2. block_type Field Mismatch

**Symptom**: `{"code": 1770001, "msg": "invalid param"}` even with correct URL

**Cause**: Using wrong field name for block_type

**Common mistakes**:
```python
# ❌ WRONG - block_type 2 is NOT heading1
{
    "block_type": 2,
    "heading1": {"elements": [...]}  # Wrong!
}

# ✅ CORRECT - block_type 2 is "text"
{
    "block_type": 2,
    "text": {"elements": [...], "style": {}}
}
```

**Verified mappings**:
- `block_type: 2` → `text` field (text paragraph)
- `block_type: 3` → `heading3` field (heading level 3)
- `block_type: 26` → `bullet` field (bullet list item, but unstable - see below)

### 3. Missing style Field

**Symptom**: Invalid param error even with correct block_type

**Cause**: `text`, `bullet`, `ordered` objects require `style: {}` field

**Fix**:
```python
# ❌ WRONG - Missing style
{
    "block_type": 2,
    "text": {
        "elements": [{"text_run": {"content": "Hello"}}]
    }
}

# ✅ CORRECT - Include style (even if empty)
{
    "block_type": 2,
    "text": {
        "elements": [{"text_run": {"content": "Hello"}}],
        "style": {}  # REQUIRED
    }
}
```

### 4. Bullet Lists Are Unreliable

**Observation**: `block_type: 26` (bullet) sometimes fails with invalid param

**Workaround**: Use text blocks with Unicode bullet character
```python
# ✅ RELIABLE - Text block with bullet character
{
    "block_type": 2,
    "text": {
        "elements": [{"text_run": {"content": "• List item text"}}],
        "style": {}
    }
}

# ⚠️ UNSTABLE - May work, may fail
{
    "block_type": 26,
    "bullet": {
        "elements": [{"text_run": {"content": "List item"}}],
        "style": {}
    }
}
```

## Common Tasks

### Create Text Block with Bold
```python
{
    "block_type": 2,
    "text": {
        "elements": [
            {"text_run": {"content": "Normal text "}},
            {"text_run": {
                "content": "bold text",
                "text_element_style": {"bold": True}
            }},
            {"text_run": {"content": " more normal"}}
        ],
        "style": {}
    }
}
```

### Batch Add Blocks

Add blocks in small batches with delays:
```python
import time

revision_id = get_revision_id(token, doc_id)

for batch in batches:
    revision_id = add_blocks(token, doc_id, batch, revision_id)
    time.sleep(0.5)  # Avoid rate limit
```

**Best practices**:
- 5-10 blocks per batch
- 0.5-1s delay between batches
- Always use the new revision_id returned from each call

### Helper Script

Use included `scripts/feishu_doc_writer.py` for production code:

```python
from feishu_doc_writer import FeishuDocWriter, text_block, mixed_text_block

writer = FeishuDocWriter(app_id=APP_ID, app_secret=APP_SECRET)

# Create document
doc_id = writer.create_document("My Doc")

# Add content
blocks = [
    text_block("Title", bold=True),
    text_block("Normal paragraph"),
    mixed_text_block([
        ("Regular ", False),
        ("Bold", True),
        (" text", False)
    ])
]

writer.add_blocks(doc_id, blocks)
```

## Troubleshooting

### Debug Checklist

When getting "invalid param" errors:

1. ✓ Is `document_revision_id` in the URL query string?
2. ✓ Does `block_type` match the field name? (2→text, 3→heading3, etc.)
3. ✓ Do all text/bullet/ordered objects have `style: {}`?
4. ✓ Are you using text blocks instead of unstable bullet blocks?

### Inspect Full Error Response
```python
result = response.json()
import json
print(json.dumps(result, indent=2, ensure_ascii=False))
```

### Test Token Validity
```python
response = requests.get(
    f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}",
    headers={"Authorization": f"Bearer {token}"}
)
print(response.json())  # Should return document info, not auth error
```

### Common Error Codes

- `1770001` - Invalid param (missing field, wrong field name, missing style, etc.)
- `429` - Rate limit exceeded
- `403/400` - Permission denied (check app permissions)

## Rate Limits

- **Application level**: 3 calls/second max
- **Document level**: 3 concurrent edits/second max

Handle rate limits with exponential backoff:
```python
import time

def add_with_retry(writer, doc_id, blocks, max_retries=3):
    for attempt in range(max_retries):
        try:
            return writer.add_blocks(doc_id, blocks)
        except Exception as e:
            if "429" in str(e) and attempt < max_retries - 1:
                time.sleep(2 ** attempt)  # Exponential backoff
            else:
                raise
```

## Resources

### references/common-pitfalls.md

Comprehensive reference of all discovered pitfalls, edge cases, and debugging techniques. Read this when:
- Encountering persistent API errors
- Need detailed examples of each gotcha
- Debugging complex integration issues

### scripts/feishu_doc_writer.py

Production-ready Python class for document operations. Includes:
- FeishuDocWriter class with token management
- Helper functions: text_block(), mixed_text_block(), empty_line()
- Example usage with error handling
- Automatic revision_id tracking

Use this script as a starting point for custom integrations.

## Further Reading

- Official API docs: https://open.feishu.cn/document/server-docs/docs/docs/docx-v1/document-block/create
- Use browser DevTools to inspect actual request format from official examples
- Test in small increments - validate each block format before batch operations
