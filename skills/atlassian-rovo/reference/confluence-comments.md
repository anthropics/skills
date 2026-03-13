# Confluence Comments — Reference

## Overview

Read and write footer comments, inline comments, and reply threads on Confluence pages using the REST API.

**API versions:** Creating and reading comments uses v2 (`/wiki/api/v2/`). Replying to comments requires v1 (`/wiki/rest/api/content`) with the ancestors array pattern.

All examples use `{site}` as the Atlassian site URL placeholder.
Credentials: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

## Read Operations

### List footer comments on a page

```bash
curl -s "https://{site}/wiki/api/v2/pages/{pageId}/footer-comments?body-format=storage" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```

### List inline comments on a page

```bash
curl -s "https://{site}/wiki/api/v2/pages/{pageId}/inline-comments?body-format=storage" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```

Inline comments include `properties.inlineOriginalSelection` showing the highlighted text.

### Read a specific comment by ID

Footer:
```bash
curl -s "https://{site}/wiki/api/v2/footer-comments/{commentId}?body-format=storage" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```

Inline:
```bash
curl -s "https://{site}/wiki/api/v2/inline-comments/{commentId}?body-format=storage" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```

### Read reply thread (children of a comment)

```bash
curl -s "https://{site}/wiki/api/v2/footer-comments/{commentId}/children" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```

```bash
curl -s "https://{site}/wiki/api/v2/inline-comments/{commentId}/children" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```

---

## Write Operations

### Create a footer comment

```bash
curl -s -X POST "https://{site}/wiki/api/v2/footer-comments" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "pageId": "{pageId}",
    "body": {"representation": "storage", "value": "<p>Your comment here</p>"}
  }'
```

### Create an inline comment

```bash
curl -s -X POST "https://{site}/wiki/api/v2/inline-comments" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "pageId": "{pageId}",
    "body": {"representation": "storage", "value": "<p>Comment on this text</p>"},
    "inlineCommentProperties": {
      "textSelection": "exact text to highlight",
      "textSelectionMatchCount": 1,
      "textSelectionMatchIndex": 0
    }
  }'
```

### Reply to a comment (footer or inline)

Replies use the **v1 API** with the `ancestors` array to thread under a parent comment:

```bash
curl -s -X POST "https://{site}/wiki/rest/api/content" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "type": "comment",
    "container": {"id": "{pageId}", "type": "page"},
    "ancestors": [{"id": "{parentCommentId}"}],
    "body": {"storage": {"value": "<p>Reply text</p>", "representation": "storage"}}
  }'
```

> **Why v1?** The v2 API returns HTTP 405 when POSTing to `.../children`. The v1 ancestors pattern is the only working approach for threaded replies.

### Add a Jira issue comment

```bash
acli jira workitem comment create --key {projectKey}-{N} --body "Comment text"
```

---

## Shell Helpers

The `atlassian-helpers.sh` library provides convenience functions:

| Function | Description |
|----------|-------------|
| `confluence_add_footer_comment <pageId> <body>` | Create footer comment |
| `confluence_add_inline_comment <pageId> <body> <selection>` | Create inline comment |
| `confluence_get_footer_comment <commentId>` | Read footer comment by ID |
| `confluence_get_inline_comment <commentId>` | Read inline comment by ID |
| `confluence_list_comments <pageId> [footer\|inline]` | List comments on a page |
| `confluence_reply_to_comment <pageId> <parentId> <body>` | Reply to a comment (v1 API) |

---

## Gotchas

1. **Inline textSelection matching:** The `textSelection` must exactly match text in the page body. `textSelectionMatchCount` is the total occurrences on the page. `textSelectionMatchIndex` (0-based) selects which occurrence.

2. **Resolution status:** Inline comments have a `resolutionStatus` field (`open`, `resolved`, `dangling`, `reopened`). Footer comments do not.

3. **Body format:** Comment body in v2 uses storage format (HTML). The v1 reply also uses storage format.

4. **Reply threading:** Both footer and inline comments support reply threads. Use v2 GET `.../children` to read replies, but v1 POST with `ancestors` to create replies.

5. **Inline comment markers in page body:** When a page has inline comments, Confluence wraps the anchored text in `ac:inline-comment-marker` tags in the storage body. Be aware of these when parsing or updating page content.
