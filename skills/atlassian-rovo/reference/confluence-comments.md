# Confluence Comments — Reference

## Overview

Read and write footer comments, inline comments, and reply threads on Confluence pages.

## Tools

### Read

| Tool | Description | Key Parameters |
|------|-------------|----------------|
| `getConfluencePageFooterComments` | Get footer comments on a page | `pageId`, `limit`, `sort` |
| `getConfluencePageInlineComments` | Get inline comments (filterable by resolution) | `pageId`, `limit`, `resolutionStatus` |
| `getConfluenceCommentChildren` | Get reply thread on a comment | `commentId`, `commentType` (footer/inline) |

### Write

| Tool | Description | Key Parameters |
|------|-------------|----------------|
| `createConfluenceFooterComment` | Add footer comment or reply | `pageId` OR `parentCommentId`, `body` |
| `createConfluenceInlineComment` | Add inline comment on text | `pageId` OR `parentCommentId`, `body`, `inlineCommentProperties` |
| `addCommentToJiraIssue` | Add Jira issue comment | `issueIdOrKey`, `commentBody` |

---

## Usage Patterns

### Read all footer comments on a page

```
atlassian:getConfluencePageFooterComments:
  cloudId: "{cloudId}"
  pageId: "{pageId}"
  limit: 10
  sort: "created-date"
```

### Read open inline comments

```
atlassian:getConfluencePageInlineComments:
  cloudId: "{cloudId}"
  pageId: "{pageId}"
  limit: 10
  resolutionStatus: "open"
```

Inline comments include `properties.inlineOriginalSelection` showing the highlighted text.

Resolution status options: `open`, `resolved`, `dangling`, `reopened`.

### Read reply thread

```
atlassian:getConfluenceCommentChildren:
  cloudId: "{cloudId}"
  commentId: "{commentId}"
  commentType: "footer"   # or "inline"
  limit: 10
```

### Write a footer comment

```
atlassian:createConfluenceFooterComment:
  cloudId: "{cloudId}"
  pageId: "{pageId}"
  body: "Your comment in **Markdown**"
```

### Reply to a footer comment

```
atlassian:createConfluenceFooterComment:
  cloudId: "{cloudId}"
  parentCommentId: "{commentId}"
  body: "Reply text"
```

### Write an inline comment on specific text

```
atlassian:createConfluenceInlineComment:
  cloudId: "{cloudId}"
  pageId: "{pageId}"
  body: "Comment on this text"
  inlineCommentProperties:
    textSelection: "exact text to highlight"
    textSelectionMatchCount: 1
    textSelectionMatchIndex: 0
```

### Reply to an inline comment

```
atlassian:createConfluenceInlineComment:
  cloudId: "{cloudId}"
  parentCommentId: "{inlineCommentId}"
  body: "Reply to inline comment"
```

---

## Gotchas

1. **Mutually exclusive IDs:** `pageId` and `parentCommentId` cannot be used together. For top-level comments use `pageId`. For replies use `parentCommentId` only. Passing both returns HTTP 400: "Must specify one and only one".

2. **Inline textSelection matching:** The `textSelection` must exactly match text in the page body. `textSelectionMatchCount` is the total number of times the text appears on the page. `textSelectionMatchIndex` (0-based) selects which occurrence to highlight.

3. **Resolution status:** Inline comments have a `resolutionStatus` field. Use `resolutionStatus: "open"` when reading to filter to unresolved comments. Footer comments do not have resolution status.

4. **Body format:** Comment body accepts Markdown. The API converts it to storage format (footer) or ADF (inline) automatically.

5. **Reply threading:** Both footer and inline comments support reply threads via `parentCommentId`. Use `getConfluenceCommentChildren` to read replies, passing the correct `commentType`.
