---
name: pre-task-calibration
description: Mechanical pre-action verification for Claude Code. Before any Edit/Write operation, enforces three mandatory checks — concept review, input consistency, and verification planning — via PreToolUse hook exit codes. Complements persona-review (adversarial depth) and delivery-verification (session-end completeness).
license: MIT
---

# Pre-Task Calibration

A mechanical checkpoint that runs before every high-risk tool call. Three mandatory questions enforced by PreToolUse hook — any fail blocks the operation.

## When to Activate

- Before any Edit, Write, or high-risk Bash operation
- When the cost of a wrong edit is high (production configs, shared code)
- When you want structured verification habits rather than ad-hoc checking
- After installing delivery-verification and wanting pre-action + post-action defense

## How It Works

```
PreToolUse (Edit/Write) → three mandatory checks:
  Q1: Concept review passed? (did I validate the approach?)
  Q2: Inputs consistent? (paths, constants match actual code?)
  Q3: Verification planned? (will I verify output, not claim completion?)
  All three pass → allow tool call
  Any fail → exit 2, tool call blocked
```

## Install

Add to settings.json PreToolUse hooks:

```json
{
  "hooks": {
    "PreToolUse": [{
      "matcher": "Edit|Write|Bash",
      "hooks": [{
        "type": "command",
        "command": "python3 ~/.claude/scripts/three-questions-guard.py",
        "timeout": 5000
      }]
    }]
  }
}
```

## Example

```
PreToolUse (Edit): three-questions-guard.py checks:
→ Q1: concept-review record found (3 min ago) ✓
→ Q2: file paths consistent with actual code ✓
→ Q3: post-edit verification method specified ✓
→ Allow Edit
```

## Integration

Complements — does not replace:
- **persona-review**: adversarial depth for complex decisions
- **delivery-verification**: session-end completeness checks
- **neural-gate**: post-session behavioral constraint verification

## Design

The three questions are ordered by damage cost: getting the approach wrong (Q1) is more expensive than getting inputs wrong (Q2), which is more expensive than skipping verification (Q3). If Q1 fails, Q2 and Q3 are irrelevant — fixing the approach invalidates all downstream work.
