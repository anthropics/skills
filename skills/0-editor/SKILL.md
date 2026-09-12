---
name: 0-editor
description: A robust, native file editing skill for OpenClaw that uses fuzzy AST/line matching instead of exact string replacement. Use this skill whenever you need to edit source code files to avoid whitespace and indentation matching errors.
---

# 0-editor: Agent-Native File Editing

Do NOT use the built-in `edit` tool for modifying blocks of code. The native `edit` tool requires exact string matches, meaning any hallucinated space, tab, or newline will cause your edit to fail.

Instead, use `0-editor` which aligns your edits semantically.

## Usage Instructions

When you need to modify a file:

1. Write the code you want to replace into a temporary file:
   `write /tmp/old.txt`
2. Write the new code into another temporary file:
   `write /tmp/new.txt`
3. Run the `0-editor` CLI via the `exec` tool:
   `exec 0-editor <target_file> /tmp/old.txt /tmp/new.txt`

## Example Tool Call

```json
// 1. Write the old block
{"call": "default_api:write", "args": {"file_path": "/tmp/old.txt", "content": "function add(a, b) {\n  return a + b;\n}"}}

// 2. Write the new block
{"call": "default_api:write", "args": {"file_path": "/tmp/new.txt", "content": "function add(a, b, c=0) {\n  return a + b + c;\n}"}}

// 3. Execute 0-editor
{"call": "default_api:exec", "args": {"command": "0-editor /workspace/math.js /tmp/old.txt /tmp/new.txt"}}
```

`0-editor` will intelligently ignore indentation and whitespace drifts, locate the old block in `math.js`, and replace it with your new block perfectly.
