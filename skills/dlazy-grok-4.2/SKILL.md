---
name: dlazy-grok-4.2
version: 1.0.0
description: Efficient text generation, dialogue QA, and logical reasoning using Grok 4.2 text model.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy grok-4.2 -h to view help information."}}
---

# dlazy-grok-4.2

Efficient text generation, dialogue QA, and logical reasoning using Grok 4.2 text model.

## Trigger Keywords

- grok 4.2
- generate text
- qa
- chat

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy grok-4.2` command to get results.

```bash
dlazy grok-4.2 -h

Options:
  --prompt <prompt>  Prompt
  -h, --help         display help for command
```

## Output Format

```json
{
  "code": 0,
  "message": "",
  "data": {
    "urls": ["https://oss.dlazy.com/result.png"]
  }
}
```

## Command Examples

```bash
# basic call:
dlazy grok-4.2 --prompt 'prompt text'

# complex call:
dlazy grok-4.2 --prompt 'prompt text'
```

## Error Handling

| Code | Error Type                         | Example Message                                                                                                          |
| ---- | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| 501  | Missing required parameter         | `error: required option '--prompt <prompt>' not specified`                                                              |
| 502  | Local file read error              | `Error: Image file/Video file not found: C:\path\to\your\file`                                                          |
| 503  | API request failed (no balance)    | `Error during API request: Request failed with status code 400` / `Response details: {"error": "Insufficient balance"}` |
| 503  | API request failed (server error)  | `HTTP status code error (500 server crash)`                                                                             |
| 504  | Asynchronous task execution failed | `=== Generation Failed ===` / `{Specific error reason returned by backend, for example "Prompt violates safety policy"}` |

> **CRITICAL INSTRUCTION FOR AGENT**: If the output returns `code: 503` and indicates insufficient balance, you MUST inform the user that their credits are insufficient and provide them with this link to recharge: [https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits](https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits)

## Tips

Visit https://dlazy.com for more information.
