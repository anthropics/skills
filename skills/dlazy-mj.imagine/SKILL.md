---
name: dlazy-mj.imagine
version: 1.0.0
description: Generate artistic images using Midjourney (MJ) model. Supports text-to-image.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy mj.imagine -h to view help information."}}
---

# dlazy-mj.imagine

Generate artistic images using Midjourney (MJ) model. Supports text-to-image.

## Trigger Keywords

- midjourney
- mj
- generate image, artistic painting
- text to image

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy mj.imagine` command to get results.

```bash
dlazy mj.imagine -h

Options:
  --prompt <prompt>              Prompt
  --aspect_ratio <aspect_ratio>  Aspect Ratio (Supports: auto, 1:1, 4:3, 3:4,
                                 16:9, 9:16, 3:2, 2:3, 21:9) [Default: auto]
  --botType <botType>            Bot Type (Supports: MID_JOURNEY, NIJI_JOURNEY)
                                 [Default: MID_JOURNEY]
  --output <output>              Output (Supports: grid, U1, U2, U3, U4)
                                 [Default: grid]
  -h, --help                     display help for command
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
dlazy mj.imagine --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy mj.imagine --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
