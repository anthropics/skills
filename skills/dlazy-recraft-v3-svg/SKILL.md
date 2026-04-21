---
name: dlazy-recraft-v3-svg
version: 1.0.0
description: Generate high-quality SVG vector graphics from text using Recraft v3.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy recraft-v3-svg -h to view help information."}}
---

# dlazy-recraft-v3-svg

Generate high-quality SVG vector graphics from text using Recraft v3.

## Trigger Keywords

- recraft svg
- generate vector graphics
- generate svg
- text to image

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy recraft-v3-svg` command to get results.

```bash
dlazy recraft-v3-svg -h

Options:
  --prompt <prompt>              Prompt
  --aspect_ratio <aspect_ratio>  Aspect Ratio (Supports: auto, 1:1, 4:3, 3:4,
                                 16:9, 9:16, 3:2, 2:3, 21:9) [Default: auto]
  --style <style>                Style (Supports: Vector Art, Line Art,
                                 Engraving) [Default: Vector Art]
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
dlazy recraft-v3-svg --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy recraft-v3-svg --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
