---
name: dlazy-jimeng-i2v-first
version: 1.0.0
description: Generate dynamic videos based on a single first frame image and prompts using Jimeng.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy jimeng-i2v-first -h to view help information."}}
---

# dlazy-jimeng-i2v-first

Generate dynamic videos based on a single first frame image and prompts using Jimeng.

## Trigger Keywords

- jimeng image to video
- first frame to video
- image to video

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy jimeng-i2v-first` command to get results.

```bash
dlazy jimeng-i2v-first -h

Options:
  --prompt <prompt>                    Prompt
  --generation_mode <generation_mode>  Generation Mode (Supports: Frames)
                                       [Default: Frames]
  --duration <duration>                Duration (s) (Supports: 5, 10) [Default:
                                       5]
  --image <image>                      Path to the local image file or remote
                                       image URL (First frame)
  -h, --help                           display help for command
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
dlazy jimeng-i2v-first --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy jimeng-i2v-first --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
