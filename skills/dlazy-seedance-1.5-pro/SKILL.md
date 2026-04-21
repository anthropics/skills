---
name: dlazy-seedance-1.5-pro
version: 1.0.0
description: Convert images into dynamic dance videos using Doubao Seedance 1.5 Pro.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy seedance-1.5-pro -h to view help information."}}
---

# dlazy-seedance-1.5-pro

Convert images into dynamic dance videos using Doubao Seedance 1.5 Pro.

## Trigger Keywords

- doubao seedance
- generate dance video
- dancing video
- action video

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy seedance-1.5-pro` command to get results.

```bash
dlazy seedance-1.5-pro -h

Options:
  --prompt <prompt>                    Prompt
  --generation_mode <generation_mode>  Generation Mode (Supports: Frames)
                                       [Default: Frames]
  --resolution <resolution>            Resolution (Supports: 480p, 720p, 1080p)
                                       [Default: 720p]
  --ratio <ratio>                      画幅比例 (Supports: 16:9, 4:3, 1:1, 3:4,
                                       9:16, 21:9, adaptive) [Default:
                                       adaptive]
  --duration <duration>                Duration (s) (Supports: 4, 5, 6, 7, 8,
                                       9, 10, 11, 12) [Default: 5]
  --generate_audio <generate_audio>    Generate Audio [Default: true]
  --image <image>                      Path to the local image file or remote
                                       image URL (First frame)
  --image-tail <imageTail>             Path to the local image file or remote
                                       image URL (Tail/Last frame)
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
dlazy seedance-1.5-pro --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy seedance-1.5-pro --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
