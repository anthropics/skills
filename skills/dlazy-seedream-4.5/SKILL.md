---
name: dlazy-seedream-4.5
version: 1.0.0
description: Generate smooth, high-quality videos with Doubao Seedream 4.5. Supports text-to-video and image-to-video.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy seedream-4.5 -h to view help information."}}
---

# dlazy-seedream-4.5

Generate smooth, high-quality videos with Doubao Seedream 4.5. Supports text-to-video and image-to-video.

## Trigger Keywords

- doubao seedream 4.5
- generate video
- text to video, image to video

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy seedream-4.5` command to get results.

```bash
dlazy seedream-4.5 -h

Options:
  --prompt <prompt>          Prompt
  --resolution <resolution>  Resolution (Supports: 2k, 4k) [Default: 2k]
  --size <size>              Size (Supports: 1:1, 4:3, 3:4, 16:9, 9:16, 3:2,
                             2:3, 21:9) [Default: 16:9]
  --image <image>            Path to the local image file or remote image URL
  -h, --help                 display help for command
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
dlazy seedream-4.5 --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy seedream-4.5 --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
