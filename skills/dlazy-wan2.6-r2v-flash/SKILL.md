---
name: dlazy-wan2.6-r2v-flash
version: 1.0.0
description: Quickly generate dynamic short videos from reference images using Wan 2.6 Flash.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy wan2.6-r2v-flash -h to view help information."}}
---

# dlazy-wan2.6-r2v-flash

Quickly generate dynamic short videos from reference images using Wan 2.6 Flash.

## Trigger Keywords

- wan 2.6 flash
- fast reference image to video
- generate video

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy wan2.6-r2v-flash` command to get results.

```bash
dlazy wan2.6-r2v-flash -h

Options:
  --prompt <prompt>                    Prompt
  --generation_mode <generation_mode>  Generation Mode (Supports: Components)
                                       [Default: Components]
  --size <size>                        Size (Supports: 1280*720, 720*1280,
                                       960*960, 1088*832, 832*1088, 1920*1080,
                                       1080*1920, 1440*1440, 1632*1248,
                                       1248*1632) [Default: 720*1280]
  --duration <duration>                Duration (s) (Supports: 2, 3, 4, 5, 6,
                                       7, 8, 9, 10) [Default: 5]
  --shotType <shotType>                Shot Type (Supports: single, multi)
                                       [Default: single]
  --watermark <watermark>              Watermark (Supports: true, false)
                                       [Default: false]
  --audio <audio>                      Audio (Supports: true, false) [Default:
                                       false]
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
dlazy wan2.6-r2v-flash --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy wan2.6-r2v-flash --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
