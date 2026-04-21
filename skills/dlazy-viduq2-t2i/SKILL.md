---
name: dlazy-viduq2-t2i
version: 1.0.0
description: Generate high-quality images with Vidu Q2. Supports text-to-image and image-to-image.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy viduq2-t2i -h to view help information."}}
---

# dlazy-viduq2-t2i

Generate high-quality images with Vidu Q2. Supports text-to-image and image-to-image.

## Trigger Keywords

- vidu q2
- generate image, edit image
- text to image, image to image

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy viduq2-t2i` command to get results.

```bash
dlazy viduq2-t2i -h

Options:
  --prompt <prompt>                    Prompt
  --generation_mode <generation_mode>  Generation Mode (Supports: Components)
                                       [Default: Components]
  --aspectRatio <aspectRatio>          Aspect Ratio (Supports: 16:9, 9:16, 1:1,
                                       3:4, 4:3, 21:9, 2:3, 3:2) [Default:
                                       9:16]
  --resolution <resolution>            Resolution (Supports: 1080p, 2K, 4K)
                                       [Default: 1080p]
  --image <image>                      Path to the local image file or remote
                                       image URL
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
dlazy viduq2-t2i --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy viduq2-t2i --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
