---
name: dlazy-kling-image-o1
version: 1.0.0
description: Generate exquisite images with Kling o1 model. Supports text-to-image and image-to-image.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy kling-image-o1 -h to view help information."}}
---

# dlazy-kling-image-o1

Generate exquisite images with Kling o1 model. Supports text-to-image and image-to-image.

## Trigger Keywords

- kling o1
- kling image
- generate image, edit image
- text to image, image to image

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy kling-image-o1` command to get results.

```bash
dlazy kling-image-o1 -h

Options:
  --prompt <prompt>              Prompt
  --clarity <clarity>            Clarity (Supports: 2k, 4k) [Default: 2k]
  --aspect_ratio <aspect_ratio>  Aspect Ratio (Supports: 16:9, 9:16, 1:1, 4:3,
                                 3:4, 3:2, 2:3, 21:9, auto) [Default: 16:9]
  --image <image>                Path to the local image file or remote image
                                 URL
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
dlazy kling-image-o1 --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy kling-image-o1 --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
