---
name: dlazy-jimeng-t2i
version: 1.0.0
description: Text-to-image generation with Jimeng, quickly converting text to high-quality images.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy jimeng-t2i -h to view help information."}}
---

# dlazy-jimeng-t2i

Text-to-image generation with Jimeng, quickly converting text to high-quality images.

## Trigger Keywords

- jimeng
- generate image, text to image
- draw a picture

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy jimeng-t2i` command to get results.

```bash
dlazy jimeng-t2i -h

Options:
  --prompt <prompt>  Prompt
  --size <size>      Size (Supports: 1024*1024, 2048*2048, 2304*1728,
                     2496*1664, 2560*1440, 3024*1296, 1728*2304, 1664*2496,
                     1440*2560, 1296*3024, 4096*4096, 4694*3520, 4992*3328,
                     5404*3040, 6198*2656, 3520*4694, 3328*4992, 3040*5404,
                     2656*6198) [Default: 1440*2560]
  --image <image>    Path to the local image file or remote image URL
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
dlazy jimeng-t2i --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy jimeng-t2i --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
