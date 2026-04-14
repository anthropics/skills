---
name: dlazy-kling-v3-omni
version: 1.0.0
description: Versatile video generation with Kling v3 Omni. Supports multi-modal inputs to generate stunning dynamic videos.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy kling-v3-omni -h to view help information."}}
---

# dlazy-kling-v3-omni

Versatile video generation with Kling v3 Omni. Supports multi-modal inputs to generate stunning dynamic videos.

## Trigger Keywords

- kling v3 omni
- generate omni video
- text to video, image to video

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy kling-v3-omni` command to get results.

```bash
dlazy kling-v3-omni -h

Options:
  --prompt <prompt>                            Prompt
  --generation_mode <generation_mode>          Generation Mode (Supports: Frames, Components) [Default: Frames]
  --subjects <subjects>                        Subjects
  --video_refer_type <video_refer_type>        Video Refer Type (Supports: feature, base) [Default: feature]
  --keep_original_sound <keep_original_sound>  Keep Original Sound [Default: false]
  --aspect_ratio <aspect_ratio>                Aspect Ratio (Supports: 16:9, 9:16, 1:1) [Default: 16:9]
  --duration <duration>                        Duration (s) (Supports: 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) [Default: 5]
  --mode <mode>                                Mode (Supports: Standard, Pro) [Default: Standard]
  --sound <sound>                              音效 [Default: false]
  --image <image>                              Path to the local image file or remote image URL (First frame)
  --image-tail <imageTail>                     Path to the local image file or remote image URL (Tail/Last frame)
  --video <video>                              Path to the local video file or remote video URL
  -h, --help                                   display help for command
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
dlazy kling-v3-omni --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy kling-v3-omni --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
