---
name: dlazy-jimeng-omnihuman-1.5
version: 1.0.0
description: Generate realistic digital human broadcast videos from portrait images and audio/text using Jimeng OmniHuman 1.5.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy jimeng-omnihuman-1.5 -h to view help information."}}
---

# dlazy-jimeng-omnihuman-1.5

Generate realistic digital human broadcast videos from portrait images and audio/text using Jimeng OmniHuman 1.5.

## Trigger Keywords

- digital human
- jimeng omnihuman
- generate digital human video
- virtual human broadcast

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy jimeng-omnihuman-1.5` command to get results.

```bash
dlazy jimeng-omnihuman-1.5 -h

Options:
  --generation_mode <generation_mode>  Generation Mode (Supports: Components)
                                       [Default: Components]
  --audio <audio>                      Audio
  --audioDuration <audioDuration>      Audio Duration
  --prompt <prompt>                    Prompt
  --resolution <resolution>            Resolution (Supports: 720p, 1080p)
                                       [Default: 1080p]
  --fast_mode <fast_mode>              Fast Mode [Default: false]
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
dlazy jimeng-omnihuman-1.5 --prompt 'prompt text' --image '/path/to/image.png'

# complex call:
dlazy jimeng-omnihuman-1.5 --prompt 'prompt text' --image 'https://oss.dlazy.com/image.png'
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
