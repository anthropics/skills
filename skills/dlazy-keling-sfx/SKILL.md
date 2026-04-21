---
name: dlazy-keling-sfx
version: 1.0.0
description: Generate matching scene sound effects based on text descriptions or video frames using Kling SFX.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy keling-sfx -h to view help information."}}
---

# dlazy-keling-sfx

Generate matching scene sound effects based on text descriptions or video frames using Kling SFX.

## Trigger Keywords

- kling sfx
- generate sound effects
- video dubbing

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy keling-sfx` command to get results.

```bash
dlazy keling-sfx -h

Options:
  --prompt <prompt>                            Prompt
  --duration <duration>                        Duration (s) (Supports: 3, 4, 5, 6, 7, 8, 9, 10) [Default: 5]
  --prompt_mode <prompt_mode>                  Prompt Mode (Supports: 音效, 配乐, 无) [Default: 音效]
  --sound_effect_prompt <sound_effect_prompt>  Sound Effect Prompt
  --bgm_prompt <bgm_prompt>                    BGM Prompt
  --asmr_mode <asmr_mode>                      ASMR Mode [Default: false]
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
dlazy keling-sfx --prompt 'prompt text'

# complex call:
dlazy keling-sfx --prompt 'prompt text'
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
