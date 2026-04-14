---
name: dlazy-keling-tts
version: 1.0.0
description: Convert text into high-quality, emotional speech reading using Kling TTS.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy keling-tts -h to view help information."}}
---

# dlazy-keling-tts

Convert text into high-quality, emotional speech reading using Kling TTS.

## Trigger Keywords

- kling tts
- text to speech
- generate speech

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy keling-tts` command to get results.

```bash
dlazy keling-tts -h

Options:
  --prompt <prompt>                  Prompt
  --voice_language <voice_language>  Voice Language (Supports: zh, en)
                                     [Default: zh]
  --voiceId <voiceId>                Voice ID [Default: genshin_vindi2]
  --speed <speed>                    Speed (Supports: 0.8, 1.0, 1.5) [Default:
                                     1.0]
  --format <format>                  Format (Supports: mp3, wav) [Default: mp3]
  -h, --help                         display help for command
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
dlazy keling-tts --prompt 'prompt text'

# complex call:
dlazy keling-tts --prompt 'prompt text'
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
