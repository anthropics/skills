---
name: dlazy-doubao-tts
version: 1.0.0
description: Synthesize text into natural and fluent speech using Doubao TTS.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy doubao-tts -h to view help information."}}
---

# dlazy-doubao-tts

Synthesize text into natural and fluent speech using Doubao TTS.

## Trigger Keywords

- doubao tts
- text to speech
- generate speech
- voice broadcast

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy doubao-tts` command to get results.

```bash
dlazy doubao-tts -h

Options:
  --prompt <prompt>                  Prompt
  --voice_language <voice_language>  Voice Language (Supports: zh-cn, en)
                                     [Default: zh-cn]
  --voiceId <voiceId>                Voice ID [Default:
                                     zh_female_shuangkuaisisi_uranus_bigtts]
  --speed_ratio <speed_ratio>        Speed Ratio (Supports: 0.8, 1.0, 1.2, 1.5,
                                     2.0) [Default: 1.0]
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
dlazy doubao-tts --prompt 'prompt text'

# complex call:
dlazy doubao-tts --prompt 'prompt text'
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
