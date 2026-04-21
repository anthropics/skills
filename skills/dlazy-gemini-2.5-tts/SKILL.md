---
name: dlazy-gemini-2.5-tts
version: 1.0.0
description: Generate multilingual, highly natural audio using Gemini 2.5 text-to-speech.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, you can run dlazy gemini-2.5-tts -h to view help information."}}
---

# dlazy-gemini-2.5-tts

Generate multilingual, highly natural audio using Gemini 2.5 text-to-speech.

## Trigger Keywords

- gemini tts
- text to speech
- generate speech

## Usage

**CRITICAL INSTRUCTION FOR AGENT**: 
Run the `dlazy gemini-2.5-tts` command to get results.

```bash
dlazy gemini-2.5-tts -h

Options:
  --prompt <prompt>                  Prompt
  --voice_language <voice_language>  Voice Language (Supports: cmn, en)
                                     [Default: cmn]
  --voiceName <voiceName>            Voice Name [Default: Kore]
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
dlazy gemini-2.5-tts --prompt 'prompt text'

# complex call:
dlazy gemini-2.5-tts --prompt 'prompt text'
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
