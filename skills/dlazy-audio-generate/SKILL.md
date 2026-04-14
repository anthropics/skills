---
name: dlazy-audio-generate
version: 1.0.0
description: Audio generation skill. Automatically selects the best dlazy CLI audio/TTS model based on the prompt.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, automatically select the corresponding dlazy subcommand."}}
---

# dlazy-audio-generate

Audio generation skill. Automatically selects the best dlazy CLI audio/TTS model based on the prompt.

## Trigger Keywords / 触发关键词

- generate audio
- text to speech, TTS
- generate music, sound effect

## Usage / 使用方法

This skill handles all audio generation requests by selecting the best `dlazy` audio model.

### Available Audio Models
- `dlazy gemini-2.5-tts`, `dlazy doubao-tts`, `dlazy keling-tts`: Text-to-speech.
- `dlazy suno.music`: Music generation.
- `dlazy keling-sfx`: Sound effects.
- `dlazy vidu-audio-clone`, `dlazy kling-audio-clone`: Voice cloning.

**CRITICAL INSTRUCTION FOR AGENT**: 
1. Select the most appropriate audio model.
2. Run `dlazy <model_name> -h` to check parameters.
3. Execute the command.
4. If the output returns `code: 503` and indicates insufficient balance, you MUST inform the user and provide this link to recharge: [https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits](https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits)


## Error Handling / 错误处理

| Code | Error Type                         | Example Message                                                                                                          |
| ---- | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| 501  | Missing required parameter         | `error: required option '--prompt <prompt>' not specified`                                                              |
| 502  | Local file read error              | `Error: Image file/Video file not found: C:\path\to\your\file`                                                          |
| 503  | API request failed (no balance)    | `Error during API request: Request failed with status code 400` / `Response details: {"error": "Insufficient balance"}` |
| 503  | API request failed (server error)  | `HTTP status code error (500 server crash)`                                                                             |
| 504  | Asynchronous task execution failed | `=== Generation Failed ===` / `{Specific error reason returned by backend, for example "Prompt violates safety policy"}` |

## Tips

Visit https://dlazy.com for more information.
