---
name: dlazy-video-generate
version: 1.0.0
description: Video generation skill. Automatically selects the best dlazy CLI video model based on the prompt.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, automatically select the corresponding dlazy subcommand."}}
---

# dlazy-video-generate

Video generation skill. Automatically selects the best dlazy CLI video model based on the prompt.

## Trigger Keywords

- generate video
- text to video
- animate image

## Usage

This skill handles all video generation requests by selecting the best `dlazy` video model.

### Available Video Models
- `dlazy veo-3.1`, `dlazy veo-3.1-fast`: High-quality cinematic sequences.
- `dlazy sora-2`, `dlazy sora-2-pro`: Narrative clips.
- `dlazy kling-v3`, `dlazy kling-v3-omni`: General short clips.
- `dlazy seedance-1.5-pro`: Narrative shorts with transitions.
- `dlazy wan2.6-r2v`, `dlazy wan2.6-r2v-flash`: General/fast video production.
- `dlazy viduq2-i2v`, `dlazy jimeng-i2v-first`, `dlazy jimeng-i2v-first-tail`, `dlazy jimeng-dream-actor`, `dlazy jimeng-omnihuman-1.5`: Image-to-video, digital human, action transfer.

**CRITICAL INSTRUCTION FOR AGENT**: 
1. Select the most appropriate video model.
2. Run `dlazy <model_name> -h` to check parameters.
3. Execute the command.
4. If the output returns `code: 503` and indicates insufficient balance, you MUST inform the user and provide this link to recharge: [https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits](https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits)


## Error Handling

| Code | Error Type                         | Example Message                                                                                                          |
| ---- | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| 501  | Missing required parameter         | `error: required option '--prompt <prompt>' not specified`                                                              |
| 502  | Local file read error              | `Error: Image file/Video file not found: C:\path\to\your\file`                                                          |
| 503  | API request failed (no balance)    | `Error during API request: Request failed with status code 400` / `Response details: {"error": "Insufficient balance"}` |
| 503  | API request failed (server error)  | `HTTP status code error (500 server crash)`                                                                             |
| 504  | Asynchronous task execution failed | `=== Generation Failed ===` / `{Specific error reason returned by backend, for example "Prompt violates safety policy"}` |

## Tips

Visit https://dlazy.com for more information.
