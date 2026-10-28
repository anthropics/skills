---
name: avatar-mix
description: Create a 16:9 and 9:16 video with your HeyGen avatar presenting content, with a dynamic edit alternating between fullscreen avatar, avatar-in-corner over background, and background-only modes, with transitions, music, and SFX. Accepts a URL or a script. Use when the user wants to generate an avatar video from a webpage or a script.
---

# avatar-mix

Pipeline to produce 16:9 (1920x1080) and 9:16 (1080x1920) videos where the user's HeyGen avatar presents content over generated backgrounds, with an edit alternating between 3 modes.

Source repository: https://github.com/Upload-Post/avatar-mix

## Engines
- **HeyGen MCP** (https://mcp.heygen.com/mcp/v1/, OAuth) — talking avatar + audio/SFX.
- **HyperFrames** (npx hyperframes) or PIL cards — background video.
- **FFmpeg** (scripts/composite.py) — compositing, transitions, audio mix.

## Avatar Identity (user config)
Copy config/avatar.example.json to config/avatar.json and fill in avatar_id + voice_id (discover with list_avatar_looks / list_voices MCP tools; get_current_user for the account).
config/avatar.json is in .gitignore (personal). Default engine: Avatar V.
Recommended HeyGen plan: Creator (600 credits). Free plan does not support multiple scenes or TTS.

## The 3 Scene Modes
- **fullscreen** — avatar full screen (always starts on this mode).
- **corner** — full-screen background + avatar in PiP webcam box. Background is NOT removed. In 16:9 it goes bottom-right (~28%). In 9:16 it goes centered bottom, larger (~58%).
- **bg_only** — background only; avatar voice continues as voice-over.

## Workflow (strict order due to dependencies)

### 0. Config (once)
Fill config/avatar.json with avatar_id and voice_id (use MCP tools list_avatar_looks and list_voices).
Verify: ffmpeg -version, node -v (>=22), MCP connected (get_current_user).

### 1. Input to scene script
If source is URL, use WebFetch to extract content. If script, use as-is.
Write spoken script and segment into scenes. Create work/<slug>/script.json (see templates/script.example.json).
Rules: Scene 1 = fullscreen. Alternate corner / bg_only / fullscreen to match content rhythm.
Each scene: id, mode, narration, bg_visual (headline, subline/bullets, style), transition (fade|slide|cut), transition_after_sec.
bg_visual style: title_card | bullets | fullbleed | screenshot (with image).

### 2. Avatar (HeyGen MCP) — one clip per scene
For each scene, call mcp__heygen__create_video_from_avatar with avatarId, voiceId, script = narration, aspectRatio: "16:9", resolution: "1080p" (use 720p for tests), and ALWAYS engine: {"type": "avatar_v"}.
Poll with mcp__heygen__get_video until completed; get video_url.
Download to work/<slug>/clips/avatar_<id>.mp4.
In bg_only the clip is generated the same way; the composite only uses its audio.

### 3. Measure durations
For each clip: ffprobe -v error -show_entries format=duration -of default=nk=1:nw=1 clip.
Write duration (seconds) into each scene in script.json. Required before step 4.

### 4. Backgrounds (one per scene)
Golden rule: backgrounds must be custom animated explanatory graphics, NOT website screenshots.
Generate with HyperFrames mock-ups and data-viz. Use hyperframes capture <url> only occasionally.

HyperFrames flow: two projects per format: work/<slug>/hf/ (16:9) and work/<slug>/hf_9x16/ (vertical).
Run: python3 scripts/make_bg.py --slug <slug> --mode hyperframes --aspect 16:9|9:16

### 5. Music and SFX (HeyGen MCP) — contextual per video
- Music: search_audio_sounds (type=music) with music_query to assets/music.*
- Base SFX: transition whoosh to assets/sfx/whoosh.mp3
- Contextual SFX: search for effects that match the video content (riser on intro, coins when talking about money, chime when a chat appears, achievement on completion)
- Write manifest work/<slug>/sfx_manifest.json: [{ "scene": <id>, "offset": <sec>, "file": "assets/sfx/x.mp3", "gain_db": -12 }]

### 6. Composite (FFmpeg)
python3 scripts/composite.py --slug <slug> --aspect 16:9|9:16 [--music ...] [--whoosh assets/sfx/whoosh.mp3] [--sfx-manifest work/<slug>/sfx_manifest.json]
Produces output/<slug>{_9x16}.mp4 with 3 modes, transitions, music with ducking, and SFX. Output is metadata-free.
Dual format shortcut: bash scripts/run.sh <slug> <music> <card|hyperframes> both

### 6.5 Hormozi-style captions (recommended for 9:16)
- Word timing: mcp__heygen__create_speech per scene returns word_timestamps -> save in work/<slug>/captions_src.json
- python3 scripts/make_captions.py --slug <slug> --aspect 9:16
- python3 scripts/burn_captions.py --slug <slug> --aspect 9:16
- Produces output/<slug>_9x16_subs.mp4

### 7. Deliver
Show path to output/<slug>.mp4 and a summary of scenes/duration.

### 8. Publish to social networks (Upload-Post API)
Upload both formats with scripts/publish.sh (direct local file upload, no public URL needed).
- Vertical (with subs): bash scripts/publish.sh output/<slug>_9x16_subs.mp4 <profile> tiktok,instagram,youtube,threads "<title>" "<desc>" "#hashtags" REELS
- Horizontal: bash scripts/publish.sh output/<slug>.mp4 <profile> youtube,linkedin,facebook,x "<title>" "<desc>"
Always confirm before publishing.

## Requirements
- HeyGen account (Creator plan recommended, $29/mo, 600 credits)
- HeyGen avatar + voice (digital twin)
- HeyGen MCP connected (OAuth at /mcp) or HEYGEN_API_KEY in .env
- Upload-Post account for publishing (UPLOAD_POST_API_KEY in .env)
- FFmpeg, Node >= 22, Python 3 + Pillow
