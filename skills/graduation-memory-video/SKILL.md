---
name: graduation-memory-video
description: "Cinematic graduation video creator with multiple script options. Given one portrait photo, generates keyframe images → Kling first-last-frame transition videos → 15-18s assembled video → piano accompaniment. Script A (default): 6-keyframe graduation journey (high school → doctoral). Script B: 4-keyframe romantic '校草递毕业证' (campus heartthrob hands you a shared graduation photo). Users can also customize shot content. Use when user requests 毕业纪念视频, 校草递毕业证, graduation memory video, graduation tribute, or creative graduation short video."
license: Apache-2.0
compatibility: Requires image generation capability and Python 3.9+ with moviepy for video assembly fallback. Video/music generation tools (Kling, Suno/Mureka) optional — moviepy and Python wave module provide functional fallbacks.
metadata:
  author: theo-lovart
  version: "2.0"
  category: creative-design
---

# Graduation Memory Video Creator

Create a cinematic graduation video from a single portrait photo. Supports multiple script workflows — users choose a preset or customize shot content. Core flow: keyframe images → Kling first-last-frame transition videos → assembled video → piano accompaniment.

**Design philosophy**: Variable-duration cinematic pacing (not uniform 3s/clip). Emotional rhythm where key moments get more screen time. Every transition prompt must demand: smooth, natural, aesthetically beautiful — NO stiff mechanical morphing, NO abrupt cuts.

## Quick Flow

```
Input photo → [Step 0] Choose script → [Step 1] Generate keyframe images → [Step 2] Generate transition videos → [Step 3] Assemble video → [Step 4] Add music
```

---

## Step 0: Script Selection

Before generating anything, confirm which script the user wants:

| Script | Name | Keyframes | Duration | Mood | Default? |
|--------|------|-----------|----------|------|----------|
| **A** | Graduation Journey | 6 | 15-18s | Warm nostalgic, academic journey | ✅ Yes (when user has no specific request) |
| **B** | Campus Heartthrob Hands You Photo | 4 | 12-15s | Romantic surprise, sweet interaction | No |

### Selection logic:
1. User mentions "校草" / "heartthrob" / "递毕业证" / romantic surprise → Script B
2. User has no special request → Script A (default)
3. User wants custom content → Custom mode: user specifies shot count and content, agent designs prompts and transitions

### Custom Mode
Users can modify any preset script or fully customize:
1. User describes desired scenes
2. Agent drafts a shot table with content summary per frame
3. User confirms shot table
4. Agent generates complete prompts and transitions
5. Execute Steps 1-4 with confirmed script

---

## Script A: Graduation Journey (6 keyframes, default)

### Shot Table

| Frame | Scene | Color Tone | Emotion |
|-------|-------|-----------|---------|
| 1 | High school graduation | Bright warm golden-white | Youthful beginning |
| 2 | Bachelor's graduation | Warm rich golden | Growth & confidence |
| 3 | Master's graduation | Warm amber (deeper) | Maturation |
| 4 | Doctoral graduation | Rich saturated red-gold | Academic peak |
| 5 | Doctoral diploma | Soft muted golden | Quiet reflection |
| 6 | Memorial book cover | Warmest soft sunset | Fond closure |

### Transition Map

| Video # | Start Frame | End Frame | Duration | Emotion |
|---------|-------------|-----------|----------|---------|
| 1 | Image 1 (High School) | Image 2 (Bachelor's) | 2-2.5s | Youthful beginning |
| 2 | Image 2 (Bachelor's) | Image 3 (Master's) | 2-2.5s | Growth acceleration |
| 3 | Image 3 (Master's) | Image 4 (Doctoral) | 3-3.5s | Academic peak |
| 4 | Image 4 (Doctoral) | Image 5 (Diploma) | 2.5-3s | Celebration → reflection |
| 5 | Image 5 (Diploma) | Image 6 (Memorial Book) | 2.5-3s | Reflection → closure |
| 6 | Image 6 (Memorial Book) | **No end frame** | 3-4s | Warm closure hold |

Complete prompts in `references/prompt_templates.md`.

---

## Script B: Campus Heartthrob Hands You Photo (4 keyframes)

### Storyline
On a peach blossom-lined campus path, a young handsome man in bachelor's gown stands facing away from the camera. He turns around revealing a surprised and delighted youthful face. He hands a shared graduation photo toward the camera (your POV) — the photo shows him and you (the user) in bachelor's gowns at the campus entrance, both with sunny smiles. The camera focuses in on this photo,定格 the two radiant smiles.

### Shot Table

| Frame | Scene | Color Tone | Emotion |
|-------|-------|-----------|---------|
| 1 | Peach blossom path · back view | Soft pink-golden warm | Mystery: who is he? |
| 2 | Turns around · surprised face | Bright warm vivid | Surprise & heartbeat |
| 3 | Hands shared photo · sunny smile | Warm golden + bright photo | Sweet interaction |
| 4 | Focus on photo · two smiles | Soft warm intimate定格 | Tender closure |

### Two-person Challenge
Frames 3-4 contain TWO different people (the heartthrob + the user). Person consistency is harder than Script A. Strategies:
1. `[HEARTTHROB_DESC]` identical copy-paste across all 4 frames
2. `[USER_DESC]` identical copy-paste across frames 3-4
3. If image-to-image (GPT image2) is available, prefer it for better consistency

### Transition Map

| Video # | Start Frame | End Frame | Duration | Emotion |
|---------|-------------|-----------|----------|---------|
| 1 | Image 1 (back view) | Image 2 (face reveal) | 3-3.5s | Mystery reveal, deliberate pace |
| 2 | Image 2 (surprised face) | Image 3 (hands photo) | 3-3.5s | Heartbeat interaction |
| 3 | Image 3 (hands photo) | Image 4 (focus on photo) | 2.5-3s | Intimate focus |
| 4 | Image 4 (photo定格) | **No end frame** | 3-4s | Tender closure hold |

### Pacing
4 keyframes → ~12-15s total. Each keyframe gets more time than in Script A:

| Segment | Content | Duration | Emotion |
|---------|---------|----------|---------|
| Opening + reveal | Back → face turn | 6-7s | Suspense and surprise need lingering |
| Interaction + closure | Hands photo → focus photo | 5-6s | Sweet interaction unfolds naturally |
| Hold ending | Photo定格 | 3-4s | Tender closure, lingering warmth |

Complete prompts in `references/prompt_templates.md`.

---

## Step 1: Generate Keyframe Images

Use available image generation tool (GPT image-2 preferred for consistency, ImageGen as fallback). Generate all keyframe images in numbered order, confirming each before proceeding.

**⚠️ Person consistency is the #1 challenge.** Text-to-image tools produce different faces each time. Strategies:
- Extract extremely detailed person features from user's photo
- Copy-paste identical person description across all prompts
- If GPT image-2 image-to-image mode is available, prefer it

Parameters: 9:16 vertical, 720×1280, warm cinematic color grading.

---

## Step 2: Generate Transition Videos (Kling First-Last Frame Mode)

### Strict Order
1. Complete Step 1 first — all keyframe images done
2. Then generate videos in order
3. Videos 1→(N-1) use first-last frame mode; Video N uses first-frame-only hold

### First-Last Frame Mode
- `image_url` = start frame (image being transitioned FROM)
- For Kling via Hermes: `reference_image_urls` = [end frame image]
- For direct Kling API: upload both start and end frames

### Prompt Requirements (every video)
1. Describe start and end frame content explicitly
2. **Transition must be smooth, natural, aesthetically beautiful — NO stiff mechanical morphing, NO abrupt cuts**
3. Emotional atmosphere matching the transition's role
4. Color tone continuity — maintain warm progression, no sudden shifts

### If Kling Not Available
Use moviepy crossfade montage as fallback.

---

## Step 3: Assemble Video

Concatenate transition videos with crossfade (0.6-0.8s overlap). Add 1-2s fade-out at end.

Script A: ~15-18s, clip_durations = [2.5, 2.5, 3.5, 3.0, 3.0, 3.5]
Script B: ~12-15s, clip_durations = [3.5, 3.5, 3.0, 3.5]

Resolution: 720×1280, FPS: 30.

---

## Step 4: Add Piano Accompaniment

Script A keywords: `warm piano solo, gentle, nostalgic, graduation memory, emotional, soft melody, no vocals, 18 seconds`
Script B keywords: `warm piano solo, sweet, romantic surprise, youthful heartbeat, gentle melody, no vocals, 15 seconds`

Volume: 30-40%. Fade out last 1.5-2s synchronized with video ending.

---

## Verification

1. All keyframe images exist, person consistency acceptable
2. All transition videos smooth (no jarring cuts)
3. Final video duration matches target, resolution 720×1280
4. Piano music audible at 30-40%, fades out at end
5. Present result to user for review

---

## Lovart成品 Reference

- Theo's Lovart成品: 720×1280 @ 30fps, 18.1s
- 4 main scene segments (~5s → ~6s → ~6.6s), NOT uniform 6×3s
- Variable-duration pacing produces superior emotional impact
