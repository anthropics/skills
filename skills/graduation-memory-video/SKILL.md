---
name: graduation-memory-video
description: Create a cinematic graduation tribute video from a person's photo. Generates 6 graduation scene images (high school through doctoral, diploma, memorial book cover) with Chinese academic gown colors, then composes them into a 15-18 second video with piano accompaniment using variable-duration cinematic pacing. Use this when users request a graduation memory video, graduation tribute, graduation photo slideshow, 毕业纪念视频, or any request to create a video commemorating academic milestones from a portrait photo.
license: Apache-2.0
compatibility: Requires image generation capability and Python 3.9+ with moviepy for video assembly fallback. Video/music generation tools (Kling, Suno/Mureka) optional — moviepy and Python wave module provide functional fallbacks.
metadata:
  author: theo-lovart
  version: "1.1"
  category: creative-design
---

# Graduation Memory Video Creator

Create a heartfelt cinematic graduation tribute video from a single portrait photo — spanning from high school through doctoral degree, ending with a diploma and memorial book cover.

**Core Design Philosophy**: This is NOT a mechanical slideshow with equal-duration clips. It follows cinematic narrative pacing — key scenes (doctoral graduation, memorial book ending) receive longer screen time while transitional scenes move faster, creating natural emotional breathing room. Reference analysis from Lovart成品 shows real videos use 4 main scene blocks (~5s→~6s→~6.6s) rather than uniform 6×3 seconds.

If video/music generation tools (Kling, Suno/Mureka) are not available in the current environment, fall back to moviepy crossfade montage (variable-duration clips) and Python wave module for placeholder audio. Always inform the user about the fallback and its limitations before proceeding.

## Workflow Overview

```
Input photo → [Step 1] Generate 6 graduation scene images → [Step 2] Create transition videos → [Step 3] Assemble video → [Step 4] Add piano music → Final output
```

## Step 1: Generate 6 Graduation Scene Images

Use the available image generation tool to create 6 images in 9:16 (vertical/portrait) aspect ratio. Each image must maintain person consistency based on the user's reference photo.

### ⚠️ Person Consistency Challenge

**This is the skill's greatest challenge.** If the environment supports image-to-image generation (reference image input), prioritize that mode for better consistency. If only text-to-image is available, describe the person's features in extreme detail in every prompt — and use the EXACT SAME description text across all 6 prompts (copy-paste, never abbreviate or rephrase). Consistency takes priority over brevity.

After generating all 6 images, show them to the user for approval before proceeding. If any image deviates too much from the person's appearance, regenerate that specific image.

### 6 Images Summary

Load `references/prompt_templates.md` for complete prompt templates. Key points:

1. **High School** — Chinese high school uniform (蓝白配色运动校服), school corridor with warm morning light, youthful smile
2. **Bachelor's** — Chinese bachelor's gown (黑色学士服 with 粉色领饰), tree-lined campus path, library background
3. **Master's** — Chinese master's gown (蓝色硕士服 with 藏蓝色领饰), ginkgo-lined autumn path, graduate school entrance
4. **Doctoral** — Chinese doctoral gown (红色博士服 with 红色领饰), traditional Chinese building with "学术报告厅" plaque, peach blossoms
5. **Diploma** — Doctoral diploma on sunlit wooden desk, portrait visible, university name obscured
6. **Memorial Book Cover** — Closed book with "毕业纪念册" title, sunset-like warm lighting

### Color Tone Progression

The 6 images follow an intentional emotional color progression:

| Scene | Color Character | Emotional Mapping | Key Words |
|-------|----------------|-------------------|-----------|
| High School | Bright warm, white-gold | Youthful beginnings | bright warm, golden highlights |
| Bachelor's | Rich golden, warm spring | Growing confidence | rich golden, warm spring |
| Master's | Amber warm, deeper | Depth and maturity | amber, burnt sienna |
| Doctoral | Slightly more saturated, red-gold | Peak achievement | richer saturation, red-gold |
| Diploma | Soft muted yellow, receding | Quiet reflection | muted golden, softer |
| Memorial Book | Warmest, softest sunset tones | Closure and fond memory | warmest, softest, sunset-like |

### Key Parameters

- **Aspect ratio**: 9:16 (vertical) for all images
- **Resolution**: 720×1280 (standard mobile vertical) or higher
- **Style**: Warm cinematic film grain, shallow depth of field, golden hour lighting
- **Cultural**: Chinese university degree gown styles (not Western)
- **Person description**: MUST be identical text across all 6 prompts

## Step 2: Create Transition Videos

Use Kling's **First-Last Frame mode** to create transition videos. This is the core generation method — Kling takes a start frame image and an end frame image as input, and AI-generates the smooth transition animation between them.

### ⚠️ Strict Generation Order

1. **Complete Step 1 first**: Generate all 6 graduation scene images in order (1→6), confirming each image's quality before proceeding to the next
2. **Then generate videos**: Only start Step 2 after all 6 images are finished
3. **Generate videos in order**: Videos 1→5 use first-last frame mode sequentially, Video 6 uses first-frame-only mode

### First-Last Frame Mode Details

Kling's first-last frame mode allows you to provide both a starting frame image and an ending frame image — Kling automatically generates the smooth transition animation between them. This ensures continuity: each video's end frame is the next video's start frame, forming a perfect chain.

**Generation rules**:
- **Videos 1-5**: Use first-last frame mode. Start frame = previous image, End frame = next image
- **Video 6**: Use first-frame-only mode (no end frame needed). Start frame = Image 6, static hold + slow fade-out

| Video # | Start Frame Image | End Frame Image | Transition Description | Suggested Duration | Emotional Role |
|---------|-------------------|----------------|----------------------|--------------------|----------------|
| 1 | Image 1 (High School) | Image 2 (Bachelor's) | School corridor → campus path | 2-2.5s | Youthful beginning |
| 2 | Image 2 (Bachelor's) | Image 3 (Master's) | Library path → ginkgo path | 2-2.5s | Growth acceleration |
| 3 | Image 3 (Master's) | Image 4 (Doctoral) | Graduate school → ancient building | 3-3.5s | Academic peak |
| 4 | Image 4 (Doctoral) | Image 5 (Diploma) | Peach blossoms → sunlit desk | 2.5-3s | Celebration → reflection |
| 5 | Image 5 (Diploma) | Image 6 (Memorial Book) | Diploma → memorial book | 2.5-3s | Reflection → closure |
| 6 | Image 6 (Memorial Book) | **No end frame** | Memorial book static hold ending | 3-4s | Warm closure |

**Video 6 special handling**: Only provide Image 6 as the start frame — no end frame. Kling will generate a slow static hold + fade-out ending (3-4 seconds), giving viewers time to absorb the emotional conclusion.

### Transition Prompt Requirements

Each video's prompt must include:
1. **Explicit start and end frame content description** (e.g., "starting from school corridor scene, naturally transitioning to campus path scene")
2. **Transition style**: Smooth, natural, aesthetically beautiful — **no stiff mechanical morphing, no abrupt cuts**. This is critical.
3. **Emotional atmosphere description**: Each transition should echo its emotional role (e.g., Video 3 is "academic peak" — needs dignified pacing)
4. **Color tone continuity**: Maintain warm color progression throughout the transition — no sudden color shifts

Complete prompt templates in `references/prompt_templates.md`.

### Cinematic Pacing Strategy

**Do NOT use equal-duration clips.** The video should have emotional rhythm with breathing room:

| Scene Segment | Content | Suggested Duration | Emotional Role |
|---------------|---------|--------------------|----------------|
| Opening | High school → Bachelor's | 4-5 seconds | Let viewers enter the emotion |
| Middle 1 | Bachelor's → Master's | 2.5-3 seconds | Growth acceleration, compact |
| Middle 2 | Master's → Doctoral | 4-5 seconds | Academic peak, more time here |
| Closing | Doctoral → Diploma → Memorial book | 5-6 seconds | Reflective ending, unhurried |

Total: approximately 15-18 seconds.

### If Kling is Not Available

If Kling is not available in the current environment, use moviepy crossfade montage as a fallback — still achieves smooth visual transitions, but no AI-generated continuous camera motion. See Step 3 for moviepy fallback parameters.

## Step 3: Assemble Video

Combine transition videos into a complete video:

- **Total duration**: ~15-18 seconds (variable pacing per Step 2)
- **Assembly order**: Video 1 → 6, seamless with crossfade transitions
- **Remove original audio**: Strip all source audio tracks
- **Ending**: Last 1-2 seconds slow fade to black or white, giving viewers a natural pause

### moviepy Montage Fallback

If using moviepy image montage (instead of Kling video transitions), use these parameters:

```python
# Variable clip durations per image (cinematic pacing)
clip_durations = [2.5, 2.5, 3.5, 3.0, 3.0, 3.5]  # high school through memorial book
# Crossfade overlap duration
transition_duration = 0.6  # 0.6 seconds overlap
# Image dimensions (matching Lovart reference standard)
size = (720, 1280)  # 9:16 vertical standard
# Each image loaded as ImageClip with set duration
# Use CompositeVideoClip + CrossFadeIn for fade transitions
# Total ≈ sum(clip_durations) - 5*transition_duration ≈ 15 seconds
# Plus 2-second ending fade-out ≈ 17 seconds
```

**Note**: moviepy v2.x does NOT have `moviepy.editor` module. Correct import: `from moviepy import VideoFileClip, ImageClip, CompositeVideoClip`

## Step 4: Add Piano Accompaniment

Use Suno or Mureka to generate warm piano solo music. If not available, use Python + wave/pydub module to create a simple piano-style WAV placeholder, or ask the user to provide their own music file. Inform the user about the fallback before proceeding.

- **Style**: Warm, healing, nostalgic, piano solo
- **Duration**: Match video length exactly (15-18 seconds)
- **Requirements**: Pure music, no vocals, gentle rhythm
- **Prompt keywords**: "warm piano solo, gentle, nostalgic, graduation memory, emotional, soft melody, no vocals, 18 seconds"
- **Volume**: Background volume soft (30-40% of total), never overpowering
- **Ending**: 2-second fade-out synchronized with video fade-out

Combine audio and video into the final output.

## Adaptation Variants

The core structure can adapt to different variants while keeping the workflow unchanged:

- **Stage count**: User may request only some stages (e.g., bachelor's + master's only)
- **Degree type**: Can swap Chinese/Western degree gown styles
- **Scene customization**: User may specify specific campus scenes
- **Duration**: Adjust individual clip durations (2-5 seconds), total varies accordingly
- **Music style**: Swap piano for strings, guitar, etc.
- **Pacing preference**: User may prefer uniform pacing — use equal 3s/clip in that case

## Chinese Degree Gown Color Reference

| Degree Level | Gown Color | Trim Color | Visual Meaning |
|-------------|-----------|-----------|---------------|
| Bachelor's | Black | Pink trim (文科) | Foundation, warm start |
| Master's | Blue | Dark blue trim | Depth and rigor |
| Doctoral | Red | Red trim + black border | Peak achievement, honor |

If user specifies a specific discipline, adjust trim colors accordingly. Default uses pink trim ( humanities/arts).

## Lovart Reference Analysis

Based on analysis of a real Lovart成品 video (Theo's production):

- **成品 parameters**: 720×1280 @ 30fps, 18.1s, audio 44100Hz
- **Scene rhythm**: 4 main scene blocks (~5s→~6s→~6.6s), not uniform 6×3 seconds
- **Key finding**: Real成品 videos use natural breathing rhythm — longer opening (emotional entry), faster middle transitions, unhurried closing
- **Visual style**: Warm cinematic tones, crossfade transitions (never hard cuts)

This analysis informed Step 2's pacing strategy and Step 3's assembly parameters.

## Resources

- `references/prompt_templates.md` — Complete prompt templates for all 6 images and 6 transition videos, including person description extraction guide and color tone progression table
