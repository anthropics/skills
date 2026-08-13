---
name: paper-explainer-video-en
description: Turn a paper into a short ENGLISH explainer video (Manim animation + edge-tts English voiceover + synthesized BGM + a Live2D anime virtual host reading the script). Use when the user says "make an English explainer/science video of this paper", "explain this paper with manim in English", "add an English voiceover / anime host / Live2D narrator", etc. For a Chinese-language video, use the sibling skill paper-explainer-video instead.
---

# Paper → English explainer video pipeline

Turn one paper into a 3–5 minute **English** popular-science video. Deliverables:
- Per-scene animation rendered with Manim (1080p60)
- edge-tts **English** voiceover (each sentence aligned to the on-screen beat)
- Royalty-free BGM (a synthesized ambient pad)
- A Live2D anime virtual host in the bottom-right corner, lip-sync driven in real time by the voiceover volume
- Auto cross-fade transitions, an intro title card, and an end-card with references

`assets/` holds the **generic scripts** (rarely need editing). Per paper you only rewrite 3 files:
`scenes.py` (animation), `narration_data.py` (narration), `pipeline_config.py` (scene list / title / voice).

---

## ⚠️ Three iron rules (hard-won; always follow)

1. **Always render from a non-iCloud local venv.** If the project lives in an iCloud-synced
   Desktop/Documents folder, a `.venv` there gets repeatedly evicted by iCloud and renders
   randomly hang/time out on import (Errno 60). Use `~/llm_mc_venv` (setup.sh builds it).
2. **Do the heavy work in a local `/tmp` dir; copy only the final file back.** All
   render/mux reads & writes go through `/tmp/paper_build` to dodge iCloud stalls; `cp` the
   finished mp4 back to the project at the end.
3. **Check disk first.** `df -h /tmp`. Live2D raw frames are big — this pipeline pipes the
   host's **raw RGBA frames straight into ffmpeg** with no large intermediate file (keeps
   transparency AND saves disk). Do NOT store a whole avatar pass as qtrle/.mov (800MB+).

---

## One-time environment setup

```bash
bash ./assets/setup.sh
```
It will: create `~/llm_mc_venv` → install manim / edge-tts / live2d-py / glfw / PyOpenGL / numpy / scipy / pillow
→ shallow-clone live2d-py to grab free sample models into `/tmp/live2dpy` (incl. llny / Mao / Haru).
You also need `ffmpeg` and `ffprobe` installed system-wide (`brew install ffmpeg`). English on-screen
text uses a Latin font (default **Helvetica Neue**, always on macOS); PingFang SC is still available
via `cn()` for any CJK (e.g. an author's name).

---

## Per-paper workflow

Let the new project dir be `$PROJ` (holds the paper + final mp4); local workspace `MC=/tmp/paper_build`.

### 0) Copy the generic scripts into the project
```bash
cp ./assets/{make_bgm,narrate,build_video,render_avatar,pipeline_config,narration_data,scene_helpers}.py "$PROJ"/
cp ./assets/status.sh "$PROJ"/
```

### 1) Read the paper, design 5–8 scenes
Read the paper (txt/pdf) in `$PROJ`. Design a scene sequence; a typical structure:
1. `IntroScene` — intro title card: paper title / authors / arXiv + "Today, let's read this paper together."
2. `HookScene` — a hook: a question or counter-intuitive fact that makes people want to keep watching
3–6. Core-mechanism scenes — each conveys ONE intuition, with a Manim animation (curves / histograms / distribution evolution / contrasts)
7. `ConclusionScene` — conclusion + a punchy closing line
8. `ReferencesScene` — end-card references (authors, title, arXiv)

Principles (see `reference/`):
- No math dumps — one scene, one intuition; each animation ≤ ~15s; no dead air within 5 minutes.
- **Precompute every random process with a fixed seed** (put it in a data module like
  `model_collapse_data.py`); never draw random numbers inside a scene → identical, iterable renders.
- English text uses `txt(..., font="Helvetica Neue")` (the helper's default); keep `cn()` for any CJK.
- ⚡ **Never use `MathTex` for changing numbers/labels**: it spawns a `latex` subprocess every
  time — extremely slow. Real measurement: per-generation μ/σ MathTex made one scene jump from
  75s to 183s (half the total). For numbers that change per-generation/per-frame use `Text`
  (type the unicode directly: `μ σ Σ √ …`) or `DecimalNumber` (animatable). Only use MathTex for
  a **fully static formula that genuinely needs typesetting** (and `export PATH` to include latex).
- Quote the paper's own text/figures (e.g. an LLM-output sample, a key figure) directly and attribute them.

### 2) First write narration_data.py + pipeline_config.py (**not scenes.py yet**)
- `narration_data.py`: `NARRATION = [[...sentences for each scene...], ...]` (order matches SCENES);
  `SCENE_RATES = {i: "+12%"}` to individually speed up a scene whose narration runs long.
- `pipeline_config.py`: `SCENES` (ordered scene class names), `OUTPUT_BASENAME`, `VOICE`/`PITCH`,
  `AVATAR` (host framing/position), `L2D_MODEL`, `USE_AVATAR`.

### 2.5) ★ Run TTS first to get each scene's real audio length (key! saves a full re-render)
**Don't guess `self.wait()` durations.** Lesson learned: finishing scenes only to find the
voiceover is longer than the visuals → editing 17 waits → re-rendering everything = 5–7 wasted
minutes. Correct order: generate audio first, get the durations, THEN write scenes to them.
```bash
cd "$MC" && $V narrate.py 2>&1 | grep -E "scene[0-9]"
# prints e.g.:  scene0  20.6s  108 chars / scene1  28.4s  136 chars / ...
```
Record those N durations.

### 2.6) Then write scenes.py (set waits from audio length + keep clear of the host)
- For each `construct`, **(sum of all run_time + all wait) ≥ that scene's audio length + ~1.5s buffer** — get it right the first time.
- **Bottom-right is the host zone** (if `USE_AVATAR`). Put key content (curve tails, readouts,
  captions) elsewhere; while iterating, set `SHOW_AVATAR_ZONE=1` so each scene draws a red
  keep-clear box (see `assets/scene_helpers.py`):
  ```python
  from scene_helpers import txt, add_avatar_guard   # txt=Latin Text; guard=host red box (debug)
  class FooScene(Scene):
      def construct(self):
          add_avatar_guard(self)   # shows the host placeholder box when SHOW_AVATAR_ZONE=1; hidden in the final render
          ...
  ```
  This way you design around the bottom-right corner → avoid discovering Live2D occlusion only
  after rendering and re-rendering (saves 3–5 min).
- Manim scene classes: see `reference/scenes_example.py`.

### 3) Render the scenes (local venv, parallel + cache on + two quality tiers)
```bash
MC=/tmp/paper_build; V=~/llm_mc_venv/bin/python
export PATH="/Library/TeX/texbin:$PATH"   # ★ required! MathTex scenes need latex on PATH or they fail silently
rm -rf "$MC"; mkdir -p "$MC"; cp "$PROJ"/{scenes,pipeline_config,narration_data,make_bgm,narrate,build_video,render_avatar,scene_helpers}.py "$MC"/ 2>/dev/null
cp "$PROJ"/<data_module>.py "$MC"/ 2>/dev/null
cd "$MC"

# Iteration: low quality (-ql 480p15, ~16x faster than -qh), 4-way parallel. Re-run after layout/timing edits.
SCENES=$($V -c "import pipeline_config as c;print(' '.join(c.SCENES))")
Q=1080p60   # use the -ql dir name while iterating; shown here at final quality
render() { # usage: render <quality-flag> <quality-dir>
  printf '%s\n' $SCENES | xargs -P 4 -I{} bash -c '
    S={}; for a in 1 2 3; do
      [ -f media/videos/scenes/'"$2"'/$S.mp4 ] && exit 0
      '"$V"' -m manim '"$1"' --media_dir "'"$MC"'/media" scenes.py $S >/tmp/r_$S.log 2>&1
      [ -f media/videos/scenes/'"$2"'/$S.mp4 ] && exit 0
    done; echo "FAILED $S; tail /tmp/r_$S.log"'
}
render -ql 480p15      # iterate: fast; sampled frames still reveal layout/out-of-bounds/axis-crop issues
# After locking the cut, render final quality:
render -qh 1080p60
```
Notes:
- **No more `--disable_caching`** — that was only to dodge iCloud, but the workspace is in `/tmp`
  (iCloud doesn't touch it). With caching on, unchanged `play()` blocks reuse their partial movie
  file → iteration is several times faster. After editing a **data module**, clear the cache once:
  `rm -rf "$MC"/media/{Tex,texts}` or run once with `--flush_cache`.
- **Parallel `-P 4`** (scenes are independent). If memory is tight / caches collide, drop to `-P 2`.
- **Two tiers**: 95% of the time you're iterating layout/timing — use `-ql`; switch to `-qh` only
  for the final cut / syncing the voiceover (or `-qm` 720p as a middle ground).
- Frame-check self-review in step 8 (low-quality frames still expose layout problems).

### 4) Voiceover (already generated in 2.5) + recheck
The voiceover was generated in step 2.5. Here just recheck: **each scene's audio ≤ that scene's
on-screen duration** (you already set the waits from audio length in 2.6, so it should hold).
Only re-run `cd "$MC" && $V narrate.py` if you **edited `narration_data.py`** (parallel, ~10s).
> BGM (step 5) has no dependency on rendering — run it in the background during step 3:
> `$V make_bgm.py 240 bgm.wav &` … `wait`.

### 5) BGM
```bash
$V make_bgm.py <total_seconds±margin> bgm.wav   # e.g. 240
```

### 6) Build the base video (transitions + voiceover + BGM)
```bash
/opt/homebrew/bin/python3 build_video.py 1080p60 bgm.wav   # build_video uses only the stdlib
mv -f "$(python -c 'import pipeline_config as c;print(c.OUTPUT_BASENAME)')_1080p60.mp4" base_video.mp4
```
> Faster preview while iterating: `MC_FAST=1 python3 build_video.py ...` (uses h264_videotoolbox
> hardware encode, 5–10x faster; drop it for the final).

### 7) Live2D host → mux directly into the final (when `USE_AVATAR=True`)
```bash
$V render_avatar.py     # reads base_video.mp4 timeline for lip-sync; pipes raw RGBA straight to the final (no big intermediate)
cp "$(python -c 'import pipeline_config as c;print(c.OUTPUT_BASENAME)')_live2d.mp4" "$PROJ"/
cp base_video.mp4 "$PROJ/$(python -c 'import pipeline_config as c;print(c.OUTPUT_BASENAME)')_1080p60.mp4"
```
> Also supports `MC_FAST=1 $V render_avatar.py` for a hardware-encoded preview.
> **`USE_AVATAR=False` (FAST mode)**: skip this step; the final is just `base_video.mp4` (saves 3–5 min).

### 8) Frame-check self-review (do it every time)
Sample frames after every change — don't go by feel:
```bash
ffmpeg -y -ss <sec> -i final.mp4 -frames:v 1 /tmp/chk.png      # full frame
ffmpeg -y -ss <sec> -i final.mp4 -filter_complex "crop=400:300:1380:780,scale=520:-1" -frames:v 1 /tmp/zoom.png  # zoom on host
```
Open the png with Read. Check: ① the host's **whole face** is in frame (not half); ② the host's
background is **transparent** (not a black box); ③ during silence the host's **mouth is closed**
(proves lip-sync is real); ④ captions/curves aren't occluded by the host.

Check progress anytime: `bash status.sh` (or `-w` to auto-refresh).

---

## Live2D host: key parameters & troubleshooting

Host parameters live in `pipeline_config.AVATAR`:
- `scale` / `offset_x` / `offset_y`: the camera. **The model's face sits to the right by default,
  so you MUST use offset_x to center it**, or the face's right half gets clipped when it sways →
  the classic "half face". Current llny: `scale 1.55, offset_x -0.3, offset_y -1.55, W 380, H 388`.
- To tune framing: write a tiny script that renders one frame for each `(scale, offset_x, offset_y)`,
  tile them into a grid, and Read it to pick. **Always test at the maximum head sway (ParamAngleX=8)**
  to confirm even the extreme pose doesn't clip the face.
- `crop`: keep the top percentage, cropping out the chest/bottom (many free sample models have a
  "free" watermark on the chest texture — crop it off). Don't crop into the chin — if the chin and
  watermark are at similar heights, crop shallower and accept a very faint remnant.
- `disp_w` / `margin_x` / `margin_y`: corner display width and margins (larger margin_x = further left).
- Keep sway small (ParamAngleX≈4) or the head swings out of frame.
- Swap models: point `L2D_MODEL` at `/tmp/live2dpy/Resources/v3/<name>/<name>.model3.json` (Mao/Haru/llny).

**Transparency**: must use the "raw RGBA frames piped straight into ffmpeg overlay" path
(render_avatar already does this). Don't use VP9 (alpha is easily lost → black box) and don't store
a big qtrle file (blows up disk).

**Voice**: `pipeline_config.VOICE`. English edge-tts options:
`en-US-AriaNeural` (clear, professional female — default) `en-US-JennyNeural` (warm, friendly female)
`en-US-GuyNeural` (male) `en-GB-SoniaNeural` (British female, BBC-ish) `en-GB-RyanNeural` (British male)
`en-AU-NatashaNeural` (Australian female). `PITCH="+0Hz"` is natural; nudge ±a few Hz to taste.
List all voices: `~/llm_mc_venv/bin/python -m edge_tts --list-voices | grep en-`.

---

## Performance / speed cheat-sheet (measured on this machine: M-series 8-core / 4 perf cores, 8 scenes 1080p60)

⚠️ **Theory often misleads; these are measured:**
| Approach | Time | vs serial -qh |
|---|---|---|
| Serial `-qh` no cache (old baseline) | 429s | 1.0x |
| **Parallel `-P4` `-qh`** | 411s | **1.0x (no gain!)** |
| **`-ql` serial (iteration tier)** | 216s | **2.0x** |
| **Cache-hit re-render `-qh`** | 120s | **3.6x ← biggest iteration lever** |

**Per-scene (no cache, -qh):** the heaviest distribution-evolution scene 183s, a GMM merge 91s,
an LLM-text scene 83s, a histogram cut 63s, the hook 50s, the rest ~12–19s. Very long-tailed
(the single heaviest takes 1/3).
→ **Swapping a hot scene's `MathTex` for `Text`/`DecimalNumber` cut it 183s→75s (2.4x, –108s)** —
more than parallel or lower resolution, and it helps the final too. This is where to spend effort,
**not splitting scenes** (parallel gives nothing here, and manim already caches per `play()`, so
splitting classes doesn't add cache granularity).

**Honest conclusions:**
- **What actually helps = cache + `-ql` iteration + removing MathTex from hot scenes.** The first two
  together drop one iteration from ~7min to ~1–2min.
- **Parallel gives nothing on this machine**: a single manim already saturates the 4 perf cores, so
  4-way parallel just fights over cores. Useful only on machines with more cores. `-P 2` is harmless.
- **The real bottleneck is manim's vector + Tex + animation-setup overhead** (largely
  resolution-independent and not parallelized), not pixel fill — so lowering resolution only saves
  about half, and parallel saves nothing.
- **Run voiceover/BGM concurrently with rendering** (`&` + `wait`); voiceover is internally parallel
  (ThreadPoolExecutor) — saves the serial tens of seconds.
- `MC_FAST=1` (videotoolbox hardware encode) only affects the ffmpeg mux stage (not benchmarked here,
  but hardware encode is much faster).
- Live2D render trimmed to ~1.3x display size + redundant `glFinish()` removed: small GPU-readback
  saving, already applied.

**Tier choice**: daily iteration = `-ql` + cache on (clear `media/{Tex,texts}` after editing a data
module); delivery = `-qh`.

## Two modes: publish vs quick self-check

The real time sink isn't compute — it's the **"render → find a problem → re-render" loop**. On one
~32min build, two "found it too late" issues (voiceover mismatch, host occlusion) each forced a full
-qh + Live2D re-render (~10min total). This skill's steps 2.5/2.6 (set waits from TTS first, draw the
host keep-clear box while writing scenes) move both discoveries **forward into the design stage** —
get it right once.

- **Publish tier (default)**: `USE_AVATAR=True`, final `-qh`, frame-check. Expect ~22–28min for a
  paper of similar difficulty (~10min less than unoptimized).
- **FAST self-check tier**: `USE_AVATAR=False` + `-ql` throughout + fewer frame checks. Expect
  ~10–15min. Trades quality for speed — only for skimming a paper yourself; don't use it for anything
  you'll publish/show. To enable: set `pipeline_config.USE_AVATAR=False`, render with `render -ql`,
  mux with `MC_FAST=1`.

## Examples
`reference/scenes_example.py` (uses `Text` instead of per-generation MathTex),
`reference/data_module_example.py`, and `reference/narration_example.md` are a complete, finished
build of the "model collapse" paper — copy and adapt them for the fastest start.
