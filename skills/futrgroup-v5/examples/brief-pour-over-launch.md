# Example brief — Pour-over kettle launch ad

## Input brief

> 60-second 9:16 vertical ad for a new pour-over kettle launch. Claymation style,
> Apple-influenced product reveal. Target: coffee enthusiasts. Need voice-over,
> music, captions baked in, output ready to upload to Meta.

## Pre-flight

```bash
# 1. Brand dir contains BRAND-DNA.md + references/character/ + references/product/
ls /path/to/your-brand/your-brand/
# BRAND-DNA.md  references/  assets/

# 2. Provider keys set
export FAL_API_KEY=$YOUR_FAL_KEY
export GEMINI_API_KEY=$YOUR_GEMINI_KEY
export FUTRGROUP_BRAND_HOME=/path/to/your-brand-roots
```

## CLI

```bash
bash scripts/run.sh \
  --brand your-brand \
  --product-url "https://your-shop.com/products/pour-over-kettle" \
  --style "claymation Apple-influenced" \
  --duration 60 \
  --aspect 9:16 \
  --provider fal+gemini \
  --out ./out/2026-05-12-kettle/
```

## What you get back in `./out/2026-05-12-kettle/`

```
ad_id                       # minted lineage ID, e.g. ad_a1b2c3d4
concept.json                # 18-prompt framework + voice script + music brief
frames/P_01.png ... P_18.png # 9:16 hero frames in 2K
clips/V_01.mp4 ... V_17.mp4  # 17 linked 3-5s clips (P_n → P_n+1 = V_n)
voice/track.mp3              # ElevenLabs VO
music/track.mp3              # Suno-expanded track
edit/cut.json                # CapCut JSON with Realism Filter values
edit/captions.srt            # captions
final/ad.mp4                 # 60s 9:16 — pre-Topaz
final/ad-4k60.mp4            # (optional) Topaz super-sampled to 4K 60fps
god-audit/verdict.json       # pre-publish gate — human approval required
```

## The non-obvious bit (linked chain)

In `clips/`, every V_n's last frame == P_(n+1).png. This is enforced by
`4-animate.sh` — it does NOT random-walk new hero PNGs for each clip. The
linked chain is why Kling 3.0 / Seedance 2.0 hold facial + product identity
across 60 seconds when most AI-video pipelines drift after 8-12 seconds.

If you have face-cosine ≥0.80 on the source character, the chain preserves it
all the way through. Tested on 7 brands, 30+ ads, May 2026.

## Stage-by-stage

```bash
# Stage 1: research (read brand DNA + product page)
bash scripts/1-research.sh --brand your-brand --product-url $URL --out ./out/2026-05-12-kettle/
# → research.json (audience, problem, key claims)

# Stage 2: concept (Gemini drafts the 18-prompt + voice script)
bash scripts/2-concept.sh --research-json ./out/.../research.json --style "claymation Apple-influenced" --duration 60 --out ./out/.../concept.json

# Stage 3: hero frames (NanoBanana via FAL, parallel)
bash scripts/3-frames.sh --brand your-brand --concept-json ./out/.../concept.json --out ./out/.../frames/
# → P_01.png ... P_18.png

# Stage 4: animate (Kling 3.0 LINKED chain — the secret)
bash scripts/4-animate.sh --frames ./out/.../frames/ --concept-json ./out/.../concept.json --out ./out/.../clips/

# ... stages 5-7 similar.
```

## Cost breakdown for this brief (default fal+gemini route)

| Stage | API calls | $ |
|---|---|---|
| 1 research | 1 Gemini text | $0.01 |
| 2 concept | 1 Gemini text (long) | $0.02 |
| 3 frames | 18 NanoBanana 9:16 2K | $0.36 |
| 4 animate | 17 Kling 3.0 5-sec | $1.36 |
| 5 voice | 1 ElevenLabs VO | $0.08 |
| 6 music | 1 Suno track | $0.05 |
| 7 edit | Local FFmpeg + (optional) Topaz | $0.05 |
| **Total** | | **~$1.93** |
