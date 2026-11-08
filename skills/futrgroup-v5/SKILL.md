---
name: futrgroup-v5
description: "A 7-stage AI video-ad pipeline replicating Franky Shaw's v5 / v5.1 60-sec ad formula (decoded from the FutrGroup Whop course, May 2026). Stages: 1) research → 2) concept (LLM writes 18-prompt framework + voice script) → 3) hero frames (NanoBanana 9:16 2K) → 4) animate (LINKED frame chain — same PNG ends V_n and starts V_n+1, why quality holds across 60s) → 5) voice (ElevenLabs / Suno) → 6) music → 7) edit (CapCut Realism Filter + Topaz super-sample to 4K 60fps). Provider-routed: fal+gemini default ($1.85/ad), muapi fallback, higgsfield-cli for proprietary Soul ID. Card-flip detector on every clip, ad_id minted before stage 3. Outputs a complete 60s 9:16 4K-60fps ad with audit trail."
---

# futrgroup-v5

> Reverse-engineered 7-stage AI ad pipeline. The non-obvious bit: **the image chain is *linked*, not random** — the same hero PNG that ends V_n is the start frame of V_n+1. This is why Kling/Seedance hold quality across 60 seconds.

## Source

Decoded May 2026 from a paid Whop course `v5 by Franky Shaw / FutrGroup AI Course` (2 videos, 45min + 40min). Method: cookie-scraped m3u8 → Whisper transcript + Gemini-2.5-pro creative-mode watch-video + multimodal frame analysis at 1 frame / 15s.

The Realism Filter values, Kling 3-slot prompt law, and persona-build chain v5.1 are from the same source.

## The 7 stages

| # | Script | What it does | Cost |
|---|---|---|---|
| 1 | `1-research.sh` | Reads product URL + brand DNA, optionally enriches via NotebookLM RAG | ~$0 (local) |
| 2 | `2-concept.sh` | LLM (OpenAI) drafts: concept, 18 image prompts, voice script, music brief | ~$0.02 |
| 3 | `3-frames.sh` | Generates 18 hero frames in parallel (default: NanoBanana Pro via Gemini, 9:16) | ~$0.40 |
| 4 | `4-animate.sh` | LINKED chain: P_n → P_n+1 = V_n. Default: Kling 3.0 via FAL. Card-flip detector on every clip. | ~$1.20 |
| 5 | `5-voice.sh` | ElevenLabs VO from voice script (via your TTS sibling) | ~$0.10 |
| 6 | `6-music.sh` | Suno music brief expansion → track | ~$0.05 |
| 7 | `7-edit.sh` | Remotion props.json + Realism Filter color adjustments + optional Topaz super-sample to 4K 60fps | ~$0.05 |

**Default route ≈ $1.85/ad** (fal+gemini). `--provider muapi` ≈ $3.50/ad. `--provider higgsfield-cli` (Soul ID) ≈ $8-19/ad.

## Hard rules (enforced by stage scripts)

1. **ad_id minted before stage 3.** Set `FUTRGROUP_AD_ID_MINT_SH` to integrate your lineage-tracking system; otherwise a `local-<unix>-<brand>` ID is written to `workdir/ad-id.json` as a dev placeholder.
2. **Linked P_n → P_n+1 chain in stage 4.** Each V_n.mp4 is generated with `start_frame=P_n.png` and `end_frame=P_n+1.png`.
3. **Card-flip detector on every clip.** Configure `FUTRGROUP_CARDFLIP_SH` and clips matching the card-flip transition pattern get quarantined.
4. **God-audit gate before publish.** `7-edit.sh` does NOT publish — it emits the final MP4 + a manifest. Wire `FUTRGROUP_GODAUDIT_SH` for a pre-publish gate.

## Standalone-ness

This skill ships with:
- The 7 stage scripts (`1-research.sh` … `7-edit.sh`) + `run.sh` orchestrator
- 3 helpers (`_args.sh`, `_siblings.sh`, `_assemble.sh`)
- 2 direct API clients (`_fal-kling.sh` for FAL Kling v3, `_veo-batch.sh` for Gemini Veo 3.1 fallback)

It depends on **bash + python3 + curl + jq + ffmpeg** for the baseline route. With just `FAL_API_KEY` + `GEMINI_API_KEY` + `OPENAI_API_KEY` exported, stages 1-4-7 run end-to-end via the built-in clients (stages 5 + 6 need an external voice/music sibling).

## CapCut Realism Filter (exact canonical values)

These values are baked into `7-edit.sh` as the default adjustment layer:

| Slider | Value | Note |
|---|---|---|
| Temp | -3 | slightly cooler |
| Tint | +2 | slightly green |
| Sat | -6 | desaturate |
| Exposure | -3 | darker |
| Contrast | +12 | more punch |
| Highlight | -35 | crush highlights |
| Shadow | +18 | lift shadows |
| Fade | +6 | matte film look |

These are the exact values from the source course.

## Kling 3-slot prompt law (for stage 4)

Every Kling clip prompt should follow this 3-slot pattern:

```
{motion qualifier} + {tone} + "{verbatim spoken line}"
```

- 3-8 second clips
- "Less is more" — short prompts win over long
- "Verbatim spoken line" means the exact dialogue snippet that voice-syncs to this clip

Example: `slow camera push-in, contemplative tone, "and that's when we knew it would change everything"`

## CLI

```bash
# Run all 7 stages end-to-end
bash scripts/run.sh \
  --brand my-brand \
  --product-url "https://my-shop.com/products/X" \
  --style "claymation Apple-influenced" \
  --duration 60 \
  --aspect 9:16 \
  --provider fal+gemini \
  --out ./out/launch-X/

# Run a single stage
bash scripts/3-frames.sh --workdir ./out/launch-X --brand my-brand --provider fal+gemini
bash scripts/4-animate.sh --workdir ./out/launch-X --brand my-brand --provider fal+gemini
```

## Self-test (graceful degradation demo)

```bash
bash scripts/run.sh --selftest
# Output:
#   ok 1-research.sh
#   ok 2-concept.sh
#   ... (all 7 parse)
#   missing FUTRGROUP_NOTEBOOKLM_SH (orchestrator will use stub for this stage)
#   missing FUTRGROUP_MSCLONE_SH (orchestrator will use stub for this stage)
#   ... (per-sibling status)
#   VERDICT: PASS
```

Every sibling skill is **optional**. If a sibling is unset, the stage prints `[FUTRGROUP] WARNING: <sibling> not configured (FUTRGROUP_<NAME>) — <stub action>` and continues with stub behavior. The full pipeline runs E2E even with zero siblings configured — output is a stubbed manifest that documents what would have been generated.

## Provider env vars

```bash
# Default route (cheapest, ~$1.85/ad)
export FAL_API_KEY=$YOUR_FAL_KEY
export GEMINI_API_KEY=$YOUR_GEMINI_KEY
export OPENAI_API_KEY=$YOUR_OPENAI_KEY    # for stage 2's 18-prompt framework
export FUTRGROUP_PROVIDER=fal+gemini

# muapi fallback route (~$3.50/ad)
export MUAPI_API_KEY=$YOUR_MUAPI_KEY
export FUTRGROUP_PROVIDER=muapi

# higgsfield-cli for proprietary Soul ID (~$8-19/ad)
export HIGGSFIELD_TOKEN=$YOUR_HIGGSFIELD_TOKEN
export FUTRGROUP_PROVIDER=higgsfield-cli
```

## Sibling skill paths (all optional)

Set `FUTRGROUP_SIBLINGS_HOME` to a directory and each sibling auto-resolves as `$FUTRGROUP_SIBLINGS_HOME/<skill-name>/scripts/<entry>.sh`, OR set each var directly to an absolute path:

| Sibling | Required for full functionality | Env var |
|---|---|---|
| `notebooklm-research` | Stage 1 RAG enrichment (optional) | `FUTRGROUP_NOTEBOOKLM_SH` |
| `marketing-studio-clone` | Stage 2 prefix composition (optional) | `FUTRGROUP_MSCLONE_SH` |
| `mcsla-prompt-builder` | Stage 4 motion-prompt builder (optional) | `FUTRGROUP_MCSLA_SH` |
| `muapi` (img.sh / i2v.sh / create-music.sh) | `--provider muapi` route | `FUTRGROUP_MUAPI_IMG_SH` / `FUTRGROUP_MUAPI_I2V_SH` / `FUTRGROUP_MUAPI_MUSIC_SH` |
| `video-gen` (FAL Kling wrapper) | Stage 4 default (or use built-in `_fal-kling.sh`) | `FUTRGROUP_VIDEO_GEN_SH` |
| `ai-voiceover` | Stage 5 (else `vo.txt` stub) | `FUTRGROUP_VOICEOVER_SH` |
| `higgsfield-cli` | `--provider higgsfield-cli` + `--use-virality` | `FUTRGROUP_HIGGSFIELD_GEN_SH` / `FUTRGROUP_HIGGSFIELD_I2V_SH` / `FUTRGROUP_HIGGSFIELD_VIRALITY_SH` |
| `unified-intel/ad-id-mint.sh` | Lineage tracking (optional) | `FUTRGROUP_AD_ID_MINT_SH` |
| `video-card-flip-detector` | Stage 4 QA (optional) | `FUTRGROUP_CARDFLIP_SH` |
| `god-mode-audit` | Pre-publish gate (optional) | `FUTRGROUP_GODAUDIT_SH` |
| `remotion-renderer` | Stage 7 polished render (else FFmpeg fallback) | `FUTRGROUP_REMOTION_SH` |
| `hyperframes-render` | Stage 7 caption overlay (optional) | `FUTRGROUP_HYPERFRAMES_SH` |
| Topaz CLI (`tvai` / `tvai-cli`) | Stage 7 4K-60 super-sample (else FFmpeg fallback) | `FUTRGROUP_TOPAZ_BIN` |

## Brand DNA contract

`--brand <slug>` resolves to `${FUTRGROUP_BRAND_HOME:-$HOME/.futrgroup/brands}/<slug>/`, which should contain:

- `BRAND-DNA.md` — narrative voice + visual rules + audience
- `references/character/*.{png,jpg}` — hero character reference
- `references/product/*.{png,jpg}` — product hero
- (optional) `assets/logo/*.png` — for stage-7 watermark

## License

MIT — see LICENSE.txt.

## Example brief

See `examples/brief-pour-over-launch.md`.

## Versioning

- `0.1.0` (2026-05-09) — 7-stage orchestrator + canonical Realism Filter values + Kling 3-slot law.
- `0.2.0` (planned) — parallel-clip generation in stage 4, more provider routes.
- `0.3.0` (2026-05-12) — standalone refactor: full env-var sibling resolution via `_siblings.sh`, graceful degradation in every stage, no hardcoded brand or skill paths.
