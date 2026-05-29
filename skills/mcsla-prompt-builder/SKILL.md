---
name: mcsla-prompt-builder
description: "Compose MCSLA-structured video prompts (Model · Camera · Subject · Look · Action) that work on raw FAL Kling 3.0 / Seedance 2.0 / Veo 3.1 / Nano Banana — not just on Higgsfield. 50+ named camera moves, 13 shot sizes, 9 micro-expressions, 10 color grades, 5 film stocks, 18 lighting types, 5 styles — all platform-recognized vocab. Composes ≤200-word prompts in canonical Subject→Action→Camera→Style order, validates them, and lists every vocab class for agent discovery."
---

# mcsla-prompt-builder

> Drop-in MCSLA video-prompt composer. Works on **any** generative-video model — not just Higgsfield. Vocab catalog reverse-engineered from a community Higgsfield skill (OSide v3.7.0).

## What MCSLA is

Every Higgsfield video prompt follows this 5-layer structure. The same vocab works on raw Kling 3.0 / Seedance 2.0 / Veo 3.1 / Nano Banana because they're trained on the same cinematography corpus.

| Slot | What | Example |
|---|---|---|
| **M**odel | which engine | `kling-3.0` / `seedance-2.0` / `veo-3.1` / `wan-2.7` |
| **C**amera | named move | `Robo Arm arcing slowly from base to lid` / `Bullet Time` / `Snorricam` / `FPV Drone` |
| **S**ubject | body + micro-expression | `weight forward, jaw tight, simmering rage, eyes locked on camera` |
| **L**ook | platform style + grade + stock + light | `Cinematic + Blockbuster grade + Kodak Portra 400 + golden-hour rim light` |
| **A**ction | Subject → Action → Camera → Style ordering | `She raises the cup, steam rises, camera dollies in, warm Kodak Portra` |

**Hard rules** (enforced by the CLI):
- ≤200 words (models distort beyond)
- Named tokens only — no generic substitutes
- Img-to-video: prompt = motion ONLY (don't redescribe the static frame)
- No negatives — phrase positively (`tack sharp`, not `no blur`)
- `Subject → Action → Camera → Style` order is empirically most reliable across all three engines

## CLI

```bash
# Run from the skill directory (this folder)
SK="./scripts/mcsla-build.sh"

# Compose from slots
"$SK" \
  --model kling-3.0 \
  --camera "Robo Arm" \
  --camera-detail "arcing slowly from base to lid" \
  --subject "matte black travel mug" \
  --subject-detail "minimal design, no branding" \
  --look "cinematic commercial, warm neutrals, soft diffused natural light" \
  --action "hot coffee pours in, steam rises in macro close-up" \
  --aspect 9:16 \
  --duration 5

# Validate an existing prompt
"$SK" --validate "your prompt text..."

# List vocab
"$SK" --list cameras
"$SK" --list shot-sizes
"$SK" --list micro-expressions
"$SK" --list color-grades
"$SK" --list film-stocks
"$SK" --list lighting

# JSON output (agent-friendly)
"$SK" --model kling-3.0 --camera "Bullet Time" --subject "..." --action "..." --format json
```

## Vocab data files (all platform-recognized)

All vocab JSONs ship in `data/`. Each entry is a string token the underlying video model is trained to recognize.

| File | Count | Source |
|---|---|---|
| [`data/cameras.json`](data/cameras.json) | 50+ | Dolly, Crane, Orbit, Zoom, Follow, Cinematic, Time-based, Cut Vocab |
| [`data/shot-sizes.json`](data/shot-sizes.json) | 13 | ELS, EWS, WS, MLS, MWS, MS, MCU, CU, ECU, Insert, OTS, POV, Two-Shot |
| [`data/micro-expressions.json`](data/micro-expressions.json) | 9 | Deadpan Neutral, Quiet Devastation, Cold Calculation, Bitter Amusement, etc. |
| [`data/color-grades.json`](data/color-grades.json) | 10 | Blockbuster, Cold thriller, Cyberpunk, Horror, Romance, Noir, etc. |
| [`data/film-stocks.json`](data/film-stocks.json) | 5 | Kodak Portra 400, Fuji Velvia, Kodak Vision3 500T, Ilford HP5, Kodak Ektachrome |
| [`data/lighting.json`](data/lighting.json) | 18 | Golden hour, Volumetric, Rembrandt, Butterfly, Chiaroscuro, etc. |
| [`data/styles.json`](data/styles.json) | 5 | Cinematic, VHS, Super 8MM, Anamorphic, Abstract |

## Composition order rule (the single non-obvious bit)

Output sentence order: `Subject → Action → Camera → Style`. Empirically validated across Kling 3.0, Seedance 2.0, Veo 3.1. Reverse order = blurry/distorted output even with same tokens.

## Optional integrations (env-var-gated)

The script has two optional integration points. Both are off by default; set the env var to a sibling-skill path to enable.

| Flag | Env var | What it does |
|---|---|---|
| `--register-pattern` | `MCSLA_PROMPT_BANK_SH=/path/to/prompt-bank.sh` | After compose, register the prompt into a sibling `prompt-bank` skill. No-op if env var unset. |
| `--apply-preset <name>` | `MCSLA_PRESET_LIB_SH=/path/to/preset-apply.sh` | Pull style+motion strings from a sibling preset catalog. No-op if env var unset. |

If you don't have those sibling skills installed, the core compose / validate / list paths still work — they're independent.

## Example output

```
$ bash scripts/mcsla-build.sh --model kling-3.0 --camera "Robo Arm" \
    --camera-detail "arcing slowly from base to lid" \
    --subject "matte black travel mug" \
    --action "hot coffee pours in, steam rises in macro close-up" \
    --look "warm neutrals, soft diffused light, Kodak Portra 400"

matte black travel mug — hot coffee pours in, steam rises in macro close-up.
Camera: Robo Arm arcing slowly from base to lid.
Style: warm neutrals, soft diffused light, Kodak Portra 400.
[27 words · MCSLA-valid · model=kling-3.0 · aspect=9:16]
```

## Testing

```bash
bash scripts/mcsla-build.sh --selftest    # dry-run all vocab loads + 3 known-good prompts
bash -n scripts/mcsla-build.sh             # syntax check
```

## License

MIT — see LICENSE.txt.

## Versioning

- `0.1.0` (2026-05-09) — initial MVP with 7 vocab JSONs + compose / validate / list CLI.
- `0.2.0` (planned) — VLM post-gen scoring loop, auto-mutate when score < 7.

## Example brief

See `examples/brief-coffee-pour.md` for a sample brief + the prompt this skill produces from it.
