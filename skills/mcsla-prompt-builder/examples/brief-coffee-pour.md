# Example brief — Coffee pour macro shot

## Input brief (human-language)

> Need a 5-second 9:16 commercial video of hot coffee pouring into a matte
> black travel mug. Want a macro shot with steam rising. Robo Arm camera move
> arcing from the base of the mug up to the lid as the pour completes. Warm
> Kodak Portra 400 grade, soft diffused natural light, cinematic commercial feel.

## CLI invocation

```bash
bash scripts/mcsla-build.sh \
  --model kling-3.0 \
  --camera "Robo Arm" \
  --camera-detail "arcing slowly from base to lid" \
  --subject "matte black travel mug" \
  --subject-detail "minimal design, no branding" \
  --action "hot coffee pours in, steam rises in macro close-up" \
  --look "cinematic commercial, warm Kodak Portra 400, soft diffused natural light" \
  --aspect 9:16 \
  --duration 5
```

## Output prompt

```
matte black travel mug, minimal design, no branding. hot coffee pours in, steam rises in macro close-up. Camera: Robo Arm arcing slowly from base to lid. cinematic commercial, warm Kodak Portra 400, soft diffused natural light. Aspect 9:16. Duration 5s.
```

## Why this works

- **Subject → Action → Camera → Style** order is preserved (the single non-obvious empirical rule).
- **Named camera move** (`Robo Arm`) — recognized by Kling 3.0, Seedance 2.0, Veo 3.1 because they're trained on the same cinematography corpus.
- **Named film stock** (`Kodak Portra 400`) — passes through the engine's grading layer; generic "warm tones" would get lost.
- **Word count: 39** — well under the 200-word distortion threshold.
- **No negatives** — every directive is phrased positively (`tack sharp` not `no blur`, `minimal design` not `no logos`).

## JSON output (for agent pipelines)

```bash
bash scripts/mcsla-build.sh \
  --model kling-3.0 \
  --camera "Robo Arm" \
  --camera-detail "arcing slowly from base to lid" \
  --subject "matte black travel mug" \
  --action "hot coffee pours in, steam rises in macro close-up" \
  --look "warm Kodak Portra 400, soft diffused light" \
  --format json
```

```json
{
  "model": "kling-3.0",
  "camera": "Robo Arm",
  "subject": "matte black travel mug",
  "look": "warm Kodak Portra 400, soft diffused light",
  "action": "hot coffee pours in, steam rises in macro close-up",
  "aspect": "9:16",
  "duration": "5",
  "prompt": "matte black travel mug. hot coffee pours in, steam rises in macro close-up. Camera: Robo Arm arcing slowly from base to lid. warm Kodak Portra 400, soft diffused light. Aspect 9:16. Duration 5s.",
  "word_count": 33
}
```
