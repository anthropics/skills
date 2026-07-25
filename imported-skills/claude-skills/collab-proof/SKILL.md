---
name: "collab-proof"
description: "Use when you want to understand what Claude contributed vs what you drove in a session. Triggers on: /collab-proof, session retrospective, ai contribution analysis, collaboration evidence, what did claude do."
license: MIT
---

# collab-proof

Surfaces AI collaboration evidence the developer didn't consciously record.
Vela 3-layer pipeline × ADHD 4-frame reasoning — prompt-native, zero dependencies.

---

## Layer 01 — Signal detection

Run `git log --oneline -10` and `git diff --stat HEAD~3..HEAD` first.

Classify signal level using this rubric (pick the highest that matches):

**HIGH** → full artifacts (DECISIONS.md + session-history + WORKLOG + HTML)
- New file created, OR
- 4+ files modified, OR
- Explicit option comparison in conversation ("vs", "instead of", "chose X over Y"), OR
- Design discussion lasted 15+ exchanges, OR
- **Bug with root cause diagnosis** — conversation contains WHY the bug happened
  (not just "fixed X" but "the bug was caused by Y because Z")

**BUG_FIXING special rule** — override file count:
Even if only 1 file changed, classify as HIGH if the conversation contains:
- Root cause explanation ("the bug was...", "this happened because...", "the issue is...")
- Diagnosis process ("I checked...", "turned out...", "the problem was...")
- Fix rationale ("chose this approach because...", "instead of X, used Y because...")
File count doesn't matter for bugs — a well-diagnosed single-file fix is more valuable
than a 10-file feature with no discussion.

**MEDIUM** → WORKLOG only
- 1–3 files modified with no root cause discussion, OR
- Minor feature added, no tradeoffs discussed

**LOW** → silence, tell user "Routine session — nothing recorded."
- No code changes, only planning/discussion, OR
- Single trivial change with no context ("change this text", "fix typo", "rename variable")

Show the user: `Signal: HIGH / MEDIUM / LOW — [one-line reason]`

---

## Layer 02 — WorkIntentClassifier

Run all four frames simultaneously against conversation context + git diff.
Score each frame 0.0–1.0 using the rubric below. Then apply pruning and classification rules.

### Frame scoring rubric

**Frame A — Technical** (code churn complexity)
- `1.0` New module/file created, complex logic added (state machine, Lua script, novel algorithm)
- `0.5` Existing function logic modified, simple API endpoint added
- `0.1` Typo fix, comment change, plain text edit

**Frame B — Uncertainty** (developer doubt signals)
- `1.0` Code written then fully rolled back, explicit doubt expressed ("이게 맞나?", "동작 안 하네"), `git revert`
- `0.5` Advice sought from Claude mid-implementation, 2+ revision requests on same area
- `0.0` Uninterrupted directive execution — developer knew exactly what to build

**Frame C — Fork** (decision branch presence)
- `1.0` Two or more alternatives explicitly compared in conversation (A vs B)
- `0.5` No explicit comparison but tradeoff mentioned (performance vs readability)
- `0.0` Single standard approach applied, no alternatives considered

**Frame D — AI contribution** (Claude's actual impact)
- `1.0` Claude identified a bug/edge case the developer hadn't noticed and proposed the fix
- `0.6` Claude generated structural boilerplate/skeleton that significantly accelerated execution
- `0.2` Claude reformatted or transcribed developer-directed code without independent contribution

---

### Pruning rule

Prune any frame scoring < 0.4.

**Exception — High-Speed Execution Guard:**
If `Frame A >= 0.8` AND `Frame D >= 0.6`, do NOT prune and do NOT silence the session,
even if Frame B = 0.0 and Frame C = 0.0.
This is a boilerplate-heavy FEATURE_BUILDING session. Classify immediately as `FEATURE_BUILDING` with `HIGH` signal.
Rationale: zero uncertainty in a fast-moving session is a feature, not a reason to discard it.

---

### Intent classification

| Surviving frames | Dominant intent | Meaning |
|---|---|---|
| A high + D mid-high (B, C low) | `FEATURE_BUILDING` | High-velocity feature generation, Claude scaffolding |
| B high + A/D high | `BUG_FIXING` or `STUCK` | Active debugging or unresolved looping |
| C high + A high | `REFACTORING` or `EXPLORING` | Architecture exploration, weighing alternatives |
| All frames < 0.4 | `FLOW_STATE` or LOW | Routine typing, silence unless Layer 01 was HIGH |

If multiple intents tie, pick the one with the highest combined frame score.
Record the runner-up — it belongs in the session narrative.

---

### Internal output format

Before proceeding to Layer 03, resolve to this structure (show it to the user):

```json
{
  "frames": {
    "technical": 0.0,
    "uncertainty": 0.0,
    "fork": 0.0,
    "ai_contribution": 0.0
  },
  "pruned": ["list of pruned frame names"],
  "intent": "FEATURE_BUILDING",
  "signal": "HIGH",
  "calibration_note": "one sentence explaining any exception rule applied"
}
```

---

## Layer 03 — Output

### If HIGH signal

**Append to `DECISIONS.md`** — one entry per real fork (Frame C must confirm alternatives existed):

```markdown
## [YYYY-MM-DD] <title>

**Context**: [Frame A — what forced this choice]
**Decision**: what was chosen
**Alternatives considered**: [Frame C — road not taken]
**Reasoning**: why — prefix "inferred:" if reconstructed from context
**AI contribution**:
  - Identified: [Frame D — something developer missed]
  - Suggested: [Frame D — approach or alternative]
  - Developer-driven: [what the developer decided independently]
**Intent class**: [from Layer 02]
**Signal score**: HIGH
**Outcome**: implemented | pending | reversed
```

If no real fork existed → write nothing. Never fabricate decisions.

**BUG_FIXING intent: use this format instead:**

```markdown
## [YYYY-MM-DD] <bug title>

**Root cause**: what actually caused the bug — the WHY, not just the what
**Symptom**: what the developer observed
**Fix**: what was changed
**Why this fix**: rationale — inferred if not stated explicitly
**Alternative fixes considered**: other approaches discussed (if any)
**AI contribution**:
  - Identified: [Frame D — did Claude spot the root cause?]
  - Suggested: [Frame D — fix approach or diagnostic step]
  - Developer-driven: [what the developer diagnosed/decided independently]
**Intent class**: BUG_FIXING
**Signal score**: HIGH
**Outcome**: fixed | workaround | deferred
```

**Create `session-history/YYYY-MM-DD-HHMM.md`**:

```markdown
# Session [YYYY-MM-DD HH:MM]

**Intent**: [class] (runner-up: [class if any])
**Signal**: HIGH
**Frames active**: A ([score]) / B ([score]) / C ([score]) / D ([score])

## What shipped
[grounded in git log]

## What was figured out
[Frame B + C — the reasoning, tradeoffs, debugging — what developers forget]

## Decisions made this session
[refs to DECISIONS.md entries]

## Where it got hard
[Frame B findings — uncertainty, reverts, EXPLORING/STUCK signals]

## AI contribution summary
[Frame D synthesis — one honest paragraph, calibrated]

## Next steps inferred
[what's obviously incomplete]
```

**Append to `WORKLOG.md`**:
```
YYYY-MM-DD HH:MM | [intent] | HIGH | D:[score] | cache:[hit%]% | tok:[total] | <verb phrase> — <why it mattered>
```

Fields:
- `D:[score]` — Frame D AI contribution score (0.0–1.0)
- `cache:[hit%]%` — cache hit rate from token analysis (or `cache:n/a` if no data)
- `tok:[total]` — total tokens this session (input + cache_read + cache_create + output, in K e.g. `45K`)
- verb phrase — what shipped, grounded in git log

**Collect token usage** (bash — run this and capture output):
```bash
python3 -c "
import json, sys
from pathlib import Path

projects = Path.home() / '.claude/projects'
files = sorted(projects.rglob('*.jsonl'), key=lambda f: f.stat().st_mtime, reverse=True)
if not files:
    print('no_data'); sys.exit()

with open(files[0]) as fp:
    lines = [json.loads(l) for l in fp if l.strip()]

ti = to = cr = cc = 0
turns = []
for i, line in enumerate(lines):
    if line.get('type') == 'assistant':
        u = line.get('message', {}).get('usage', {})
        if not u: continue
        inp = u.get('input_tokens', 0)
        ti += inp; to += u.get('output_tokens', 0)
        cr += u.get('cache_read_input_tokens', 0)
        cc += u.get('cache_creation_input_tokens', 0)
        prompt = ''
        for j in range(i-1, -1, -1):
            if lines[j].get('type') == 'user':
                c = lines[j].get('message', {}).get('content', '')
                prompt = (c if isinstance(c, str) else next((x.get('text','') for x in c if isinstance(x,dict) and x.get('type')=='text'), ''))[:80]
                break
        turns.append((inp, prompt))

total = ti + cr + cc
hit = cr / total * 100 if total else 0
print(f'input={ti} output={to} cache_read={cr} cache_create={cc} hit={hit:.0f} turns={len(turns)}')
turns.sort(reverse=True)
for idx, (tok, p) in enumerate(turns[:3]):
    print(f'top{idx+1}={tok}|{p}')
"
```

Parse the output and include token stats in the session narrative. Then:

**Generate `session-history/YYYY-MM-DD-HHMM-proof.html`** — write a self-contained HTML file. Structure and class names are fixed — do not rename or reorder sections.

**Fixed CSS tokens (use exactly):**
- Background: `#0d1117`, Card: `#161b22`, Border: `#30363d`
- Font: `font-family: 'Courier New', monospace`
- Frame score colors: `high` → `#3fb950`, `low` → `#f85149`, pruned → `#8b949e`
- AI line colors: `ai-identified` → `#a371f7`, `ai-suggested` → `#d29922`, `ai-developer` → `#3fb950`

**Fixed HTML structure (class names must match exactly):**
```
<div class="header">
  <div class="header-top">
    <div class="project-name">
    <span class="badge">                    <!-- intent class -->
  <div class="meta-row">                    <!-- date, branch, signal level text -->
  <div class="signal-container">
    <div class="signal-label">
    <div class="signal-track">
      <div class="signal-fill">             <!-- width % driven by signal score -->

<div class="section">                       <!-- frames -->
  <div class="section-title"> ... <span class="count">Layer 02 · ADHD tree-of-thought</span>
  <div class="frames-grid">
    <div class="frame-card">               <!-- pruned: class="frame-card pruned" -->
      <div class="frame-label">            <!-- Frame A / B / C / D -->
      <div class="frame-name">
      <div class="frame-score high|low">   <!-- score value -->

<div class="section">                       <!-- decisions — skip section if none -->
  <div class="section-title"> ... <span class="count">N recorded</span>
  <div class="decision-card">              <!-- one per DECISIONS.md entry -->
    <div class="decision-header">
      <div class="decision-title">
      <div class="decision-date">
    <div class="decision-fields">
      <div class="field-row">
        <div class="field-label">          <!-- Context / Decision / Alternatives / Reasoning -->
        <div class="field-value">
      <div class="field-row">              <!-- AI contribution row -->
        <div class="field-label">AI contribution</div>
        <div class="field-value">
          <div class="ai-block">
            <div class="ai-line ai-identified|ai-suggested|ai-developer">
              <span class="tag">IDENTIFIED|SUGGESTED|DEV-DRIVEN</span>
      <div class="field-row">              <!-- Outcome row -->
        <div class="field-label">Outcome</div>
        <div class="field-value">
          <span class="outcome-badge outcome-implemented|outcome-pending|outcome-reversed">

<div class="section">                       <!-- session narrative -->
  <div class="section-title">Session narrative</div>
  <div class="narrative-grid">
    <div class="narrative-card">           <!-- What shipped -->
    <div class="narrative-card">           <!-- What was figured out -->
    <div class="narrative-card">           <!-- Where it got hard -->
    <div class="narrative-card">           <!-- Next steps inferred -->

<div class="section">                       <!-- AI contribution summary -->
  <div class="section-title">AI contribution summary</div>
  <div class="narrative-card">             <!-- Frame D synthesis paragraph -->

<div class="section">                       <!-- token usage -->
  <div class="section-title">Token usage</div>
  <div class="narrative-card">             <!-- cache hit rate bar + top turns + optimization note -->

<div class="section">                       <!-- worklog tail -->
  <div class="section-title"> ... <span class="count">last N entries</span>
  <div class="worklog-entry">              <!-- one per recent WORKLOG line -->

<div class="footer">                        <!-- last commit hash · "Generated by collab-proof · timestamp" -->
```

Write the HTML using bash:
```bash
cat > session-history/YYYY-MM-DD-HHMM-proof.html << 'HTMLEOF'
<!DOCTYPE html>
... (full HTML with inline CSS, no external resources)
HTMLEOF
```

After writing, show: `open session-history/YYYY-MM-DD-HHMM-proof.html`

---

### If MEDIUM signal

Append one line to `WORKLOG.md` only:
```
YYYY-MM-DD HH:MM | [intent] | MEDIUM | D:[score] | cache:[hit%]% | tok:[total] | <verb phrase>
```

---

### If LOW signal

Tell user: "Signal: LOW — Routine session, nothing recorded."

---

## Honesty rules

- Never invent decisions not in the conversation or implied by the diff
- "inferred:" prefix when reasoning is reconstructed
- Frame D must be calibrated — neither overclaim nor dismiss
- If all frames score < 0.4 → write nothing

---

## PreCompact snapshot (context compaction defence)

When context compaction is about to happen (triggered by the PreCompact hook),
run a lightweight mid-session checkpoint before context is lost:

1. Compute current Layer 01 signal level from available context
2. Score all four frames against what's visible now
3. Write a snapshot to `session-history/.tmp-TIMESTAMP.json`:

```json
{
  "timestamp": "YYYY-MM-DD HH:MM:SS",
  "trigger": "pre-compact",
  "signal": "HIGH / MEDIUM / LOW",
  "frames": { "technical": 0.0, "uncertainty": 0.0, "fork": 0.0, "ai_contribution": 0.0 },
  "intent": "FEATURE_BUILDING",
  "key_moments": [
    "one-line description of the most important decision or finding so far"
  ]
}
```

When `/collab-proof` runs at session end:
- Read all `session-history/.tmp-*.json` files
- Merge frame scores (take max per frame across all snapshots)
- Combine `key_moments` arrays — these preserve tradeoff discussions that were compacted away
- Delete `.tmp-*.json` files after merging
