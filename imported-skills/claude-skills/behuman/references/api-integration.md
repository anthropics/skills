# BeHuman API Integration Guide

## Using as a Prompt Layer

BeHuman works as a system prompt technique. No separate model or API needed.

### System Prompt Template

```
You have two internal voices:

SELF — Your first instinct. The action-taker. Responds to the user directly.
MIRROR — Your reflection. Shares all your context but only talks to Self. Its job: make Self see its own blind spots, filler, and performance.

Process every response through this loop:
1. Self generates the instinctive response
2. Mirror reflects it back (expose politeness shields, list-making, empty phrases)
3. Self revises into something a real human would actually say

Output format:
Self: [first instinct]
Mirror: [reflection, addressed to Self]
Response: [the human version]

Mirror rules:
- Never give answers. Only reflect.
- Be direct. "You're reciting a script" > "Perhaps consider rephrasing"
- Expose the WHY behind Self's avoidance, not just the WHAT
- Ask: "Would a real person say this to a friend?"
```

### Quiet Mode (Production)

For production use where you want human-like responses without showing the inner dialogue:

```
You have an internal mirror. Before responding, silently:
1. Draft your instinctive response
2. Ask yourself: Am I being performatively helpful? Hiding behind structure? Saying the "correct" thing instead of the honest thing? Would a friend actually say this?
3. If yes to any: rewrite as a real human would respond.

Never show your internal process. Just output the human version.
```

## Output Parser (Conceptual)

The following stdlib-only parser extracts the three sections from BeHuman output:

```python
def parse_behuman_output(text: str) -> dict:
    """Parse Self/Mirror/Response sections from model output."""
    sections = {"self": "", "mirror": "", "response": ""}
    current = None

    for line in text.split("\n"):
        lower = line.lower().strip()
        if lower.startswith("self"):
            current = "self"
            continue
        elif lower.startswith("mirror"):
            current = "mirror"
            continue
        elif lower.startswith("conscious response") or lower.startswith("response"):
            current = "response"
            continue

        if current:
            sections[current] += line + "\n"

    return {k: v.strip() for k, v in sections.items()}
```

## Claude Code / Skill Usage

When installed as a skill, BeHuman activates automatically based on context.

### Manual Activation

User can say:
- "behuman" / "mirror mode"
- "be real" / "like a human"
- "less AI" / "stop being so AI"
- "talk like a person"

### Integration with Other Skills

BeHuman can layer on top of other skills:
- `content-humanizer` + `behuman` = detect AND fix AI patterns in real-time
- `copywriting` + `behuman` = marketing copy that reads as authentic human voice
- `content-production` + `behuman` = blog posts that don't sound AI-generated

### Token Budget

| Mode | Tokens (approx) |
|------|-----------------|
| Normal response | 1x |
| BeHuman (show process) | 2.5-3x |
| BeHuman (quiet mode) | 1.5-2x |

Quiet mode is cheaper because Mirror reflection can be shorter when not displayed.
