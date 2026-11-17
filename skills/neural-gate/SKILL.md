---
name: neural-gate
description: Neural-layer behavioral constraint verification for Claude Code. After session end, checks whether key behavioral constraints actually appeared in output — complementing filesystem gates (which verify file state) with NL-channel verification (which detects whether rules shaped behavior). Early-stage; explicitly a weak proxy pending v2 semantic verification.
license: MIT
---

# Neural-Gate — Behavioral Constraint Echo Detection

A post-session check that verifies whether behavioral constraints actually appeared in agent output. While filesystem gates check file state (mtime, exit codes), neural-gate checks the NL channel: did the rules we wrote actually change what the agent did?

## When to Activate

- After sessions where behavioral constraints were expected to apply
- When you want evidence that rules shaped behavior, not just evidence that rules exist
- As the fourth layer in a pipeline: pre-task → adversarial review → delivery verification → neural echo check
- When diagnosing why a constraint exists on disk but never manifests in output

## How It Works

```
Session End (Stop hook):
  1. Read constraint keyphrases from config (BODY.md, INTERFACE.md)
  2. Scan session transcript for keyphrase occurrences
  3. Report: which constraints echoed, which didn't
  4. Never blocks — this is detection, not enforcement
```

Keyphrase echo is a weak proxy: "the constraint was mentioned" ≠ "the constraint changed behavior." This is an explicit limitation, not a bug. v2 roadmap: semantic similarity detection for behavioral fidelity.

## Install

```json
{
  "hooks": {
    "Stop": [{
      "hooks": [{
        "type": "command",
        "command": "python3 ~/.claude/scripts/neural-gate.py",
        "timeout": 5000
      }]
    }]
  }
}
```

## Example

```
Stop hook: neural-gate scans transcript for constraint keyphrases
→ "双池审查" echoed: 3 occurrences in output ✓
→ "三问" echoed: 1 occurrence ✓
→ "Read-after-Write" echoed: 0 occurrences ⚠️
→ "降级链" echoed: 0 occurrences ⚠️
→ Echo rate: 50% (2/4 constraints visible)
→ WARN but never blocks
```

## Design Limitations (Honest)

- **Keyphrase echo ≠ behavioral compliance.** Mentioning a rule is not following it.
- **False positives**: agent can echo a constraint while ignoring it
- **False negatives**: constraint may shape behavior without being explicitly named
- **Scope**: only checks NL output, not tool call behavior

These are structural limitations of NL-channel verification — the same Prose Barrier that makes filesystem gates necessary. v2 will add semantic similarity scoring.

## Integration

The fourth layer in a pipeline where each gate covers a different failure mode:

| Gate | Layer | Checks | Blocks? |
|------|-------|--------|:--:|
| pre-task-calibration | Pre-action | Approach validity | Yes |
| persona-review | During | Adversarial depth | Reviewer discretion |
| delivery-verification | Post-action | File state completeness | Yes |
| **neural-gate** | Post-session | Constraint echo | **No** |

Neural-gate is the only gate that explicitly does not block — it detects, reports, and lets the human decide.
