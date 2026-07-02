---
name: rulehook
description: Use when Claude Code rules are being ignored, agent forgets preferences, or you need automated compliance checking. Triggers on: rules not followed, context overload causing forgotten preferences, CLAUDE.md instructions ignored, hook-based enforcement, agent governance, behavior guardrails, soft constraint enforcement.
license: MIT
---

# rulehook — enforce soft rules with hard hooks

## The problem

CLAUDE.md rules are soft constraints — Claude reads them but skips them under engineering momentum. Rules degrade over long sessions, vanish after context compaction, and have zero enforcement mechanism.

Community evidence: [anthropics/claude-code #29236](https://github.com/anthropics/claude-code/issues/29236) (paying subscriber considering legal action), [#17151](https://github.com/anthropics/claude-code/issues/17151) (CLAUDE.md ignored since v0.75), [#22309](https://github.com/anthropics/claude-code/issues/22309) ("may or may not be relevant" disclaimer).

## The fix

Three defence lines that bridge soft rules to hard hooks:

```
L1: SKILL.md prevention — insert mandatory check before code generation
L2: Stop hook two-stage grep — scan transcript → warn on violation  
L3: SessionStart compliance audit — read observations.jsonl → inject rate
```

All three operate independently, connected only via filesystem (transcript + jsonl). Zero LLM token cost. Zero external dependencies (Node.js stdlib only).

## Install

```bash
git clone https://github.com/wuykjl/rulehook.git
cd rulehook

cp hooks/stop-doc-template-check.js ~/.claude/scripts/hooks/
cp hooks/session-start-compliance-audit.js ~/.claude/scripts/hooks/
# Merge config/settings-snippet.json into ~/.claude/settings.json
# Add PRE-GENERATION-CHECK to relevant skills
node tests/simulate-all.js   # 6 scenarios, should be 100%
```

## Extending

Edit `RULES` object in `hooks/session-start-compliance-audit.js`. One JSON entry per rule:

```javascript
'my-rule': {
  name: 'My Rule',
  triggerPatterns: [/pattern.*for.*action/],
  compliancePatterns: [/pattern.*for.*compliance/],
},
```

## Performance

- CPU: ~10ms per response (Node.js regex match)
- LLM token: 0 (only ~50 token systemMessage on actual violation)
- External deps: 0
- 10-rule stress test: 0.10ms/check, 100% pass

Full documentation: https://github.com/wuykjl/rulehook
