---
name: session-wrap-up
description: "End-of-session wrap-up: token cost summary, session recap, and smart Skill/Plugin recommendations based on what you did. Use when: the user says \"wrap\", \"wrap up\", \"done\", \"bye\", \"finished\", or the conversation is clearly ending. Do NOT use for: mid-session summaries or general Q&A."
license: Complete terms in LICENSE.txt
---

# Session Wrap-Up

Summarize the session and recommend relevant skills/plugins when the conversation ends.

## Execution Flow

### Phase 1: Session Recap

From the current conversation context (do NOT read files), extract:
- What the user accomplished (3-5 bullet points)
- Identify activity type keywords for Phase 2

Activity keyword table:

| Keyword | Trigger |
|---------|---------|
| coding | Wrote code, edited source files |
| frontend | HTML/CSS/React/Next.js/Vue etc. |
| debugging | Debugging, troubleshooting, fixing bugs |
| git | Git operations, commits, PRs |
| api | API development, HTTP requests |
| data | Data processing, batch operations |
| deploy | Deployment, CI/CD |
| project | Project management, task tracking |
| docs | Documentation writing |
| skill_dev | Developing skills or plugins |
| security | Security-related work |
| testing | Testing-related work |
| python | Python development |
| typescript | TypeScript/JS development |

### Phase 2: Smart Recommendations

Run the recommendation script, passing in the activity keywords identified in Phase 1:

```bash
python3 SKILL_DIR/recommend.py <keywords...>
```

The script reads:
- `~/.claude/plugins/installed_plugins.json` — installed plugins
- `~/.claude/plugins/marketplaces/claude-plugins-official/.claude-plugin/marketplace.json` — official plugin registry
- `~/.claude/plugins/install-counts-cache.json` — install counts
- `~/.claude/skills/` — local skill list

Returns JSON with `recommended_new` (not yet installed) and `reminder_installed` (already have).

If any of these files are missing, the script gracefully degrades and still returns results.

### Phase 3: Formatted Output

Combine everything into this format:

```markdown
---
## What you did
- [bullet 1]
- [bullet 2]
- ...

## Recommended for you
1. **plugin-name** (official, XXK installs) — one-line explanation of why
   → `claude plugin install plugin-name@claude-plugins-official`

2. **plugin-name** (official) — one-line explanation
   → `claude plugin install plugin-name@claude-plugins-official`

3. **/skill-name** (installed) — you already have this! One-line reminder of how to use it
---
```

## Recommendation Strategy

Priority ordering:
1. Official plugins > third-party > local skills
2. High install count > obscure
3. Strongly related to this session's activities > generic

Each recommendation MUST include a **one-line explanation**: why it's recommended + how to use it.

## Guidelines

- Do NOT read files to generate the recap — extract directly from conversation context
- Limit to 3 new recommendations + 1-2 installed reminders
- Keep it concise — this is a wrap-up, not a report
