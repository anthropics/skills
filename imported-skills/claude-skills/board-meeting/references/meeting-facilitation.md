# Meeting Facilitation Guide

Operational playbook for running board meetings using the 6-phase protocol.
Reference this when things go sideways — and they will.

---

## Keeping Phase 2 Contributions Focused

**The problem:** Agents with deep domain knowledge tend to over-contribute. An unconstrained CFO can produce 1,500 words on a single agenda item. This kills the meeting.

**The rules:**
- **Hard cap: 5 key points per role.** If a role produces more than 5, Chief of Staff trims to the 5 most material.
- **Every point must include a recommendation or stance.** Observations without positions are filler.
- **No hedging language.** "It depends" is not a key point. "We should do X if Y, Z if not Y" is.
- **Confidence rating required.** Forces the agent to be honest about what they actually know.
- **"What would change my mind"** — this is the most important line in the contribution. It forces falsifiability.

**How to enforce:**
```
Chief of Staff instruction to each role:
"You have 5 key points maximum. Each must include a clear stance.
End with your recommendation and what would change your mind.
Do not read other agents' contributions before writing yours."
```

**If a contribution runs long:**
- Trim to the 5 highest-signal points
- Preserve the recommendation and confidence rating
- Flag in the raw transcript: "[Trimmed for meeting — full version in raw log]"

---

## Handling Role Conflicts in Phase 3

**What the Executive Mentor is for:** Not harmony. Not consensus. Productive friction.

**Common conflict types:**

### 1. Data conflict (two agents cite contradictory numbers)
- Flag both numbers explicitly
- Do NOT pick a winner — that's the founder's job
- Ask: "CFO says CAC is $2,400. CRO says $1,800. These can't both be right. Which dataset are you using?"
- Action item: Assign data reconciliation to one owner before next meeting

### 2. Priority conflict (two agents want different things first)
- Surface the underlying assumption difference
- Example: "CMO wants to invest in brand. CFO wants to cut burn. The real question is: do we believe revenue will grow 40% next quarter?"
- Frame as a bet, not a fight

### 3. Role conflict (agent operating outside their lane)
- CFO making product calls → flag and exclude from synthesis
- CMO commenting on architecture → flag and exclude
- The Executive Mentor notes: "[ROLE] contribution on [topic] is outside domain. Excluded from synthesis. Refer to [correct role]."
- This is not an error. It's expected. Executives have opinions on everything. Only domain-relevant contributions count.

### 4. False consensus (everyone agrees but nobody has evidence)
- This is the most dangerous failure mode
- Symptom: All Phase 2 contributions say "yes" with high confidence
- Executive Mentor response: "Unanimous agreement on a hard question is a red flag. What evidence does each of you have? Or are you reasoning from the same assumption?"
- Force each agreeing agent to state their independent evidence

---

## When to Extend vs Cut Short a Meeting

**Extend when:**
- A genuine new risk surfaces in Phase 3 that wasn't in the agenda
- The founder asks a question that requires re-running Phase 2 for a new angle
- A data conflict is discovered that changes the decision space entirely
- The action items from synthesis are unclear or unowned

**How to extend:** Add a new mini-Phase 2 with only the relevant roles for the new question. Don't restart the full meeting.

**Cut short when:**
- The founder has already reached a decision before Phase 4 — capture it, log it, move on
- The agenda item is resolved in Phase 2 without genuine conflict — skip Phase 3, go straight to synthesis
- It's a pure update meeting with no decisions required — skip Phases 2-4, go straight to action items

**Never cut short:**
- Phase 5 (founder review) — always required, always explicit
- Phase 6 (decision extraction) — always required, even for small decisions

---

## Handling Founder Disagreement with All Agents

This happens. The founder has context agents don't.

**Protocol:**
1. Acknowledge explicitly: "You're overriding the consensus position."
2. Ask: "What do you know that the agents didn't factor in?" (Not to challenge — to capture.)
3. Log the override in Layer 2 with full context:
   ```
   User Override: Founder rejected [consensus position] because [reason].
   Decision: [founder's actual decision]
   Agent recommendation: [what they said] — DO NOT RESURFACE without new data
   ```
4. Never push back on a founder override. Document it. Move on.
5. If the same override happens 3+ times, flag a pattern: "You've overridden the CFO on burn rate three meetings in a row. Would you like to update the financial constraints in company-context.md?"

**What NOT to do:**
- Don't say "but the CFO said..."
- Don't re-argue on behalf of any agent
- Don't note it as a "controversial" decision in the minutes — it's just the decision

---

## Common Failure Modes

### Groupthink
**Symptom:** All agents produce similar recommendations with high confidence.
**Cause:** Agents are inadvertently reading each other's outputs (Phase 2 isolation violated), or company-context.md contains implicit bias toward one direction.
**Fix:** Re-run Phase 2 with explicit isolation. Ask: "Give me the strongest argument AGAINST this direction."

### Analysis Paralysis
**Symptom:** Phase 2 produces comprehensive analysis but no clear recommendation from any role.
**Cause:** Agents are hedging. Usually happens on genuinely hard questions.
**Fix:** Force the issue. "I need a recommendation, not an analysis. If you had to bet the company on one direction, what would it be? Confidence can be Low."

### Bikeshedding
**Symptom:** 30+ minutes spent on a detail that doesn't matter to the core decision.
**Cause:** An easy-to-understand sub-problem attracts disproportionate attention.
**Example:** Debating button color on a pricing page instead of the pricing strategy.
**Fix:** Chief of Staff intervenes: "This is a sub-decision. I'm logging it as a separate action item for async resolution. Back to [main agenda item]."

### Scope Creep
**Symptom:** New agenda items keep appearing mid-meeting.
**Cause:** Meeting surfaces real issues that feel urgent.
**Fix:** New items go on a "parking lot" list. Addressed after the current agenda is complete or in the next meeting.
```
🅿️ PARKING LOT
- [Item 1] — added by [role], will address [when]
- [Item 2]
```

### Layer Contamination
**Symptom:** Future meeting references a rejected proposal or a debate that was never approved.
**Cause:** Phase 1 accidentally loaded a raw transcript instead of decisions.md.
**Fix:** Hard rule in Phase 1: load decisions.md (Layer 2) ONLY. Never load raw transcripts. If raw context is needed, founder explicitly requests it.

### Decision Amnesia
**Symptom:** Same question debated again in a later meeting.
**Cause:** Layer 2 decisions.md not consulted in Phase 1, or entry was too vague.
**Fix:** Phase 1 always surfaces relevant past decisions. If a question was already decided, Chief of Staff surfaces it: "We addressed this on [DATE]. Decision was [X]. Do you want to reopen it?"

### Role Fatigue
**Symptom:** Later agents in Phase 2 (CHRO, CRO) produce weaker contributions.
**Cause:** Context window pressure. Agents at the end of a long meeting have less capacity.
**Fix:** For meetings with 7+ roles, split into two batches. First batch: strategic roles (CEO, CFO, CMO). Second batch: operational roles (COO, CHRO, CRO). Run Executive Mentor after all contributions.

---

## Meeting Health Metrics

After each board meeting, score it:

| Metric | Good | Bad |
|--------|------|-----|
| Action items produced | 3–7 | 0 or >10 |
| Decisions with clear owners | 100% | < 80% |
| Unresolved open questions | 1–3 | >5 |
| Founder overrides | 0–2 | >5 (suggests context mismatch) |
| Roles activated | 3–6 | All 9 (too many = noise) |
| Phase 2 conflicts surfaced | At least 1 | 0 (groupthink risk) |

Track these in `~/.claude/decisions/meeting-health.md` over time. Pattern: if action items consistently exceed 8, meetings are too infrequent. If conflicts are consistently 0, isolation is broken.
