---
name: "board-meeting"
description: "Multi-agent board meeting protocol for strategic decisions. Runs a structured 6-phase deliberation: context loading, independent C-suite contributions (isolated, no cross-pollination), critic analysis, synthesis, founder review, and decision extraction. Use when the user invokes /cs:boardroom, calls a board meeting, or wants structured multi-perspective executive deliberation on a strategic question."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: board-protocol
  updated: 2026-03-05
  frameworks: 6-phase-board, two-layer-memory, independent-contributions
---

# Board Meeting Protocol

Structured multi-agent deliberation that prevents groupthink, captures minority views, and produces clean, actionable decisions.

## Keywords
board meeting, executive deliberation, strategic decision, C-suite, multi-agent, /cs:boardroom, founder review, decision extraction, independent perspectives

## Invoke
`/cs:boardroom [topic]` — e.g. `/cs:boardroom Should we expand to Spain in Q3?`

---

## The 6-Phase Protocol

### PHASE 1: Context Gathering
1. Load `~/.claude/company-context.md`
2. Load Layer 2 approved decisions from `~/.claude/decisions/approved/` **(Layer 2 ONLY — never raw transcripts)**
3. Reset session state — no bleed from previous conversations
4. Present agenda + activated roles → wait for founder confirmation

**Chief of Staff selects relevant roles** based on topic (not all 14 every time):
| Topic | Activate |
|-------|----------|
| Market expansion | CEO, CMO, CFO, CRO, COO |
| Product direction | CEO, CPO, CTO, CMO |
| Hiring/org | CEO, CHRO, CFO, COO (+ VPE for eng hiring) |
| Pricing | CMO, CFO, CRO, CPO |
| Technology | CTO, CPO, CFO, CISO |
| Contracts / term sheets / legal exposure | GC, CEO, CFO |
| Data strategy / training-data rights | CDO, CAIO, GC, CISO |
| AI strategy / model selection / AI risk | CAIO, CTO, CDO, CFO |
| Retention / churn / customer success | CCO, CRO, CPO |
| Eng delivery / DORA / team structure | VPE, CTO, CHRO, CFO |

---

### PHASE 2: Independent Contributions (ISOLATED)

**No cross-pollination. Each agent runs before seeing others' outputs.**

Order: Research (if needed) → CMO → CFO → CEO → CTO → COO → CHRO → CRO → CISO → CPO → GC → CDO → CAIO → CCO → VPE (activated roles only)

**Reasoning techniques:** CEO: Tree of Thought (3 futures) | CFO: Chain of Thought (show the math) | CMO: Recursion of Thought (draft→critique→refine) | CPO: First Principles | CRO: Chain of Thought (pipeline math) | COO: Step by Step (process map) | CTO: ReAct (research→analyze→act) | CISO: Risk-Based (P×I) | CHRO: Empathy + Data | GC: Risk-Based (clause exposure) | CDO: Decision-Driven (what decision does this data drive) | CAIO: Eval-Demanding (no eval, no ship) | CCO: Retention-Obsessed (GRR over NRR) | VPE: Throughput-First (cycle-time math)

**Contribution format (max 5 key points, self-verified):**
```
## [ROLE] — [DATE]

Key points (max 5):
• [Finding] — [VERIFIED/ASSUMED] — 🟢/🟡/🔴
• [Finding] — [VERIFIED/ASSUMED] — 🟢/🟡/🔴

Recommendation: [clear position]
Confidence: High / Medium / Low
Source: [where the data came from]
What would change my mind: [specific condition]
```

Each agent self-verifies before contributing: source attribution, assumption audit, confidence scoring. No untagged claims.

---

### PHASE 3: Critic Analysis
Executive Mentor receives ALL Phase 2 outputs simultaneously. Role: adversarial reviewer, not synthesizer.

Checklist:
- Where did agents agree too easily? (suspicious consensus = red flag)
- What assumptions are shared but unvalidated?
- Who is missing from the room? (customer voice? front-line ops?)
- What risk has nobody mentioned?
- Which agent operated outside their domain?

---

### PHASE 4: Synthesis
Chief of Staff delivers using the **Board Meeting Output** format (defined in `../agent-protocol/SKILL.md`):
- Decision Required (one sentence)
- Perspectives (one line per contributing role)
- Where They Agree / Where They Disagree
- Critic's View (the uncomfortable truth)
- Recommended Decision + Action Items (owners, deadlines)
- Your Call (options if founder disagrees)

---

### PHASE 5: Human in the Loop ⏸️

**Full stop. Wait for the founder.**

```
⏸️ FOUNDER REVIEW — [Paste synthesis]

Options: ✅ Approve | ✏️ Modify | ❌ Reject | ❓ Ask follow-up
```

**Rules:**
- User corrections OVERRIDE agent proposals. No pushback. No "but the CFO said..."
- 30-min inactivity → auto-close as "pending review"
- Reopen any time with `/cs:boardroom resume`

---

### PHASE 6: Decision Extraction
After founder approval:
- **Layer 1:** Write full transcript → `~/.claude/decisions/raw/YYYY-MM-DD-<slug>.md`
- **Layer 2:** Write approved decision record → `~/.claude/decisions/approved/YYYY-MM-DD-<slug>.md` and append to the index `~/.claude/decisions/approved/decisions.md`
- Mark rejected proposals `[DO_NOT_RESURFACE]`
- Confirm to founder with count of decisions logged, actions tracked, flags added

---

## Memory Structure

Uses the canonical two-layer decision memory (see `../agent-protocol/SKILL.md` → "Decision Memory (Canonical Layout)"):

```
~/.claude/decisions/
├── raw/YYYY-MM-DD-<slug>.md        # Layer 1 — full transcripts (never auto-loaded)
├── raw/archive/YYYY/               # Raw transcripts after 90 days
├── approved/YYYY-MM-DD-<slug>.md   # Layer 2 — founder-approved records (Phase 1 loads these)
└── approved/decisions.md           # Layer 2 index — append-only
```

**Future meetings load Layer 2 only.** Never Layer 1. This prevents hallucinated consensus.

Migration: a legacy `memory/board-meetings/` folder may exist from earlier versions; read it for history but write new transcripts and decisions to `~/.claude/decisions/`.

---

## Failure Mode Quick Reference
| Failure | Fix |
|---------|-----|
| Groupthink (all agree) | Re-run Phase 2 isolated; force "strongest argument against" |
| Analysis paralysis | Cap at 5 points; force recommendation even with Low confidence |
| Bikeshedding | Log as async action item; return to main agenda |
| Role bleed (CFO making product calls) | Critic flags; exclude from synthesis |
| Layer contamination | Phase 1 loads `~/.claude/decisions/approved/` only — hard rule |

---

## References
- `templates/meeting-agenda.md` — agenda format
- `templates/meeting-minutes.md` — final output format
- `references/meeting-facilitation.md` — conflict handling, timing, failure modes
