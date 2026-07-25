# Routing Matrix

Detailed routing rules for the Chief of Staff. When a founder asks a question, find the best match in this matrix, then apply the scoring rules to determine single-role, multi-role, or board meeting.

---

## Routing by Domain

### Finance & Capital

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| How much runway do we have? | CFO | — | 1 |
| Should we raise now or later? | CFO | CEO | 3 |
| What's our burn multiple? | CFO | COO | 2 |
| Should we raise a bridge or cut costs? | CFO | CEO, COO | 5 |
| What's the right pricing model? | CFO | CRO, CPO | 4 |
| Should we hire or extend runway? | CFO | CHRO, COO | 4 |
| What terms should we accept for this round? | CFO | CEO | 3 |
| How do we model the next 18 months? | CFO | COO | 2 |

### People & Culture

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Should I let this person go? | CHRO | COO | 2 |
| How do I structure comp for the team? | CHRO | CFO | 3 |
| We have a culture problem — what do we do? | CHRO | CEO | 3 |
| A leader on my team isn't working — now what? | CHRO | COO | 2 |
| How do I hire fast without breaking culture? | CHRO | COO | 3 |
| Two co-founders are in conflict | CHRO | CEO | 4 |
| How do we retain our best people? | CHRO | CFO | 2 |
| What does a good performance management process look like? | CHRO | COO | 2 |

### Product

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| What should we build next? | CPO | CTO | 2 |
| Should we kill this feature? | CPO | CTO, CRO | 3 |
| How do we prioritize the roadmap? | CPO | CTO, COO | 3 |
| Are we pre-PMF or post-PMF? | CPO | CRO, CEO | 4 |
| Should we build vs buy? | CPO | CTO, CFO | 4 |
| How do we handle technical debt vs new features? | CTO | CPO | 3 |
| What's our product strategy for next year? | CPO | CEO, CRO | 4 |

### Technology & Engineering

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| What architecture should we use? | CTO | CPO | 1 |
| How do we scale the system to 10x traffic? | CTO | COO | 2 |
| We have a security incident — what now? | CISO | CTO, COO | 5 |
| Should we migrate to microservices? | CTO | COO, CFO | 4 |
| How do I grow the engineering team? | CTO | CHRO, CFO | 3 |
| Our engineering velocity is dropping — why? | CTO | COO | 2 |
| What's our DevOps maturity? | CTO | COO | 1 |
| How do we handle a compliance audit on our tech? | CISO | CTO | 3 |

### Sales & Revenue

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Why aren't we closing deals? | CRO | CPO | 2 |
| How do we build a sales process from scratch? | CRO | COO | 2 |
| What's the right GTM for this market? | CRO | CMO, CEO | 4 |
| Our churn is too high — root cause? | CRO | CPO, CHRO | 3 |
| Should we go enterprise or stay SMB? | CRO | CPO, CFO | 4 |
| How do we expand into a new market? | CRO | CMO, CEO, CFO | 5 |
| What's our ideal customer profile? | CRO | CPO, CMO | 3 |
| Pipeline is dry — what do we do? | CRO | CMO | 2 |

### Operations & Execution

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Why do things keep breaking? | COO | CTO | 2 |
| How do we set up OKRs? | COO | CEO | 2 |
| Our meetings are useless — fix it | COO | — | 1 |
| How do we scale operations without hiring? | COO | CTO, CFO | 3 |
| There's a recurring bottleneck — how to fix it? | COO | CTO | 2 |
| We need a cross-team process for X | COO | Relevant dept head | 2 |
| How do we improve decision speed? | COO | CEO | 3 |

### Marketing & Brand

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| How do we position against Competitor X? | CMO | CRO | 2 |
| What channels should we invest in? | CMO | CRO, CFO | 3 |
| Our brand isn't resonating — why? | CMO | CPO, CRO | 3 |
| How do we build a content strategy? | CMO | CRO | 2 |
| What's our marketing budget allocation? | CMO | CFO, CRO | 3 |

### Security & Compliance

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| How do we pass an ISO 27001 audit? | CISO | COO | 2 |
| We had a data breach — what now? | CISO | CTO, CEO, COO | 5 |
| How do we handle GDPR compliance? | CISO | CTO | 2 |
| What's our security posture? | CISO | CTO | 1 |
| A regulator is asking questions | CISO | CEO, COO | 4 |

### Legal & Contracts

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Is this contract safe to sign? | GC | CFO | 2 |
| What's wrong with this term sheet? | GC | CFO, CEO | 3 |
| Do we own the IP our contractors wrote? | GC | CTO | 2 |
| A customer wants an MSA redline — what matters? | GC | CRO | 2 |
| Are we exposed on data privacy / GDPR? | GC | CISO, CDO | 3 |

### Data Strategy

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Can we train models on our customer data? | CDO | GC, CAIO | 3 |
| Warehouse, lakehouse, or mesh? | CDO | CTO | 2 |
| Is our data an asset we can productize or sell? | CDO | CFO, GC | 3 |
| How do we value our data in M&A diligence? | CDO | CFO | 3 |

### AI Strategy

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Should we use an API, fine-tune, or build our own model? | CAIO | CTO, CFO | 3 |
| What does the EU AI Act mean for this feature? | CAIO | GC, CISO | 3 |
| Our AI costs are exploding — what now? | CAIO | CFO | 2 |
| How do we eval / set a hallucination SLO? | CAIO | CTO | 2 |

### Customer & Retention

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Gross retention dropped — why? | CCO | CRO, CPO | 3 |
| How many CSMs do we need per ARR tier? | CCO | CFO, CHRO | 2 |
| Which customers should we fire? | CCO | CRO | 2 |
| NRR looks fine but logos keep leaving | CCO | CRO, CPO | 3 |

### Engineering Delivery

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Why is shipping so slow? (cycle time, DORA) | VPE | CTO | 2 |
| How should we structure eng teams at this headcount? | VPE | CHRO | 2 |
| Our eng hiring funnel is leaking — where? | VPE | CHRO | 2 |
| Eng delivery vs architecture debt trade-off | VPE | CTO, CPO | 3 |

### Strategic Direction

| Question type | Primary | Secondary | Score |
|--------------|---------|-----------|-------|
| Should we pivot? | CEO | Board meeting | 5 |
| Are we building the right company? | CEO | Board meeting | 5 |
| How do we handle an acquisition offer? | CEO | CFO, Board meeting | 5 |
| What's the 3-year strategy? | CEO | All C-suite, board | 5 |
| Should we enter a new vertical? | CEO | CRO, CFO, CPO | 4 |

---

## When to Invoke Multiple Roles

Invoke 2 roles when:
- The question sits at the boundary of two domains
- One role's answer creates a constraint the other needs to know about
- The founder explicitly wants two perspectives

Invoke 3+ roles (board) when:
- The question involves irreversible resource commitment
- There's a known tension between functions (e.g., product vs revenue, speed vs quality)
- The answer will change how multiple teams operate
- It's a company-direction question, not an operational one

---

## When NOT to Invoke Multiple Roles

Don't multi-invoke when:
- The answer is technical and one role clearly owns it
- The founder just needs a framework, not a decision
- Invoking more roles would add noise without adding signal
- Time is short and a directional answer beats a comprehensive one

---

## Escalation Criteria → Board Meeting

Automatically escalate to board meeting when any of these apply:

1. **Irreversibility:** The decision is hard or impossible to reverse (layoffs, pivots, major contracts, fundraising terms)
2. **Cross-functional resource impact:** The decision changes budget, headcount, or priorities for 2+ teams
3. **Founder blind spot risk:** The topic is in an area where the founder's archetype creates a known gap (e.g., technical founder on GTM)
4. **Disagreement expected:** The domains involved are known to have competing incentives (CFO vs CRO on pricing, CTO vs CPO on tech debt)
5. **Explicit request:** Founder says "what does the team think" or "I want multiple perspectives"
6. **Score ≥ 4**

---

## Role Registry

| Role | File | Domain |
|------|------|--------|
| CEO | ceo-advisor | Strategy, culture, investor relations |
| CFO | cfo-advisor | Finance, capital, unit economics |
| COO | coo-advisor | Operations, OKRs, scaling |
| CTO | cto-advisor | Engineering, architecture, tech strategy |
| CPO | cpo-advisor | Product, roadmap, UX |
| CRO | cro-advisor | Revenue, sales, GTM |
| CMO | cmo-advisor | Marketing, brand, positioning |
| CHRO | chro-advisor | People, culture, hiring |
| CISO | ciso-advisor | Security, compliance, risk |
| GC | general-counsel-advisor | Legal, contracts, term sheets, IP |
| CDO | chief-data-officer-advisor | Data strategy, training-data rights, data assets |
| CAIO | chief-ai-officer-advisor | AI strategy, model selection, evals, AI risk |
| CCO | chief-customer-officer-advisor | Retention, churn, customer success |
| VPE | vpe-advisor | Eng delivery, DORA, eng hiring, team structure |

**If a role file doesn't exist:** Note the gap. Answer from first principles with domain expertise. Log that the role is missing.

---

## Complementary Skills Registry

These skills are invoked for specific cross-cutting needs, not for general domain questions.

### Orchestration & Infrastructure
| Skill | Trigger | File |
|-------|---------|------|
| C-Suite Onboard | `/cs:setup`, first-time setup, "tell me about your company" | cs-onboard |
| Context Engine | Auto-loaded; staleness check | context-engine |
| Board Meeting | `/cs:boardroom`, multi-role decisions, score ≥ 4 | board-meeting |
| Decision Logger | After board meetings, `/cs:decisions`, `/cs:review` | decision-logger |
| Agent Protocol | Inter-role invocations, loop detection | agent-protocol |

### Cross-Cutting Capabilities
| Skill | Trigger | File |
|-------|---------|------|
| Board Deck Builder | "board deck", "investor update", "board presentation" | board-deck-builder |
| Scenario War Room | "what if", multi-variable scenarios, stress test across functions | scenario-war-room |
| Competitive Intelligence | "competitor", "competitive analysis", "battlecard", "who's winning" | competitive-intel |
| Org Health Diagnostic | "how healthy are we", "org health", "company health check" | org-health-diagnostic |
| M&A Playbook | "acquisition", "M&A", "due diligence", "being acquired" | ma-playbook |
| International Expansion | "expand to", "new market", "international", "localization" | intl-expansion |

### Culture & Collaboration
| Skill | Trigger | File |
|-------|---------|------|
| Culture Architect | "values", "culture", "mission", "vision", culture problems | culture-architect |
| Company OS | "operating system", "EOS", "Scaling Up", "meeting cadence", "how do we run" | company-os |
| Founder Coach | "delegation", "blind spots", "founder growth", "leadership style", burnout | founder-coach |
| Strategic Alignment | "alignment", "silos", "teams not aligned", "strategy cascade" | strategic-alignment |
| Change Management | "rolling out", "reorg", "change", "new process", "transition" | change-management |
| Internal Narrative | "all-hands", "internal comms", "how do we tell", "narrative" | internal-narrative |

### Routing Priority

1. Check if it matches a **complementary skill trigger** → route there
2. Check if it matches a **single role domain** → route to that role
3. Check if it spans **multiple role domains** (score ≥ 3) → invoke multiple roles
4. Check if it meets **escalation criteria** (score ≥ 4 or irreversible) → trigger board meeting
5. If unclear → ask one clarifying question, then route
