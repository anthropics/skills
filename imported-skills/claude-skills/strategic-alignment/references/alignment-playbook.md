# Strategic Alignment Playbook

Techniques for cascading strategy, detecting drift, and maintaining alignment at scale.

---

## 1. Strategy Cascade Techniques

### The One-Page Strategy Filter

Before cascading, compress strategy to one page. If it doesn't fit on one page, it's not clear enough to cascade.

**Template:**
```
Company Strategy — [Quarter/Year]
─────────────────────────────────
WHERE WE'RE GOING (6-word vision):
─────────────────────────────────
TOP 3 PRIORITIES THIS QUARTER:
1. [Priority] — owned by: [name]
2. [Priority] — owned by: [name]
3. [Priority] — owned by: [name]
─────────────────────────────────
WHAT WE'RE NOT DOING:
- [Deprioritized initiative]
- [Deferred until next quarter]
─────────────────────────────────
HOW WE MEASURE SUCCESS:
- [Key metric 1]
- [Key metric 2]
- [Key metric 3]
```

The "What we're NOT doing" section is as important as the priorities. Without it, every team adds their own priorities.

### The Cascade Workshop

**Step 1: Company OKR owners present to all department leads (60 min)**
Walk through each company OKR. Explain the "why" behind each — the reasoning, not just the what.

**Step 2: Department leads draft their OKRs in response (90 min)**
Each department answers: "Given these company OKRs, what is our department uniquely positioned to contribute?"

**Step 3: Cross-check for conflicts and gaps (60 min)**
All departments present their draft OKRs. Flag: Which company OKR has no department support? Which two departments might conflict?

**Step 4: Resolve before publishing (30 min)**
Assign missing coverage. Negotiate shared metrics for conflict-prone areas.

**Step 5: Cascade to teams and individuals**
Each department lead runs the same workshop with their teams within 1 week.

### Cascade rules

1. **Bottom-up complements top-down.** Some goals should emerge from teams, not be handed down. Reserve 20–30% of each team's OKRs for team-defined goals that connect to company direction.

2. **Every team goal needs a parent.** If you can't draw a line from a team goal to a company OKR, the goal is either wrong or the company OKR is incomplete.

3. **Cascade the WHY, not just the WHAT.** "Achieve €800K ARR in DACH" without context produces different behaviors than "Achieve €800K ARR in DACH to demonstrate product-market fit before our Series B in Q4."

---

## 2. The Telephone Game Problem and How to Beat It

### The problem

A study by a leadership development firm found that:
- 95% of employees can't name their company's top strategic priorities
- Of those who can, 60% interpret them differently than leadership intended

This is the telephone game at scale. It's not a communication failure — it's an organizational physics problem.

### Why strategy degrades

**Layer 1 → Layer 2:** Managers interpret strategy through their own context. "Focus on efficiency" becomes "cut costs" in Operations and "ship fewer features" in Engineering.

**Layer 2 → Layer 3:** Teams interpret their manager's interpretation. The original strategy is now third-hand.

**Written vs. oral:** Written documents persist. Oral communication changes with each telling. Most cascade happens orally.

**Recency bias:** The last thing said overwrites earlier context. A strategy set in January doesn't survive a September all-hands that emphasizes something different.

### How to beat it

**Repetition is the solution, not the problem.** Most leaders communicate a strategy once and assume it was received. Research on organizational communication suggests 7+ exposures before a message changes behavior.

**Vary the format.** Same message in writing, verbal, visual, story, and example. Different people receive different formats.

**Create shared vocabulary.** If everyone calls the strategy by the same name, it creates a reference point. "We're in DACH focus mode" is more transmissible than a paragraph.

**Test comprehension, not communication.** Ask random team members: "What are our top 3 priorities right now?" The answer tells you whether cascade worked, not whether you communicated.

**Use stories, not slides.** "Here's a decision we made last week that's a perfect example of the strategy" is more memorable than restating the OKR.

---

## 3. Cross-Functional OKR Design

Silos form when teams have no shared goals. The fix: design OKRs that require multiple teams to cooperate.

### Shared ownership OKR

**Format:**
```
Objective: [What we'll achieve together]
Primary owner: [Team A]
Contributing owner: [Team B]

Key Results:
- KR owned by Team A: [Metric]
- KR owned by Team B: [Metric]
- Shared KR (both teams): [Metric that requires both]
```

**Example:**
```
Objective: Launch the partner API and acquire first 3 integrations
Primary owner: Engineering
Contributing owner: Business Development

KR 1 (Engineering): API v1 live with 100% documentation by Week 8
KR 2 (BD): 3 signed partner integration agreements by EoQ
KR 3 (Shared): First partner integration live and in production by EoQ
```

### Cross-functional conflict metric

When two teams' goals are potentially in conflict, add a shared guardrail metric:

**Example:**
- Sales goal: 15 new logos
- CS goal: Churn < 2%
- **Shared guardrail:** New customer 90-day churn < 5% (Sales can't close unqualified customers; CS can't blame Sales for their churn)

---

## 4. Alignment Check Cadence

### Quarterly alignment check (before OKR planning)

Run this before setting next quarter's OKRs:

**Week −2 (2 weeks before quarter start):**
- All teams review current OKRs: Which are we hitting? Which are we missing?
- Run the alignment checker: Orphans? Gaps? Conflicts?

**Week −1:**
- Cascade workshop: Company sets next quarter's OKRs
- Cross-functional conflict review
- Coverage gap assignment

**Week 1 of new quarter:**
- All teams have finalized OKRs with documented parent company OKRs
- Shared OKRs documented with co-owners
- Guardrail metrics in place for known conflict areas

### Monthly alignment pulse

One question added to monthly department reviews:
**"How is our work moving the company-level OKRs? What's the connection?"**

Force each team lead to articulate the link. If they struggle, the cascade has broken.

### Weekly alignment signal

One question added to leadership L10 meetings:
**"Is there anything happening in our team that's at odds with the company strategy?"**

This creates a standing invitation to surface misalignment before it compounds.

---

## 5. Common Misalignment Patterns by Company Stage

### Seed stage (< 20 people)

**Pattern:** Everyone knows everything, alignment is informal. You don't need OKRs — you have daily contact.

**Risk:** Informal alignment breaks when you hire past 15 people and not everyone is in every conversation.

**Fix:** Start documenting strategy at 10–12 people, before it's painful. Establishing the habit early is easier than retrofitting at 50.

### Early growth (20–60 people)

**Pattern:** Functions are forming. Sales, Product, Engineering operate somewhat independently. Communication slows.

**Common misalignment:** Engineering builds features that Sales didn't ask for. Sales promises features Engineering hasn't planned.

**Fix:** Introduce a shared quarterly planning session. Sales and Product review the roadmap together. Engineering and Sales share a customer pipeline update monthly.

### Scaling (60–200 people)

**Pattern:** Multiple layers of management. Strategy takes longer to reach ICs. Managers filter differently.

**Common misalignment:** Department heads optimize their own metrics. Cross-functional projects stall because nobody owns the intersection.

**Fix:** Cross-functional OKRs. Shared metrics. An explicit alignment check in the quarterly planning process (use the alignment_checker.py script).

### Large (200+ people)

**Pattern:** Sub-strategies form. Business units, geographies, and product lines develop their own goals that drift from company strategy over time.

**Common misalignment:** Business unit A and Business unit B compete for the same customer segment. Platform team builds for internal use-cases that differ from external product direction.

**Fix:** Annual strategy alignment summit across business units. Centralized OKR system with visible cross-functional connections. Dedicated alignment role (often the COO or Chief of Staff).
