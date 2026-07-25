---
name: "internal-narrative"
description: "Build and maintain one coherent company story across all audiences — employees, investors, customers, candidates, and partners. Detects narrative contradictions and ensures the same truth is framed for each audience's needs. Use when preparing investor updates, all-hands presentations, board communications, recruiting narratives, crisis communications, or when user mentions company narrative, messaging consistency, storytelling, all-hands, investor update, or crisis communication."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: narrative-strategy
  updated: 2026-03-05
  frameworks: narrative-frameworks, all-hands-template
---

# Internal Narrative Builder

One company. Many audiences. Same truth — different lenses. Narrative inconsistency is trust erosion. This skill builds and maintains coherent communication across every stakeholder group.

## Keywords
narrative, company story, internal communication, investor update, all-hands, board communication, crisis communication, messaging, storytelling, narrative consistency, audience translation, founder narrative, employee communication, candidate narrative, partner communication

## Core Principle

**The same fact lands differently depending on who hears it and what they need.**

"We're shifting resources from Product A to Product B" means:
- To employees: "Is my job safe? Why are we abandoning what I built?"
- To investors: "Smart capital allocation — they're doubling down on the winner"
- To customers of Product A: "Are they abandoning us?"
- To candidates: "Exciting new focus — are they decisive?"

Same fact. Four different narratives needed. The skill is maintaining truth while serving each audience's actual question.

---

## Framework

### Step 1: Build the Core Narrative

One paragraph that every other communication derives from. This is the source of truth.

**Core narrative template:**
> [Company name] exists to [mission — present tense, specific]. We're building [what you're building] because [the problem you're solving]. Our approach is [your unique way of doing this]. We're at [honest description of current state] and heading toward [where you're going in concrete terms].

**Good core narrative (example):**
> Acme Health exists to reduce preventable falls in elderly care using smartphone-based mobility analysis. We're building an AI diagnostic tool for care teams because current fall risk assessments are subjective, infrequent, and often wrong. Our approach — using the phone's camera during a 10-second walking test — means no new hardware, no specialist required. We have 80 care facilities in DACH paying us €800K ARR, and we're heading to €3M ARR by demonstrating clinical value at scale before our Series B.

**Bad core narrative:**
> Acme Health is an innovative AI company revolutionizing elderly care through cutting-edge technology that empowers care providers and improves patient outcomes across the continuum of care.

The good version is usable. The bad version says nothing.

---

### Step 2: Audience Translation Matrix

Take the core narrative and translate it for each audience. Same truth, different frame.

| Fact | Employees need to hear | Investors need to hear | Customers need to hear | Candidates need to hear |
|------|----------------------|----------------------|----------------------|------------------------|
| We have 80 customers | "We've proven the model — your work matters" | "Product-market fit signal, capital efficient" | "80 care facilities trust us" | "Traction you'd be joining" |
| We pivoted from hardware | "We were honest enough to change course" | "Capital-efficient pivot to better unit economics" | "We found a faster, simpler way to serve you" | "We make decisions based on evidence, not ego" |
| We missed Q2 revenue | "Here's why, here's the plan, here's what you can do" | "Revenue mix shifted — trailing indicator improving" | [Usually don't tell customers revenue misses] | [Usually not shared externally] |
| We're hiring fast | "The team is growing — your network matters" | "Headcount plan aligned to growth" | [Not relevant unless it affects service] | "This is a rocket ship moment" |

**Rules:**
- Never contradict yourself across audiences. Different framing ≠ different facts.
- "We told investors growth, told employees efficiency" is a contradiction. Audit for this.
- Investors and employees see each other. Board members talk to your team. Candidates google you.

---

### Step 3: Contradiction Detection

Before any major communication, run the contradiction check:

**Question 1:** What did we tell investors last month about [topic]?
**Question 2:** What did we tell employees about the same topic?
**Question 3:** Are these consistent? If not — which version is true?

**Common contradictions:**
- "Efficient growth" to investors + "we're hiring aggressively" to candidates
- "Strong pipeline" to investors + "sales is struggling" at all-hands
- "Customer-first" in culture + recent decisions that clearly prioritized revenue over customer need

**When you catch a contradiction:** Fix the less accurate version, then communicate the correction explicitly. "Last month I said X. After more reflection, X is not quite right. Here's the clearer version."

Correcting yourself before someone else catches it builds more trust than getting caught.

---

### Step 4: Audience-Specific Communication Cadence

| Audience | Format | Frequency | Owner |
|----------|--------|-----------|-------|
| Employees | All-hands | Monthly | CEO |
| Employees | Team updates | Weekly | Team leads |
| Investors | Written update | Monthly | CEO + CFO |
| Board | Board meeting + memo | Quarterly | CEO |
| Customers | Product updates | Per release | CPO / CS |
| Candidates | Careers page + interview narrative | Ongoing | CHRO + Founders |
| Partners | Quarterly business review | Quarterly | BD Lead |

---

### Step 5: All-Hands Structure and Cadence

See `templates/all-hands-template.md` for the full template.

**Principles:**
- Lead with honest state of the company. No spin.
- Connect company performance to individual work: "Here's how what you built contributed to this outcome."
- Give people a reason to be proud of their choice to work here.
- Leave time for real Q&A — not curated questions.

**All-hands failure modes:**
- CEO speaks for 55 of 60 minutes; Q&A is "any quick questions?"
- All good news, all the time — employees know when you're not being honest
- Metrics without context: "ARR grew 15%" without explaining if that's good, bad, or expected
- Questions deflected: "That's a great point, we should follow up on that" → never followed up

---

### Step 6: Crisis Communication

When the narrative breaks — someone leaves publicly, a product fails, a security breach, a press article.

**The 4-hour rule:** If something is public or about to be, communicate internally within 4 hours. Employees should never learn about company news from Twitter.

**Crisis communication sequence:**

**Hour 0–4 (internal first):**
1. CEO or relevant leader sends an internal message
2. Acknowledge what happened factually
3. State what you know and what you don't know yet
4. Tell people what you're doing about it
5. Tell people what they should do if they're asked about it

**Hour 4–24 (external if needed):**
1. External statement (press, social) only if the event is public
2. Consistent with the internal message — same facts, audience-appropriate framing
3. Legal review if any claims or liability involved

**What not to do in a crisis:**
- Silence: letting rumors fill the vacuum
- Spin: people can detect it and it destroys trust
- "No comment": says "we have something to hide"
- Blaming: even if someone else caused the problem, your audience only cares what you're doing about it

**Template for crisis internal communication:**
> "Here's what happened: [factual description]. Here's what we know right now: [known facts]. Here's what we don't know yet: [honest uncertainty]. Here's what we're doing: [specific actions]. Here's what you should do if you're asked about this: [specific guidance]. I'll update you by [specific time] with more information."

---

## Narrative Consistency Checklist

Run before any major external communication:

- [ ] Is this consistent with what we told investors last month?
- [ ] Is this consistent with what we told employees at the last all-hands?
- [ ] Does this contradict anything on our website, careers page, or press releases?
- [ ] If an employee read this external communication, would they recognize the company being described?
- [ ] If an investor read our internal all-hands deck, would they find anything inconsistent?
- [ ] Have we been accurate about our current state, or are we projecting an aspiration?

---

## Key Questions for Narrative

- "Could a new employee explain to a friend why our company exists? What would they say?"
- "What do we tell investors about our strategy? What do we tell employees? Are these the same?"
- "If a journalist asked our team members to describe the company independently, what would they say?"
- "When did we last update our 'why we exist' story? Is it still true?"
- "What's the hardest question we'd get from each audience? Do we have an honest answer?"

## Red Flags

- Different departments describe the company mission differently
- Investor narrative emphasizes growth; employee narrative emphasizes stability (or vice versa)
- All-hands presentations are mostly slides, mostly one-way
- Q&A questions are screened or deflected
- Bad news reaches employees through Slack rumors before leadership communication
- Careers page describes a culture that employees don't recognize

## Integration with Other C-Suite Roles

| When... | Work with... | To... |
|---------|-------------|-------|
| Investor update prep | CFO | Align financial narrative with company narrative |
| Reorg or leadership change | CHRO + CEO | Sequence: employees first, then external |
| Product pivot | CPO | Align customer communication with investor story |
| Culture change | Culture Architect | Ensure internal story is consistent with external employer brand |
| M&A or partnership | CEO + COO | Control information flow, prevent narrative leaks |
| Crisis | All C-suite | Single voice, consistent story, internal first |

## Detailed References
- `references/narrative-frameworks.md` — Storytelling structures, founder narrative, bad news delivery, all-hands templates
- `templates/all-hands-template.md` — All-hands presentation template
