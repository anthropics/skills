# Hybrid Router + Fallback Architecture — When To Delegate, When To Run

This reference answers one decision: **should a research request be delegated to a specialist OR run directly by the orchestrator?** The answer is "either — depending on classification confidence," and the trustability property is **routing transparency**.

## The Core Trade-Off

A purely router-based architecture forces the user to know which specialist applies. A purely monolithic skill produces mediocre output for cases where a specialist would have done better.

The **hybrid** answer: route when confidence is high, run a fallback when it isn't, always surface the decision so the user can correct.

| Architecture | Strength | Weakness |
|---|---|---|
| **Pure router** | Always lands in the right specialist when it knows which one. | Brittle: every miss is a failure (no graceful degradation). |
| **Pure monolith** | Always answers. | Generic answers when a specialist would have done better. |
| **Hybrid (this skill)** | Specialist quality when matched; fallback when not. | Adds a classification step — but it's deterministic + fast. |

## Why Routing Transparency Is Mandatory

The hybrid is **only trustworthy if the user can see the routing decision and override it**. Otherwise the user can't tell when the orchestrator silently downgraded their request to a generic fallback (when a specialist would have done better) or upgraded it to a specialist (when fallback was what they actually wanted).

This is the same property that makes well-designed CI/CD systems trustworthy: the system tells you what stage it's in and lets you intervene. Silent routing is a black box; transparent routing is operable.

## The Three Outcomes (Forcing Frame)

Every invocation produces exactly one of:

1. **Delegation** (classified as specialist-domain, ≥2 signals OR one strong multi-word phrase signal): hand off to specialist verbatim, return their output, log the delegation.
2. **Fallback execution** (no specialist matched OR Q3 user picked "none of the above"): run the 8-step plan-decompose-search-synthesize-cite workflow.
3. **Clarification request** (classification ambiguous, OR a single bare-noun signal matched): ask Q3 (domain disambiguation, with the matched specialist as the recommended answer when there is one), then route based on the answer.

Frame this way to refuse the trap of "router silently runs its fallback because the user didn't explicitly ask for a specialist." That's the failure mode the architecture exists to prevent.

## What Makes A Good Routing Decision

A routing decision is good when:

1. **It uses signal-based deterministic logic** (keyword matching, not LLM reasoning over the query)
2. **It commits at high confidence** (≥2 signals for a specialist)
3. **It refuses to commit at low confidence** (1 signal across multiple specialists, or 0 across all → fallback or clarification)
4. **It surfaces the decision** to the user with the matched signals named
5. **It accepts override** without penalty

Bad routing decisions: LLM-only "vibes" classification, silent delegation, refusal to delegate at high-confidence matches, eager delegation at ambiguous matches.

## Forcing-Function Trade-Offs

The orchestrator's job is to make the routing decision **fast** and **visible**, not to do the research itself when a specialist exists. This forces three design constraints:

- **Minimal intake** — 2-4 questions max. Goal is to route, not to interrogate. Specialist handles its own grill-me.
- **Deterministic classifier** — no LLM round-trip. Signal matching is sub-millisecond.
- **Pass-through delegation** — don't pre-answer specialist questions. Their intake is intentional.

When these constraints are violated, the orchestrator slowly becomes a competitor to the specialists rather than their router.

## Sequencing: What Runs When

```
T+0  User invokes /cs:research with their question
T+0  Q1 (research question) — always asked
T+0  Q2 (output preference) — always asked
T+0  Classifier runs (deterministic, sub-millisecond)
T+0  IF score >= 2 OR single specialist matched one strong multi-word phrase:
       Routing transparency: "Routing to X because Y"
       Proceed with the recommended route if the user doesn't object (no timers)
       Delegate verbatim + return specialist output
     ELSE:
       Q3 (domain disambiguation) — ambiguous OR single bare-noun signal
       (bare-noun case: pre-mark the matched specialist as recommended answer)
       IF Q3 picks specialist: delegate
       IF Q3 picks "none of the above": Q4 → fallback
T+1 turn  Specialist output OR fallback workflow complete
```

This sequencing is what keeps the orchestrator fast on the happy path (specialist matched cleanly) while still degrading gracefully (Q3 + Q4 + fallback for the edge cases).

## What Goes Wrong With Each Component

### Silent delegation (no routing transparency)

User asks "what's the buzz about Anthropic," skill silently routes to `pulse`. User never sees the routing. If they wanted general research instead, they have to notice the output came from pulse, then re-invoke. This burns trust + a session.

**Fix:** Routing transparency is mandatory. State decision + accept override.

### LLM-reasoned classification

Skill uses Claude to "decide" which specialist matches. Adds latency, costs tokens, is non-deterministic across invocations (same query → different route). User can't predict what will route where.

**Fix:** Deterministic keyword matching. Predictability is the value.

### Over-eager specialist routing

Skill routes "research Microsoft" to `dossier` based on the word "research". But the user might want general research about Microsoft, not a competitor dossier. The single weak signal isn't strong enough.

**Fix:** Generic "research [topic]" doesn't route, and a single bare-noun signal ("funding", "fda", "patent", "grant") asks Q3 with a recommended answer instead of silent-routing. Specific multi-word phrases like "dossier on Microsoft" or "background on Microsoft" do route.

### Specialist intake pre-answering

Orchestrator collects Q1 + Q2 + Q3 + Q4 + Q5 (passing all into the specialist). Specialist's own grill-me is now redundant; user has to confirm answers twice.

**Fix:** Pass Q1 + Q2 only. Let specialist run its own intake.

### Fallback when specialist would have done better

User asks "review papers on GLP-1 receptor agonists" but skill runs fallback because the classifier missed "review papers" → "literature review" stemming. User gets generic web-search summary instead of structured litreview output.

**Fix:** Signals list must include all reasonable surface forms ("review papers on", "literature review", "lit review", "litreview", etc.).

## When Hybrid Is The Right Architecture

The hybrid pattern is most valuable when:

- Specialists exist + cover non-trivial portion of likely requests
- Specialists have different intake/output shapes (forcing user to know which to use is a tax)
- Generic fallback exists + is acceptable (better than rejecting the request)
- Routing can be made deterministic (predictable classification > LLM "vibes")

When these aren't true, simpler architectures win:

- No specialists yet? Build the monolith.
- One dominant specialist? Just expose it.
- Routing requires deep reasoning over intent? Use LLM classification (accept the cost).
- Fallback would mislead users? Reject instead of falling back.

## Operational Checklist

Before deploying a hybrid router skill:

- [ ] Specialist registry documented with explicit routing signals per specialist
- [ ] Classifier is deterministic (no LLM in the loop)
- [ ] Confidence threshold defined (≥2 signals for commit)
- [ ] Single-weak-match policy defined (1 signal + only one specialist → route)
- [ ] Ambiguity policy defined (≤1 across all → Q3 disambiguation)
- [ ] Routing transparency is mandatory (decision + override surface)
- [ ] Override path tested
- [ ] Fallback workflow specified end-to-end
- [ ] Audit log captures routing decisions + overrides for later review
- [ ] Anti-patterns documented (LLM classification, silent delegation, etc.)

## Citations (8 sources)

1. **Karpathy, Andrej — "LLM OS" talk (2024).** Source for the orchestrator pattern: a smart top-level dispatcher routing to specialized capabilities is more effective than a single monolithic LLM call. Frames the router-with-fallback as a kernel-vs-syscalls analogy. https://karpathy.ai/

2. **Anthropic — Multi-Agent Research System (2024-2025).** Source for the hybrid router-vs-run trade-off in agentic systems. Anthropic's research orchestrator surfaces routing decisions explicitly + accepts user overrides. Practical implementation of the pattern this skill formalizes. https://www.anthropic.com/research

3. **Schaubroeck et al. — "Bounded Confidence in Multi-Agent Systems" (2018).** Source for the academic framing of why bounded-confidence routing (commit only above threshold) outperforms always-route-or-always-defer architectures. Confidence thresholds prevent both over-eager + under-eager commitment.

4. **Google Search Engineering — Query Classification (industry posts).** Source for the deterministic-keyword-matching pattern in production query routers. Google's query classifier uses signal-based deterministic routing for predictability + debuggability, with LLM-reasoned routing only for the residual that signals miss.

5. **Robert Frost, "The Road Not Taken" (1916).** Cited tongue-in-cheek for the routing decision as a one-way door: once delegated, the user sees the specialist's output, not what fallback would have produced. Routing transparency is what gives the user the option to take the other road.

6. **Kubernetes API server — admission controller chain.** Source for the chain-of-responsibility pattern: each handler classifies + either acts or passes to next. Routing transparency in Kubernetes is the auditable admission decision log. Same property in this skill via `routing_transparency_logger.py`.

7. **Tom Preston-Werner — Semantic Versioning specification.** Source for the principle of explicit, predictable contracts over implicit behavior. SemVer's predictability is what made it adoptable; the same property applies to this skill's deterministic routing.

8. **Jeff Hodges — "Notes on Distributed Systems for Young Bloods" (2013).** Source for the principle that explicit + visible system state is what makes operators trust + intervene. Routing transparency is the operator-trust property for skill orchestration. https://www.somethingsimilar.com/2013/01/14/notes-on-distributed-systems-for-young-bloods/
