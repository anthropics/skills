# Technique Guide + LLM Governance for Marketing Teams

Two things in one reference: (1) which prompting technique to use for which marketing task, and (2) the governance layer — the rules a marketing team needs so AI-assisted content ships safely, legally, and on-brand at scale.

---

## Part 1: Technique Selection for Marketing Tasks

| Technique | Use when | Marketing examples |
|---|---|---|
| **Zero-shot + tight constraints** | Task is well-specified and format is simple | SEO meta tags, UTM naming, subject lines |
| **Few-shot (2-5 examples)** | Voice/format is hard to describe but easy to show | Brand-voice posts, email tone, ad-angle patterns — paste your 3 best-performing examples |
| **Chain-of-thought / plan-then-write** | Multi-step reasoning before output | Campaign briefs (audience → angle → channel → copy), positioning drafts |
| **Structured output (JSON/schema)** | Output feeds another tool or script | Ad variant sets, calendar entries, anything `prompt_tester.py` will grade by regex |
| **Decomposition (prompt chains)** | One mega-prompt underperforms | Research → outline → draft → brand-voice rewrite → compliance check, each step testable separately |
| **Self-critique pass** | Quality gate before human review | "List 3 weaknesses of this draft against the brief, then fix them" |

**Construction checklist** (every marketing prompt): explicit role + goal; the audience and their pain named; output format with limits (chars/words); constraints as bullets; a forbidden list (clichés, banned claims, competitor names); instruction for missing inputs ("if no proof point fits, omit proof — never invent").

**Failure patterns to check before testing:** objective too broad ("write something engaging"); missing output schema; contradictory constraints (casual tone + formal compliance phrasing in one prompt); no negative instructions, so the model fills gaps with invented stats; hidden assumptions (brand voice referenced but not provided — pass the actual voice profile from `.claude/product-marketing-context.md`).

---

## Part 2: LLM Governance for Marketing

Marketing is a high-exposure surface for AI failure: invented statistics in ads, undisclosed AI-generated endorsements, off-brand tone at scale, and privacy violations in personalization. Governance turns those from incidents into checklist items.

### The Governance Stack

1. **Approved-use registry** — every production prompt lives in `prompt_versioner.py` with a named owner, author history, and change notes. No anonymous prompt edits in production workflows.
2. **Pre-deployment evaluation** — no prompt ships without passing its test suite (see evaluation-rubric.md). Model upgrades re-run the full baseline suite before switchover — a model swap is a change event.
3. **Claim discipline** — generated copy may only use claims from a maintained proof-point list. Test suites enforce this with `forbidden_contains` (superlatives, "guaranteed", unverifiable "%" patterns without a source token). A human verifies any new claim before it enters the proof list.
4. **Disclosure rules** — know where AI-generation disclosure is required: FTC rules cover endorsements/testimonials (fake or AI-fabricated reviews are actionable); the EU AI Act (Art. 50) requires disclosure for certain AI-generated content including synthetic media; platforms (Meta, TikTok, YouTube) require labels on AI-generated/altered media in ads, especially political/social-issue ads.
5. **Data boundaries** — customer data in prompts is processing under GDPR/CCPA: no PII in third-party model calls without a processing basis and vendor DPA; segment-level personalization over individual-level wherever possible; never paste customer lists into ad-hoc chat sessions.
6. **Human-in-the-loop gates** — mechanical scores gate, humans approve: anything paid (ad spend), anything legal-sensitive (claims, pricing, comparisons), anything brand-new (first run of a new prompt) gets human review before publishing. Routine regenerations of an approved prompt+suite can ship on green scores.
7. **Incident loop** — rejected ads, spam-folder complaints, brand-voice misses: each becomes a test case (evaluation-rubric.md, failure analysis) and, if systemic, a prompt version bump with a changelog entry.

### Roles

| Role | Owns |
|---|---|
| Prompt owner (per workflow) | Template, test suite, version history |
| Marketing ops | Registry, model-change re-evaluation calendar |
| Legal/compliance reviewer | Claim list, disclosure map, escalation calls |
| Brand lead | Voice profile, lexicon-yes/no lists |

### Minimum Viable Governance (small team)

If the full stack is too heavy: (1) version every production prompt, (2) maintain the forbidden-claims list and wire it into `forbidden_contains`, (3) human-review everything paid, (4) re-run the suite on model changes. These four catch the expensive failures.

---

## Citations (7 sources)

1. NIST — AI Risk Management Framework 1.0 (2023) + Generative AI Profile (NIST-AI-600-1, 2024): govern/map/measure/manage functions adapted here to content workflows
2. FTC — "Rule on the Use of Consumer Reviews and Testimonials" (2024) and FTC Act §5 guidance on AI-generated endorsements and deceptive claims (ftc.gov)
3. EU AI Act — Regulation (EU) 2024/1689, Art. 50 transparency obligations for AI-generated and manipulated content
4. ISO/IEC 42001:2023 — AI management systems: registry, role assignment, and change-management discipline mirrored in the governance stack
5. Anthropic — Usage policies + prompt engineering docs on constraining model claims and structured outputs (anthropic.com/legal/aup, docs.anthropic.com)
6. Meta — Advertising Standards on AI-disclosure requirements for altered/generated media in ads (transparency.fb.com / Meta Business Help Center)
7. GDPR (Regulation 2016/679) Arts. 6, 28 — processing basis and processor agreements governing customer data sent to model vendors
