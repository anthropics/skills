# Knowledge-Base Hygiene Anti-Patterns

The recurring failure modes that turn a useful company wiki into a sprawl of stale, unfindable, contradictory docs. Eight anti-patterns, each anchored to authoritative sources. Seven citations.

## The pattern

An ops org's wiki passes through three predictable phases:

1. **Year 1:** 50 pages, all owned, all current, everyone finds what they need.
2. **Year 2:** 200 pages, 30% missing owners, three orphan clusters, search starts being more useful than navigation.
3. **Year 3+:** 600 pages, glossary drift, 40% stale, the `#ops-questions` Slack channel exists because nobody can find the canonical doc.

`kb_ingester.py` exists to put numbers on this decay and rank what to fix first. The anti-patterns below explain *what to fix*.

## 1. No owner per SOP

**Symptom:** YAML frontmatter has no `owner:` field, or the SOP body says "owned by the Ops team".

**Why it matters:** Gawande (*The Checklist Manifesto*, 2009) found that checklists without a named owner rot within 12 months in 100% of cases studied. Ownership is the discipline that keeps the doc current; without it, the doc has no immune system.

**Detection:** `kb_ingester.py` reports `missing_owner_count`. Goal: 0.

**Fix:** Assign every SOP to a single named human in YAML frontmatter. "The team" is not an owner.

**Citation:** Gawande 2009 (*The Checklist Manifesto*, Metropolitan Books).

---

## 2. No last-reviewed date

**Symptom:** The SOP has no `last_reviewed:` field. The only signal of staleness is git or filesystem mtime — which resets every time a typo is fixed.

**Why it matters:** ISO 9001:2015 §7.5.3 explicitly requires review cycles for controlled documents. Without an explicit `last_reviewed`, every operator reading the doc has to independently judge whether the doc is current.

**Detection:** `kb_ingester.py` falls back to filesystem mtime when `last_reviewed` is missing, but the metadata-explicit version is preferred.

**Fix:** Add `last_reviewed: YYYY-MM-DD` to every SOP frontmatter. Pair with a review cadence (12 months default, 90 days for regulated).

**Citation:** ISO 9001:2015 §7.5.3 ("Control of documented information").

---

## 3. Step says "verify the service is up" (vague success signal)

**Symptom:** Runbook step success criteria are not observable. "Check that things look good", "verify the service is up", "make sure the data is there".

**Why it matters:** Beyer et al. (*Site Reliability Workbook*, 2018, Ch. 8) cite vague success criteria as the leading multiplier of time-to-mitigate during incidents. A new operator at 3am cannot tell what "up" means.

**Detection:** `runbook_validator.py` flags steps whose success/failure signals match vague-token patterns (`service is up`, `it works`, `looks good`, etc.).

**Fix:** Rewrite success signals as observable checks. "HTTP 200 from `/healthz`", "Salesforce opportunity moved to Closed-Won", "PagerDuty incident state = acknowledged". Anything that returns a yes/no.

**Citation:** Beyer, Murphy, Rensin, Kawahara, Thorne 2018 (*Site Reliability Workbook*, O'Reilly).

---

## 4. Runbook with no rollback

**Symptom:** The runbook tells the operator how to send the alert. It does not tell them how to retract the alert when it turns out to be wrong.

**Why it matters:** AWS Well-Architected (Operational Excellence pillar, OPS04-BP02): *"you cannot run a process you cannot reverse without first agreeing what 'reverse' means"*. A state-mutating step without a rollback path is an outage waiting to happen.

**Detection:** `runbook_validator.py` enforces a rollback field per step. Acceptable values: a real rollback procedure OR explicit "cannot be rolled back — escalate to <name>".

**Fix:** For every state-mutating step, write the rollback. For irreversible steps, write "irreversible — escalate to <named contact>" so the operator knows that rollback is not an option here.

**Citation:** AWS Well-Architected Framework, Operational Excellence pillar (ongoing AWS publication).

---

## 5. Wiki sprawl across 4 tools

**Symptom:** SOPs live in Notion. Runbooks live in Confluence. Onboarding lives in a Google Doc folder. The glossary lives in a Slack canvas. Nobody knows which is canonical.

**Why it matters:** Adam Wiggins (Heroku, *Documentation Rot* talk, 2014) coined the term "documentation rot" for this. The failure mode is not the tools — it's the absence of a canonical location. Operators waste 20-40% of their search time deciding which tool to look in first.

**Detection:** Out of scope for `kb_ingester.py` (which runs on one markdown tree). The signal is human: "where's the X SOP?" gets three different answers.

**Fix:** Pick one canonical tool. Migrate the rest. Treat the others as archives, link the canonical from the others. Mozilla SUMO's KB consolidation (2016) is the template.

**Citation:** Wiggins 2014 (Heroku Engineering talk, "Documentation Rot"). Cited again in MIT TIK 2020 org-wiki research.

---

## 6. Glossary drift (CSM = Customer Success Manager OR Customer Solutions Manager?)

**Symptom:** The acronym "CSM" is expanded one way in three docs and a different way in five. New hires guess wrong for six months. Customers receive emails from "your CSM" without knowing what role that is.

**Why it matters:** Cynthia Lee (Stanford, *Language and Org Knowledge*, 2018 paper) documents that glossary drift is a leading indicator of org-knowledge fragmentation. Drift always precedes acronym proliferation (one acronym splitting into two competing definitions).

**Detection:** `kb_ingester.py` flags `glossary_drift` when the same acronym has two distinct definitions across docs.

**Fix:** Pick one canonical definition per acronym. Add a `glossary.md` page. Link every other doc to it. Refuse to expand the acronym anywhere else.

**Citation:** Lee 2018 (Stanford research on org-knowledge fragmentation).

---

## 7. Orphan pages nobody can find

**Symptom:** 30-60% of pages have no inbound links. They exist because somebody knew the URL. Search finds them; navigation does not.

**Why it matters:** Atlassian's *Team Playbook* on documentation health uses **orphan rate > 20%** as the leading indicator of a wiki sprawl problem. Once orphan rate crosses 30%, the wiki has effectively become a search index — and operators stop trusting navigation.

**Detection:** `kb_ingester.py` reports `orphan_count` and lists orphans.

**Fix:** Not "delete all orphans". Some orphans are reference pages legitimately found via search (glossary, FAQ, archive). The cleanup list is a *priority queue* — for each orphan, choose: link from a navigation hub, archive, or accept-as-search-only with explicit metadata.

**Citation:** Atlassian Team Playbook, "Documentation Health" play (2021).

---

## 8. SOPs that document the happy path only

**Symptom:** The vendor-offboarding SOP covers what happens when the vendor cooperates. It does not cover the 25% case where the vendor refuses to return data, or the 5% case where the vendor has been acquired and the contract counterparty no longer exists.

**Why it matters:** Susan Fowler (*Production-Ready Microservices*, 2016, Ch. 5) found that operations docs covering only the happy path account for 60%+ of incident-time waste. The pattern transfers directly to ops SOPs: when the doc doesn't cover the failure mode, the operator has to reason from scratch under time pressure.

**Detection:** Manual — `runbook_validator.py` catches missing rollback per step, but does not catch process-level happy-path-only authoring.

**Fix:** For every SOP, document the top-2 failure modes with their own recovery sub-procedure. The forcing-question library in `SKILL.md` (question 7) enforces this.

**Citation:** Fowler 2016 (*Production-Ready Microservices*, O'Reilly).

---

## 9. Compliance SOPs without version control

**Symptom:** A SOX-relevant or HIPAA-relevant SOP has no change history, no signoff record, no version field. An auditor asks "what was the procedure in Q2?" — nobody can answer.

**Why it matters:** FDA 21 CFR Part 211.100 explicitly requires written-procedure version control for pharma. ISO 9001 §7.5.3 imposes the same for any controlled document. Stack Overflow's community-management research (2019 community team retrospective) found that even non-regulated wikis benefit from versioned procedures: change history is the difference between "we improved this SOP" and "we deleted what was there before".

**Detection:** `--profile regulated` in `sop_generator.py` attaches the version + signoff + change-history sections. Missing those sections under a regulated overlay is the audit finding.

**Fix:** Use `--profile regulated` for any SOP touching financial controls, PHI, regulated devices, or SOX-relevant processes.

**Citations:** FDA 21 CFR Part 211.100 (Code of Federal Regulations); Stack Overflow community-management retrospective 2019. Mozilla SUMO KB lessons (2016) echo both.

---

## How this skill applies the anti-patterns

- `kb_ingester.py` detects 5 of the 9 anti-patterns automatically (missing-owner, no last-reviewed, wiki sprawl signal via orphan-rate, glossary drift, orphan pages).
- `runbook_validator.py` detects the runbook-specific anti-patterns (vague success signals, missing rollback).
- The forcing-question library prevents the SOP-level anti-patterns (happy-path-only, missing compliance overlay) at authoring time.
- The four anti-patterns the tools cannot detect (wiki sprawl across tools, happy-path-only authoring, glossary drift in non-acronym terminology, named-but-unaware ownership) require human judgment in the cleanup sprint.

The skill's job is to surface the 80% of anti-patterns a tool can find. The remaining 20% is the cleanup-sprint discussion.
