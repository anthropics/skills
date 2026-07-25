---
name: knowledge-ops
description: Use when a Head of Ops, Knowledge Manager, or TPM-Internal needs to author, validate, or clean up company SOPs and internal runbooks (procurement intake, vendor offboarding, incident-comms cascade, employee onboarding) — including 5W2H completeness checks (Who-What-When-Where-Why-How-HowMuch), cross-link and orphan-page validation across a sprawling Notion/Confluence/Obsidian wiki, KB ingestion + hygiene reporting, and runbook step verification (named owner, expected duration, observable success signal, rollback path, escalation contact). Pairs Ishikawa's 5W2H method, Gawande's *The Checklist Manifesto*, ISO 9001, ITIL v4, and Google SRE Workbook runbook discipline with deterministic stdlib-only Python tools that score completeness, detect anti-patterns, and emit prioritized cleanup lists (e.g., "validate this runbook before it goes into rotation", "audit our Confluence wiki for stale and orphaned SOPs").
context: fork
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [bizops, sop, runbook, knowledge-management, kb, 5w2h, wiki, ops-documentation]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# knowledge-ops

Company SOP + internal runbook authoring, 5W2H completeness validation, and KB hygiene reporting for Head-of-Ops / Knowledge-Manager / TPM-Internal personas.

## Purpose

An ops organization three years in accumulates a sprawl: 600 Notion pages, 200 Confluence runbooks, three Obsidian vaults, a `Drive/SOPs/` folder, and a `Slack #ops-questions` channel that exists because nobody can find the canonical doc. Predictable failure modes:

1. **No owner** — 40% of SOPs name "the team" instead of a person. When the doc rots, nobody is accountable.
2. **No last-reviewed date** — a years-old vendor-offboarding SOP still references a procurement tool that was sunset over a year ago.
3. **Vague success signals** — runbook step 4 says "verify the service is up". A new operator can't tell what that means.
4. **No rollback path** — incident-comms cascade runbook tells you how to send the alert. It doesn't tell you how to retract it when the alert was wrong.
5. **Orphan pages** — half the KB has no inbound links. Nobody finds them via navigation; they only exist because somebody knew the URL.
6. **Glossary drift** — "CSM" means Customer Success Manager in three docs and Customer Solutions Manager in five. New hires guess wrong for six months.
7. **Happy-path-only SOPs** — the doc covers what happens when everything works. It doesn't cover the 30% case where it doesn't.

This skill answers the operator's actual question: **"Which 20 docs do I fix first, and what specifically is wrong with each?"** — with deterministic logic, not intuition.

## When to use

- Authoring a new SOP for a cross-functional company process (procurement intake, vendor offboarding, incident-comms cascade, employee onboarding, expense reimbursement, customer-escalation playbook, security-incident comms, system-access provisioning).
- Validating an existing internal runbook before it goes into rotation (every step must have a named owner, expected duration, observable success signal, observable failure signal, rollback path, escalation contact).
- Ingesting a multi-document KB export (Notion zip, Confluence space export, Obsidian vault, `Drive/SOPs/` directory) and surfacing what's broken: orphan pages, stale pages (no edit > 12 months), glossary drift, missing-owner pages, cross-link map.
- Onboarding a new ops hire by generating the SOPs and ops-handbook pages they need to read in week 1.
- Wiki cleanup sprints — quarterly hygiene work where the org decides which 30 docs to archive, rewrite, or merge.

## Workflow

Four-step deterministic flow (matches the ops org's actual workflow, not an abstract process):

1. **Ingest KB.** Run `kb_ingester.py --input <vault-dir>` on the existing wiki export. Output is a markdown health report: orphan pages, stale pages, glossary drift, missing-owner pages, cross-link map, prioritized cleanup list. The report ranks the top-20 docs to fix first — usually a mix of high-traffic stale docs and compliance-relevant missing-owner docs. Take this list to the cleanup sprint.
2. **Validate existing runbooks.** For each runbook in the cleanup list (or any new runbook before it goes into rotation), run `runbook_validator.py --input <runbook.md>`. The validator scores each step against six checks (named owner, expected duration, observable success signal, observable failure signal, rollback path, escalation contact) and produces a per-step traffic-light + overall validity score 0-100 + MUST-FIX issue list. A runbook scoring < 60 is not safe to use in an incident.
3. **Generate missing SOPs.** For SOPs that need to be written from scratch (or rewritten because the existing one is unsalvageable), run `sop_generator.py --input <metadata.json> --profile <ops|support|finance|hr|it|regulated>`. Output is a 5W2H-structured SOP scaffold: Who (RACI), What (process steps), When (triggers + frequency), Where (system + tool), Why (purpose + regulatory basis), How (step-by-step), How-much (cost + time per execution). The `regulated` profile adds version control, signoff, and audit-trail sections (ISO 9001 / FDA 21 CFR Part 211 / SOC 2 / HIPAA).
4. **Cross-link + close the loop.** Re-run `kb_ingester.py` after the cleanup sprint to verify orphan-page count is down and glossary drift is resolved. The metric that matters is **"unfindable docs"** (orphans) and **"unsafe runbooks"** (validity score < 60) — not page count.

## Scripts

**`scripts/sop_generator.py`** — Reads a JSON metadata file describing an SOP (process owner, triggering event, audience role, frequency, regulatory overlay, inputs, outputs, steps outline) and emits a full 5W2H-structured SOP in markdown (or normalized JSON). The `--profile` flag tunes the output: `ops` (general internal ops), `support` (customer-support runbook style), `finance` (controls + reconciliation focus), `hr` (sensitive-data flagging), `it` (system + access focus), `regulated` (adds version control, signoff matrix, audit-trail). Regulatory overlays (`SOC2`, `HIPAA`, `ISO13485`, `GDPR`, `SOX`) attach the appropriate compliance preamble. `--sample` prints a complete vendor-offboarding SOP example. Stdlib only.

**`scripts/runbook_validator.py`** — Reads a runbook (markdown file or JSON) and validates each step against six required attributes: (1) named owner (not "the team", not "ops"), (2) expected duration (concrete number + unit), (3) observable success signal (e.g., "HTTP 200 from `/healthz`" — not "service is up"), (4) observable failure signal, (5) rollback path (or explicit "this step cannot be rolled back, escalate to X"), (6) escalation contact (named person or named on-call rotation). Output is a per-step traffic-light (GREEN/AMBER/RED), an overall validity score 0-100, and a MUST-FIX issue list. Verdict: ≥ 80 = SAFE-TO-USE, 60-79 = USE-WITH-CAUTION, < 60 = NOT-SAFE. `--sample` prints a deliberately-broken incident-comms runbook to demonstrate failure detection. Stdlib only.

**`scripts/kb_ingester.py`** — Walks a directory of markdown files (Notion export, Confluence space export, Obsidian vault, `Drive/SOPs/` directory). Extracts: (a) cross-link map (which page references which, via markdown `[link](path)` syntax), (b) glossary candidates (frequently used proper nouns and acronyms that recur in 3+ docs without a single canonical definition page), (c) orphan pages (no inbound links from anywhere in the vault), (d) glossary drift (the same term defined or used inconsistently across docs — e.g., "CSM" expanded differently in two places), (e) stale pages (no edit in > 12 months, detected via filesystem mtime or YAML `last_reviewed` frontmatter), (f) missing-owner pages (no `owner:` field in frontmatter). Emits a KB health report markdown with a prioritized top-20 cleanup list ranked by `staleness × inbound-link-count` (high-traffic stale docs first). `--sample` builds a tiny synthetic 8-page vault in a tmpdir and runs the full pipeline against it. Stdlib only.

## Quick example

```bash
# Builds a synthetic 8-page vault and emits a KB health report (orphans, stale pages, glossary drift, top-20 cleanup list)
cd business-operations/skills/knowledge-ops && python3 scripts/kb_ingester.py --sample
```

## References

- `references/5w2h_sop_canon.md` — Kaoru Ishikawa's 5W2H method, Toyota standard-work discipline, Atul Gawande's checklist manifesto, Atlassian Confluence SOP guidance, ISO 9001 SOP requirements, ITIL v4 Service Operation, FDA 21 CFR Part 211. Eight cited sources covering SOP authoring canon.
- `references/runbook_canon.md` — Google SRE Workbook (runbook chapter), Atlassian incident-management runbooks, PagerDuty Incident Response taxonomy, AWS Well-Architected operational excellence pillar, Charity Majors on observability-runbook integration, Susan Fowler on production-ready microservices, ITIL v4 Operations. Seven cited sources covering runbook design canon.
- `references/kb_hygiene_anti_patterns.md` — Eight anti-patterns drawn from Notion/Confluence wiki industry research, Mozilla SUMO knowledge-base lessons, Stack Overflow community-management research, the Atlassian Team Playbook, MIT TIK org-wiki studies, Cynthia Lee on glossary drift, and Adam Wiggins on "documentation rot".

## Assumptions

1. The KB is in markdown (or can be exported to markdown — Notion, Confluence, Obsidian, and Google Docs all support this). HTML-only or PDF-only KBs require a conversion pass first; out of scope.
2. The user has authority to commission rewrites or archives. Producing a cleanup list nobody acts on is wasted work — route findings to a named owner before running the ingester.
3. Owner metadata lives in YAML frontmatter (`owner: alex@company.com`) or in a top-of-page "Owner:" line. Tribal-knowledge ownership (the person who last edited the page) is treated as missing.
4. "Stale" defaults to 12 months. Override with `--stale-days` on `kb_ingester.py`. Some compliance regimes (FDA, ISO 13485) require shorter review cycles; use `--profile regulated` and `--stale-days 365`.
5. The user is not asking for a personal PKM. Personal Karpathy-style second-brain work belongs in `engineering/llm-wiki`.

## Anti-patterns

- **Generating SOPs in bulk without owners.** A doc with no owner has a half-life of 6 months. Refuse to generate a batch of 30 SOPs unless each one is assigned to a named human.
- **Using `runbook_validator.py` as a checkbox.** The validator catches missing structure. It does not catch wrong content. A runbook can score 100 and still tell the operator the wrong thing.
- **Treating orphan pages as garbage by default.** Some orphans are reference pages found only via search — not all orphans should be archived. The cleanup list is a *priority queue*, not a delete list.
- **Confusing knowledge-ops with `process-mapper`.** Process-mapper documents the *flow* of work between stages (BPMN, cycle time, bottleneck). Knowledge-ops documents the *artifacts* operators consume to execute the work (SOP, runbook, glossary). Both can apply to the same process.
- **Letting glossary drift accumulate.** Two definitions of "CSM" in three years becomes seven definitions in five. Fix glossary drift the moment it surfaces in `kb_ingester.py` output.
- **Skipping the regulated profile under regulated workload.** If the process touches PHI, SOX-relevant financial controls, or ISO 13485 device QMS, use `--profile regulated`. Missing version control on a regulated SOP is an audit finding.
- **Hand-writing 5W2H sections from memory.** The 5W2H scaffold exists because operators forget "How-much". Use the generator; edit the output.

## Distinct from

- **`engineering/llm-wiki`** — Karpathy-style personal PKM second brain where one human ingests sources into their own interlinked vault. Knowledge-ops is *organizational*: many authors, many readers, named owners per doc, formal review cycles, compliance overlays.
- **`engineering-team/runbook-generator`** — system-ops runbook for debugging a production system (logs, alerts, k8s, on-call). Knowledge-ops runbooks are *operator* runbooks for business processes (incident-comms cascade, vendor offboarding, employee onboarding). The audience is fellow operators, not engineers tailing logs.
- **`project-management/*`** — Jira / Confluence delivery tracking, sprint ticket workflow, project-status reporting. Knowledge-ops is the *content* in those Confluence pages, not the *tracking* of who edits them.
- **`business-operations/process-mapper`** (sibling) — BPMN process *design*: where the stages are, where work waits, which stage is the bottleneck. Knowledge-ops is process *documentation*: the SOP and runbook artifacts that tell an operator how to execute the process the mapper described.
- **`business-operations/internal-comms`** (sibling) — broadcast announcements, all-hands messaging, change-management comms. Knowledge-ops is the durable reference artifact; internal-comms is the broadcast.
- **`ra-qm-team/*`** — formal regulatory compliance authoring (ISO 13485 QMS, MDR technical files, 21 CFR Part 820). Knowledge-ops borrows the regulatory checklist but is not a substitute for a notified-body audit.

## Forcing-question library (Matt Pocock grill discipline)

Before invoking the tools, the orchestrator (or `/cs:grill-bizops`) walks the user through these questions **one at a time, with a recommended answer + canon citation**. Never bundled. Walk depth-first — do not open question 4 until 1-3 are locked.

1. **"Who is the named owner of this SOP / runbook, and do they know they own it?"**
   Recommended: a single human (not "the team"), and yes — they have agreed in writing.
   Canon: Gawande 2009 (*The Checklist Manifesto*) — checklists without an owner rot within 12 months. Ownership is the discipline.

2. **"When was this doc last reviewed, and what is the review cadence?"**
   Recommended: reviewed within the last 12 months (90 days if `--profile regulated`); cadence written in the frontmatter.
   Canon: ISO 9001:2015 §7.5.3 — controlled documents require review-cycle metadata. ITIL v4 echoes this for Service Operation runbooks.

3. **"For each runbook step: what is the observable success signal — by which I mean, what specific output tells you the step worked?"**
   Recommended: a concrete observable ("HTTP 200 from `/healthz`", "Slack thread closed with `done` reaction", "Salesforce opportunity moved to `Closed-Won` stage") — not "the service is up" or "it works".
   Canon: Beyer et al. 2018 (*Site Reliability Workbook*, Ch. 8) — observable signals are the entire point of a runbook. Vague success criteria are the leading cause of runbook misuse during incidents.

4. **"What is the rollback path for each runbook step that can fail?"**
   Recommended: every step that mutates state has either a rollback path or an explicit "cannot roll back — escalate to X" line.
   Canon: AWS Well-Architected Framework, Operational Excellence pillar — "you cannot run a process you cannot reverse without first agreeing what 'reverse' means".

5. **"Where does this doc live, and what other docs link to it?"**
   Recommended: in the canonical wiki, and at least 2 inbound links from related docs. An orphan SOP is an unfindable SOP.
   Canon: Atlassian Team Playbook on documentation health — orphan rate > 20% is the leading indicator of a wiki sprawl problem.

6. **"What is the regulatory overlay on this process — SOC 2, HIPAA, ISO 13485, GDPR, SOX, none?"**
   Recommended: explicit answer. If "none", confirm by checking the data classes the process touches.
   Canon: FDA 21 CFR Part 211.100 (Written procedures; deviations) — regulated SOPs require version control, change history, and signoff. Skip this step and the doc is an audit finding.

7. **"Is the happy path the *only* path documented, or are the 2-3 most common failure modes also documented?"**
   Recommended: the top-2 failure modes per process are documented with their own recovery sub-procedure.
   Canon: Fowler 2016 (*Production-Ready Microservices*) — operations docs that cover only the happy path are responsible for 60%+ of incident-time waste.

After all 7 are locked, invoke `kb_ingester.py` → `runbook_validator.py` → `sop_generator.py` in sequence.
