# Code-only mode

*Last updated: 2026-05-03 (v1.5.6 Phase 3 — initial publication).*

When the Quality Playbook runs against a target repo whose `reference_docs/` directory is absent or empty, it operates in **code-only mode**. This document explains what that means, why it matters, and how to upgrade a code-only run into a full-documentation run for the next pass.

## What "code-only mode" means

The playbook's normal Phase 1 derivation reads two kinds of evidence:

- **Code evidence (Tier 3+)** — the source tree itself, plus inline comments, defensive patterns, tests, and any inline documentation co-located with the code.
- **Documentation evidence (Tier 1/2)** — plaintext files the operator drops into `reference_docs/` (free-form notes, design docs, retrospectives, AI chats) and `reference_docs/cite/` (project specs, RFCs, API contracts that requirements should be traceable back to).

Code-only mode is the run state where no documentation evidence is available. The playbook proceeds — it does not abort — but every requirement it derives leans entirely on code evidence. The Phase 1 EXPLORATION.md gets a "Documentation status: code-only mode" opening section that surfaces the mode so reviewers see it on first read.

## What to expect from a code-only run

In our benchmark runs, code-only passes consistently produce:

- **Fewer requirements derived overall.** Without spec-language to anchor, Phase 1 has no Tier 1/2 evidence to cite, so the requirements set falls back to Tier 3 (code-as-spec) entirely.
- **Possibly fewer bugs found.** Code review (Phase 3) is most effective when the reviewer knows what the code is *supposed* to do — bugs that violate documented intent are easier to surface than bugs that hide behind ambiguous code-as-spec. With no documentation, the reviewer has to infer intent from the code itself, which leaves a class of intent-violation defects undetected.
- **Higher reliance on code-internal signals.** Defensive patterns (error checks, validation), test names, and comment-style annotations carry more weight in the absence of external docs.

The bug counts in code-only mode are still useful — they reflect what's discoverable from the code alone — but they are a lower bound on what a fully-documented run would produce.

## How to upgrade to a full-documentation run

Place plaintext documentation files in the target repo's `reference_docs/` tree before re-running Phase 1:

```
<target-repo>/
  reference_docs/
    project_notes.md         # Tier 4 — informal notes, AI chats
    design_overview.md       # Tier 3-4 — internal design decisions
    cite/
      api_spec.md            # Tier 1/2 — citable specs, RFCs, contracts
      protocol_v3.txt        # Tier 1/2 — formal specifications
```

Files at the top level of `reference_docs/` count as informal context (Tier 4). Files under `reference_docs/cite/` count as citable evidence (Tier 1 or 2 depending on the source's authority — see `schemas.md` §3.1). Both `.md` and `.txt` are recognized; other formats are ignored.

After dropping in documentation, re-run the playbook. Phase 1 will detect the populated `reference_docs/` and skip the code-only-mode downgrade. The new run's EXPLORATION.md, REQUIREMENTS.md, and BUGS.md will reflect the richer evidence base.

## Opt-out: `--require-docs`

Operators who want runs to abort instead of proceeding in code-only mode can pass `--require-docs` to `python3 -m bin.run_playbook` (v1.5.6+). When `--require-docs` is set and `reference_docs/` is empty at Phase 1 entry, the playbook:

1. Appends an `aborted_missing_docs` event to `quality/run_state.jsonl` (event type registered in `references/run_state_schema.md`).
2. Writes a clear `ERROR: aborted_missing_docs — reference_docs/ empty and --require-docs set` block to `quality/PROGRESS.md`.
3. Aborts before any LLM work (exit non-zero, same as a gate-fail).

The flag is off by default. Use it for compliance/policy contexts where a quiet code-only-mode downgrade would mask a real process gap (e.g., "every release run must cite a spec; no spec means the run shouldn't have started"). The flag is the opt-IN counterpart to `--no-formal-docs`'s opt-OUT (which suppresses the WARN banner for the same code-only-mode case but allows the run to continue).

## Cross-references

- **README** — Step 1 of "How to use the Quality Playbook" describes documentation as the first thing to provide.
- **`SKILL.md`** — Phase 1 prose describes how documentation evidence is used during exploration.
- **`bin/reference_docs_ingest.py`** — the implementation that ingests the `reference_docs/` tree.
- **`references/run_state_schema.md`** — defines the `documentation_state` event the playbook emits when code-only mode triggers, so the downgrade is searchable in audit trails.
