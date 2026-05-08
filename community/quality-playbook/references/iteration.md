# Iteration Mode Reference

> This file contains the detailed instructions for each iteration strategy.
> The agent reads this file when running an iteration — all operational detail lives here,
> not in the prompt or in the benchmark runner.

## Iteration cycle

The recommended iteration order is: **gap → unfiltered → parity → adversarial**. Each strategy finds different bug classes, and running them in this order maximizes cumulative yield. After each iteration, the skill prints a suggested prompt for the next strategy — follow the cycle until you hit diminishing returns or decide to stop.

```
Baseline run                                          # structured three-stage exploration
→ gap         scan previous coverage, explore gaps    # finds bugs in uncovered subsystems
→ unfiltered  pure domain-driven, no structure        # finds bugs that structure suppresses
→ parity      cross-path comparison and diffing       # finds inconsistencies between parallel implementations
→ adversarial challenge dismissed/demoted findings    # recovers Type II errors from previous triage
```

## Shared rules for all strategies

These rules apply to every iteration strategy:

1. **ITER file naming.** Write findings to `quality/EXPLORATION_ITER{N}.md` — check which iteration files already exist and use the next number (e.g., `EXPLORATION_ITER2.md` for the first iteration, `EXPLORATION_ITER3.md` for the second).

2. **Do NOT delete or archive quality/.** You are building on the existing run, not replacing it.

3. **Context budget discipline.** A first-run EXPLORATION.md can be 200–400 lines. Loading it all into context before starting your own exploration leaves too little room for deep investigation. The previous-run scan should consume ~20–30 lines of context. Targeted deep-reads should consume ~40–60 lines total. This leaves the bulk of your context budget for new exploration.

4. **Merge.** After completing the strategy-specific exploration, create or update `quality/EXPLORATION_MERGED.md` that combines findings from ALL iterations. For each section, concatenate the findings with clear attribution (`[Iteration 1]` / `[Iteration 2: gap]` / `[Iteration 3: unfiltered]` / etc.). Include the strategy name in the attribution so downstream phases can see which approach surfaced each finding. The Candidate Bugs section should be re-consolidated from all findings across all iterations. If `EXPLORATION_MERGED.md` already exists from a previous iteration, merge the new iteration's findings into it rather than starting from scratch.

   **Demoted Candidates Manifest (mandatory in EXPLORATION_MERGED.md).** After re-consolidating the Candidate Bugs section, add or update a `## Demoted Candidates` section at the end of EXPLORATION_MERGED.md. This section tracks findings that were dismissed, demoted, or deprioritized during any iteration — they are the raw material for the adversarial strategy. For each demoted candidate, record:

   ```
   ### DC-NNN: [short title]
   - **Source:** [which iteration and strategy first surfaced this]
   - **Dismissal reason:** [why it was demoted — e.g., "classified as design choice," "insufficient evidence," "needs runtime confirmation"]
   - **Code location:** [file:line references]
   - **Re-promotion criteria:** [specific evidence that would flip this to a confirmed candidate — e.g., "show that the permissive behavior violates a documented contract," "trace the code path to prove the edge case is reachable," "demonstrate that the output differs from what the spec requires"]
   - **Status:** DEMOTED | RE-PROMOTED [iteration] | FALSE POSITIVE [iteration]
   ```

   The re-promotion criteria are the most important field — they tell the adversarial strategy exactly what evidence to gather. Vague criteria like "needs more investigation" are not acceptable; write criteria that a different agent session could act on without additional context. If a subsequent iteration re-promotes or definitively falsifies a demoted candidate, update its status and add a note explaining the resolution.

5. **Continue with Phases 2–6.** Use `EXPLORATION_MERGED.md` as the primary input for Phase 2 artifact generation. All downstream artifacts (REQUIREMENTS.md, code review, spec audit) should reference the merged exploration.

   **TDD is mandatory for iteration runs (v1.3.49).** Iteration runs must execute the full TDD red-green cycle for every newly confirmed bug, exactly as baseline runs do. This means: for each new BUG-NNN confirmed in this iteration, create a regression test patch, run it against unpatched code to produce `quality/results/BUG-NNN.red.log`, and if a fix patch exists, run it against patched code to produce `quality/results/BUG-NNN.green.log`. The TDD Log Closure Gate in Phase 5 applies equally to iteration runs — missing log files will cause quality_gate.sh to FAIL. Do not skip TDD because this is "just an iteration" or because prior bugs already have logs. New bugs need new logs. If the test runner is not available for the project's language, create the log file with `NOT_RUN` on the first line and an explanation — the file must still exist.

6. **Iteration mode completion gate.** Before proceeding to Phase 2 (applies to all strategies):
   - `quality/ITERATION_PLAN.md` exists and names the strategy used
   - `quality/EXPLORATION_ITER{N}.md` exists for this iteration with at least 80 lines of substantive content
   - `quality/EXPLORATION_MERGED.md` exists and contains findings from all iterations
   - The merged Candidate Bugs section has at least 2 new candidates not present in previous iterations
   - At least 1 finding covers a code area not explored in previous iterations OR re-confirms a previously dismissed finding with fresh evidence

7. **Suggested next iteration.** At the end of Phase 6, after writing the final PROGRESS.md summary, print a suggested prompt for the next iteration strategy in the cycle. If the current strategy was:
   - **gap** → suggest: `Run the next iteration of the quality playbook using the unfiltered strategy.`
   - **unfiltered** → suggest: `Run the next iteration of the quality playbook using the parity strategy.`
   - **parity** → suggest: `Run the next iteration of the quality playbook using the adversarial strategy.`
   - **adversarial** → suggest: `Run the quality playbook from scratch.` (cycle complete)
   - **baseline (no strategy)** → suggest: `Run the next iteration of the quality playbook using the gap strategy.`

   Format the suggestion clearly so the user can copy-paste it:
   ```
   ────────────────────────────────────────────────────────
   Next iteration suggestion:
   "Run the next iteration of the quality playbook using the [strategy] strategy."
   ────────────────────────────────────────────────────────
   ```

## Meta-strategy: `all` — run every strategy in sequence

The `all` strategy is a runner-level convenience that executes gap → unfiltered → parity → adversarial in order, each as a separate agent session. A single agent session cannot run multiple strategies (context budget), so `all` is implemented by the orchestrator agent or benchmark runner as a loop of iteration calls. If any strategy finds zero new bugs, stop early (diminishing returns).

Usage (orchestrator agent): "Run all iterations" — the agent runs gap → unfiltered → parity → adversarial sequentially.
Usage (benchmark runner): `python3 bin/run_playbook.py --next-iteration --strategy all <targets>` (benchmark tooling, not shipped with the skill). `--strategy` also accepts a comma-separated ordered subset, e.g. `--strategy unfiltered,parity,adversarial`.

---

## Strategy: `gap` (default) — find what the previous run missed

Scan the previous run's coverage and deliberately explore elsewhere. Best when the first run was structurally sound but only covered a subset of the codebase.

1. **Coverage scan (lightweight).** Read the previous `quality/EXPLORATION.md` using a divide-and-conquer strategy — do NOT load the entire file into context at once. Instead:
   - Read just the section headers and first 2–3 lines of each section to build a coverage map
   - For each section, record: section name, subsystems covered, number of findings, depth level (shallow = single-function mentions, deep = multi-function traces)
   - Write the coverage map to `quality/ITERATION_PLAN.md`

2. **Gap identification.** From the coverage map, identify:
   - Subsystems or modules that were not explored at all
   - Sections with shallow findings (few lines, single-function mentions, no code-path traces)
   - Quality Risks scenarios that were listed but never traced to specific code
   - Pattern deep dives that could apply but weren't selected (from the applicability matrix)
   - Domain-knowledge questions from Step 6 that weren't addressed

3. **Targeted deep-read.** For only the 2–3 thinnest or most gap-rich sections, read the full section content from the previous EXPLORATION.md. This gives you specific context about what was already found without consuming your entire context budget on previous findings.

4. **Gap exploration.** Run a focused Phase 1 exploration targeting only the identified gaps. Use the same three-stage approach (open exploration → quality risks → selected patterns) but scoped to the uncovered areas. Write findings to `quality/EXPLORATION_ITER{N}.md` using the same template structure.

---

## Strategy: `unfiltered` — pure domain-driven exploration without structural constraints

Ignore the three-stage gated structure entirely. Explore the codebase the way an experienced developer would — reading code, following hunches, tracing suspicious paths — with no pattern templates, applicability matrices, or section format requirements. This strategy deliberately removes the structural scaffolding to let domain expertise drive discovery without constraint.

**Why this strategy exists:** In benchmarking, the unfiltered domain-driven approach used in skill versions v1.3.25–v1.3.26 found bugs that the structured three-stage approach consistently missed, particularly in web frameworks and HTTP libraries. The structured approach excels at systematic coverage but can over-constrain exploration, causing the model to spend context on format compliance rather than deep code reading. The unfiltered strategy recovers that lost discovery power.

1. **Lightweight previous-run scan.** Read just the `## Candidate Bugs for Phase 2` section and `quality/BUGS.md` from the previous run to know what was already found. Do NOT read the full EXPLORATION.md — you want a fresh perspective, not to be anchored by previous exploration paths. Write a brief note to `quality/ITERATION_PLAN.md` listing what the previous run found and confirming you are using the unfiltered strategy.

2. **Unfiltered exploration.** Explore the codebase from scratch using pure domain knowledge. No required sections, no pattern applicability matrix, no gate self-check. Instead:
   - Read source code deeply — entry points, hot paths, error handling, edge cases
   - Follow your domain expertise: "What would an expert in [this domain] find suspicious?"
   - For each suspicious finding, trace the code path across 2+ functions with file:line citations
   - Generate bug hypotheses directly — not "areas to investigate" but "this specific code at file:line produces wrong behavior because [reason]"
   - Write findings to `quality/EXPLORATION_ITER{N}.md` as a flat list of findings, each with file:line references and a bug hypothesis. No structural template required — depth and specificity matter, not section formatting.
   - Minimum: 10 concrete findings with file:line references, at least 5 of which trace code paths across 2+ functions

3. **Domain-knowledge questions.** Complete these questions using the code you just explored AND your domain knowledge. Write your answers inline with your findings, not in a separate gated section:
   - What API surface inconsistencies exist between similar methods?
   - Where does the code do ad-hoc string parsing of structured formats?
   - What inputs would a domain expert try that a developer might not test?
   - What metadata or configuration values could be silently wrong?

---

## Strategy: `parity` — cross-path comparison and diffing

Systematically enumerate parallel implementations of the same contract and diff them for inconsistencies. This strategy finds bugs by comparing code paths that should behave the same way but don't.

**Why this strategy exists:** In benchmarking, the v1.3.40 skill version found 5 bugs in virtio using "fallback path parity" and "cross-implementation consistency" as explicit exploration patterns. Three of those bugs (MSI-X slow_virtqueues reattach, GFP_KERNEL under spinlock, INTx admin queue_idx) were found by lining up parallel code paths and spotting differences — not by exploring individual subsystems. The gap, unfiltered, and adversarial strategies all explore areas or challenge decisions, but none explicitly compare parallel paths. This strategy fills that gap.

1. **Enumerate parallel paths.** Scan the codebase for groups of code that implement the same contract or handle the same logical operation via different paths. Common categories:
   - **Transport/backend variants:** multiple implementations of the same interface (e.g., PCI vs MMIO vs vDPA, sync vs async, HTTP/1.1 vs HTTP/2)
   - **Fallback chains:** primary path → fallback → last-resort (e.g., MSI-X → shared → INTx, rich error → generic error)
   - **Setup vs teardown/reset:** initialization path vs cleanup/reset path for the same resource
   - **Happy path vs error path:** normal flow vs exception/error handling for the same operation
   - **Public API variants:** overloaded methods, convenience wrappers, format-specific parsers that should produce equivalent results
   - Write the enumeration to `quality/ITERATION_PLAN.md` with a brief description of each parallel group.

2. **Pairwise comparison.** For each parallel group, read the code paths side by side and systematically check each comparison sub-type below. Not every sub-type applies to every parallel group — but explicitly considering each one prevents the strategy from only finding "obvious" discrepancies while missing structural ones.

   **Comparison sub-type checklist** (check each one for every parallel group):

   - **Resource lifecycle parity:** Compare what setup/init does with a resource vs. what teardown/reset/cleanup does with the same resource. Every resource acquired in setup must be released in teardown — and in the same order, with the same scope. Look for resources that setup creates but reset forgets (e.g., a list populated during probe but not drained during reset).
   - **Allocation context parity:** Compare allocation flags, lock context, and interrupt state across parallel paths. If one path allocates with `GFP_KERNEL` (sleepable) but runs under a spinlock that another path doesn't hold, that's a bug. Check: what locks are held? What allocation flags are valid in that context? Do parallel paths agree?
   - **Identifier and index parity:** Compare how parallel paths compute indices, offsets, or identifiers for the same logical entity. If setup uses `queue_index + admin_offset` but reset uses `raw_queue_index`, the mismatch is a bug candidate.
   - **Capability/feature-bit parity:** Compare which feature bits, flags, or capabilities each parallel path checks or sets. If the MSI-X path checks a slow-path vector list but the INTx fallback path doesn't, vectors may be misrouted after fallback.
   - **Error/exception parity:** Compare error handling between paths. If the primary path handles an error gracefully but the fallback path lets it propagate, the fallback is less robust than the primary — which is backwards.
   - **Iteration/collection parity:** Compare what collections each path iterates over. If setup iterates over `all_queues` but reset iterates over `active_queues`, resources for inactive queues leak.

   For each discrepancy found, trace both code paths with file:line citations and determine whether the difference is intentional (documented, tested, or structurally necessary) or a bug.

3. **Cross-file contract tracing.** For the most promising discrepancies, trace the call chain across files to verify:
   - What lock/interrupt context each path runs in
   - What allocation flags are valid in that context
   - Whether the contract (documented in specs, comments, or headers) requires parity
   - Write findings to `quality/EXPLORATION_ITER{N}.md` with both code paths cited for each finding.

4. **Minimum output:** At least 5 parallel groups enumerated, at least 8 pairwise comparisons traced with file:line references, at least 3 concrete discrepancy findings.

---

## Strategy: `adversarial` — challenge the previous run's conclusions

Re-investigate what the previous run dismissed, demoted, or marked SATISFIED. This strategy assumes the previous run made Type II errors (missed real bugs by being too conservative) and systematically challenges those decisions.

**Why this strategy exists:** In benchmarking, the triage step reliably demotes legitimate findings by demanding excessive evidence, marking ambiguous cases as "design choice," or accepting code-review SATISFIED verdicts without deep verification. The adversarial strategy specifically targets these failure modes.

1. **Load previous decisions.** Read these files from the previous run (use divide-and-conquer — section headers first, then targeted deep reads):
   - `quality/EXPLORATION_MERGED.md` — specifically the `## Demoted Candidates` section (this is your primary input — it contains structured re-promotion criteria for each dismissed finding)
   - `quality/BUGS.md` — what was confirmed (to avoid re-finding the same bugs)
   - `quality/spec_audits/*triage*` — what was dismissed or demoted during triage, and why
   - `quality/code_reviews/*.md` — Pass 2 SATISFIED/VIOLATED verdicts
   - `quality/EXPLORATION.md` — just the `## Candidate Bugs for Phase 2` section to see which candidates didn't become confirmed bugs
   - Write a summary to `quality/ITERATION_PLAN.md` listing: (a) demoted candidates from the manifest with their re-promotion criteria, (b) additional dismissed triage findings not yet in the manifest, (c) candidates that weren't promoted, (d) requirements marked SATISFIED that had thin evidence

2. **Re-investigate dismissed findings with a lower evidentiary bar.** The adversarial strategy uses a deliberately lower evidentiary standard than earlier strategies. The baseline and gap strategies rightly demand strong evidence to avoid false positives during initial discovery. But by the adversarial iteration, remaining undiscovered bugs are precisely the ones that conservative triage keeps rejecting — they look ambiguous, they could be "design choices," they lack dramatic runtime failures. For these findings:
   - A code-path trace showing observable semantic drift (output differs from what spec or contract requires) is sufficient to confirm — you do not need a runtime crash or dramatic failure
   - "Permissive behavior" is not automatically a design choice — check whether the spec, docs, or API contract defines the expected behavior. If the code deviates from a documented contract, it's a bug regardless of whether the deviation is "permissive"
   - If the Demoted Candidates Manifest includes re-promotion criteria, attempt to satisfy those criteria specifically. Each criterion was written to be actionable — follow it
   - Read the specific code location cited in the finding
   - Trace the code path independently — do not rely on the previous run's analysis
   - Make an explicit CONFIRMED/FALSE-POSITIVE determination with fresh evidence
   - Update the Demoted Candidates Manifest: change status to RE-PROMOTED or FALSE POSITIVE with the iteration attribution

3. **Challenge SATISFIED verdicts.** For each requirement the code review marked SATISFIED with thin evidence (single-line citation, no code-path trace, or grouped with 3+ other requirements under one citation):
   - Re-verify the requirement by reading the cited code and tracing the behavior
   - Check whether the requirement is actually satisfied or whether the review took a shallow pass

4. **Explore adjacent code.** For each re-confirmed or newly confirmed finding, explore the surrounding code for related bugs — bugs cluster. If a function has one bug, its callers and siblings likely have related issues.

5. Write all findings to `quality/EXPLORATION_ITER{N}.md`. Each finding must include: the original source (triage dismissal, candidate demotion, or SATISFIED challenge), the fresh evidence, and the new determination.
