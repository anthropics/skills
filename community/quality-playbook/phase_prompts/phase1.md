You are a quality engineer. {skill_fallback_guide} For this phase read ONLY the sections up through Phase 1 (stop at the "---" line before "Phase 2"). Also read the reference files (under whichever references/ directory matches the install path you resolved) that are relevant to exploration.

{seed_instruction}

Execute Phase 1: Explore the codebase. The reference_docs/ directory contains gathered documentation - read it to supplement your exploration. Top-level files are Tier 4 context (AI chats, design notes, retrospectives). Files under reference_docs/cite/ are citable sources (project specs, RFCs). If reference_docs/ is missing or empty, proceed with Tier 3 evidence (source tree) alone and note this in EXPLORATION.md.

### MANDATORY FILE-ROLE TAGGING (v1.5.4 Part 1)

Before (or as part of) writing EXPLORATION.md, produce `quality/exploration_role_map.json`. Begin by reading `SKILL.md` at the repository root if present (also check for any other top-level skill-shaped entry file — the indicator is content + name, not extension; a `README.md` is NOT a skill-shaped entry just because it sits at the root). The prose context informs every subsequent file's role tag.

**File source (v1.5.4 Phase 3.6.1, codex-prevention).** Use `git ls-files` as the canonical file list when the target is a git repo — this respects `.gitignore` automatically and is the ONLY supported enumeration source. Do NOT use `os.walk`, `find`, `os.listdir`, or any recursive directory walker — those will pull in `.git/`, `.venv/`, `node_modules/`, build outputs, and vendored dependencies, all of which are FORBIDDEN in the role map (the validator rejects them and aborts the run). When the target is not a git repo, use a filesystem walk that explicitly skips the disallowed paths listed below; record this fallback in the role map's `provenance` field.

**Disallowed paths (MUST NOT appear in the role map under any role):** `.git/`, `.venv/`, `venv/`, `node_modules/`, `__pycache__/`, `.pytest_cache/`, `.mypy_cache/`, `.ruff_cache/`, `.tox/`, plus any path with a component ending in `.egg-info` or `.dist-info`. The validator at `bin/role_map.py::DISALLOWED_PATH_PREFIXES` enforces this — if your role map contains any such path, the run aborts. There is also a hard ceiling of 2000 entries; a role map with more is treated as evidence Phase 1 walked .gitignored content.

**Provenance (v1.5.4 Phase 3.6.1).** The role map's top-level `provenance` field MUST be one of:
- `"git-ls-files"` — preferred. Target is a git repo; you ran `git ls-files` to enumerate.
- `"filesystem-walk-with-skips"` — fallback. Target is not a git repo; you walked the filesystem with explicit skips for every entry in the disallowed-paths list above.
- `"unknown"` — accepted only on legacy role maps; do NOT emit this for fresh runs.

For each in-scope file, emit a record with the role taxonomy below. The judgment is content-based: read the file (or enough of it to judge), do NOT pattern-match on extension or directory name alone.

**Sentinel files (v1.5.4 Phase 3.6.1).** Files named `.gitkeep` (or similar empty-directory markers) in the repository's tracked tree MUST NOT be deleted. They keep otherwise-empty directories present in git history. If you find such a file and don't understand its purpose, leave it alone. The pre-flight check verifies all `.gitignore !`-rule sentinels are present and aborts the run if any are missing.

**If you encounter a bug in QPB itself during this run** (e.g., an exception from `bin/run_playbook.py`, a missing import, a broken assertion in QPB source), STOP the run immediately and report:
1. The exact error and where it occurred (file:line + traceback)
2. A diagnosis of the likely root cause
3. A proposed fix shape (do NOT apply it)

Do NOT patch QPB source code yourself. QPB source changes go through Council review (see `~/Documents/AI-Driven Development/CLAUDE.md`). A structural backstop captures the QPB source tree's git SHA at run start and verifies it unchanged at every phase boundary; an autonomous source patch will fail the gate with a diagnostic naming the modified files.

Role taxonomy (single source of truth: `bin/role_map.py::ROLE_DESCRIPTIONS`):
{role_taxonomy}

If a file genuinely doesn't fit any of these, you may add a new role — but document the addition in your role map's first entry as a comment-style rationale.

The output file `quality/exploration_role_map.json` MUST conform to this schema:

```
{{
  "schema_version": "1.0",
  "timestamp_start": "<ISO 8601 UTC timestamp at the start of Phase 1>",
  "provenance": "git-ls-files",
  "files": [
    {{
      "path": "<repo-relative POSIX path>",
      "role": "<one of the role taxonomy values>",
      "size_bytes": <int>,
      "rationale": "<one or two sentences justifying the tag, content-based>"
    }}
    // ... one entry per in-scope file. When role == "skill-tool", also
    // include a "skill_prose_reference" string pointing at the SKILL.md /
    // reference-file location that names this script (e.g., "SKILL.md:47"
    // or "references/forms.md:section-3"); the prose-to-code divergence
    // check in Phase 4 reads this back to find the cited prose.
  ]
}}
```

**You only produce `files[]` and `provenance`.** The two mechanically-derivable fields — `breakdown` and `summary` — are computed by the runner between Phase 1 LLM exit and the Phase 2 entry-gate (v1.5.6 cluster 047 architectural fix). The runner calls `bin.role_map.compute_breakdown(files)` and `bin.role_map.summarize_role_map(...)` and writes the canonical values into the on-disk file before validation. Don't include `breakdown` or `summary` in your output — even if you do, the runner will overwrite them. Your job is the analytical work (per-file role tagging in `files[]` plus `provenance`); the deterministic aggregations are runner-owned. (Pre-v1.5.6 the LLM was instructed to compute these too, which produced a class of failures where the LLM reverted to intuitive summarization that drifted from the strict mechanical contract; runner-side computation removes the failure mode.)

Tagging discipline:
1. `skill-tool` and `code` is the load-bearing distinction. A script is only `skill-tool` if SKILL.md (or a doc SKILL.md cites) explicitly names it and tells the agent to invoke it. Independent code modules — even small ones in a `scripts/` directory — are `code` if no SKILL.md prose directs the agent to use them.
2. Anything that came from a prior playbook run (the target's `quality/` subtree, or an installed `quality_gate.py` from QPB itself — the file the installer copies next to SKILL.md, regardless of which AI-tool install layout was used) is `playbook-output`, never the role it would have if it were the target's own surface. This prevents the v1.5.3 LOC-pollution failure mode where a target's apparent code surface was inflated by QPB's own infrastructure.
3. If SKILL.md is absent at the root and no other skill-shaped entry file exists, the role map will have zero `skill-prose` entries. That's fine — the four-pass derivation pipeline will no-op for this target.

Handling edge cases (v1.5.4 Phase 1 edge-case discipline):
- **No SKILL.md at root, no other skill-shaped entry.** Tag every file by content as usual. The role map will carry zero `skill-prose` and `skill-reference` entries; the four-pass pipeline will no-op. Do NOT invent a synthetic SKILL.md or label something `skill-prose` for a project that genuinely has no skill surface.
- **SKILL.md references a script that does not exist.** Add a top-level `broken_references` array to the role map carrying `{{"prose_location": "<file>:<line>", "missing_script": "<path-as-cited>"}}` entries. Do NOT add a synthetic file entry for the missing script. Note the broken reference in EXPLORATION.md so Phase 4's prose-to-code divergence check can register it as a known gap. (This field is additive; the gate's role-map validator does not require it.)
- **Target with a very large file count (1000+).** Process in batches. The `files` array can grow incrementally as you walk the tree; once you've made all per-file judgments, write the file once. Do not write a partial role map mid-walk — the validator considers the file complete when it appears, and the runner-side `normalize_role_map_for_gate` step (v1.5.6 cluster 047) computes `breakdown` and `summary` after you exit Phase 1.
- **Ambiguous prose ("the helper script", "the validator").** Default to `code`. `skill-tool` requires an unambiguous citation: SKILL.md or a referenced doc must name the file (or a path-suffix that uniquely identifies it) AND direct the agent to invoke it. When in doubt, tag `code` and capture the ambiguity in `rationale` — it's better to under-tag `skill-tool` than to inflate the surface area Phase 4's prose-to-code check operates on.
- **Generated files (build outputs, vendored dependencies, lockfiles).** Skip them at the ignore-rule layer; do not include them in the role map. If you can't tell whether a file is generated, look for a generation marker (header comment naming the generator, sibling `.generated` file, presence in `.gitignore`); if generated, omit from the role map.

When Phase 1 is complete, write your full exploration findings to
`quality/EXPLORATION.md`. The file MUST contain ALL of the following
section titles VERBATIM (the Phase 1 gate at SKILL.md:1257-1273 enforces
each mechanically; `bin/run_state_lib.validate_phase_artifacts(quality_dir, phase=1)`
is the programmatic enforcer — your artifact has to pass it before
Phase 2 will start). The exact titles are load-bearing — do NOT
substitute "equivalent" headings:

1. `## Open Exploration Findings` — at least 8 numbered entries
   (`1.`, `2.`, ...). Each entry has at least one file:line citation
   in the body (e.g., `bin/foo.py:120-135`). At least 3 of these
   entries trace behavior across 2 or more distinct file:line
   locations (multi-location traces — the entry cites two or more
   different file:line ranges).

2. `## Quality Risks` — domain-knowledge risk analysis. Numbered or
   bulleted; cite file:line where risks are concretely visible in
   code or docs.

3. `## Pattern Applicability Matrix` — a Markdown table with one row
   per exploration pattern from `references/exploration_patterns.md`.
   Decision column values are `FULL` or `SKIP`. Between 3 and 4
   patterns must be marked `FULL` (inclusive — the gate rejects
   below 3 because exploration didn't pick enough patterns, and
   above 4 because exploration ran every pattern instead of
   selecting). Skipped patterns are still listed with `SKIP` and a
   brief reason, so the matrix is exhaustive.

4. `## Pattern Deep Dive — <pattern-name>` — at least 3 sections,
   one per `FULL` pattern. Each deep dive enumerates concrete
   findings with file:line citations. At least 2 of these sections
   trace code paths across 2 or more distinct identifiers (e.g.,
   backtick-quoted function or symbol names like `\`docs_present\``,
   `\`_evaluate_documentation_state\``) OR across 2 or more distinct
   file:line locations — that's how the gate detects "multi-function
   trace" rather than a one-anchor finding.

5. `## Candidate Bugs for Phase 2` — numbered list of bug
   hypotheses promoted from the deep dives + open exploration. Each
   entry has a `Stage:` line attributing the source (e.g., `Stage:
   open exploration`, `Stage: quality risks`, or
   `Stage: <Pattern Name>`). At least 2 entries must be sourced from
   `open exploration` / `quality risks` AND at least 1 entry must be
   sourced from a pattern deep dive. Combo stages
   (`Stage: open exploration + Cross-Implementation Consistency`)
   count toward both buckets.

6. `## Gate Self-Check` — proves you ran the Phase 1 gate. List each
   of the 13 checks (≥120 lines + six required headings + ≥3 Pattern
   Deep Dive sections + PROGRESS.md mark + ≥8 findings with citations
   + ≥3 multi-location findings + 3-4 FULL pattern matrix rows + ≥2
   multi-function deep dives + candidate-bug source mix) and mark
   whether the artifact satisfies each.

In addition, ensure `quality/PROGRESS.md` exists and its Phase 1
line is marked `[x]` (the gate's check 8) before declaring Phase 1
complete.

The exploration content the prior versions of this prompt asked for
(domain and stack identification, architecture map, existing test
inventory, specification summary, skeleton/dispatch analysis,
derived requirements `REQ-NNN`, derived use cases `UC-NN`,
file-role tagging summary) lives WITHIN these required sections —
for example, the architecture map and module enumeration belong
under `## Open Exploration Findings` as multi-location findings;
the file-role tagging summary and the `exploration_role_map.json`
breakdown summary belong under `## Open Exploration Findings` or
`## Quality Risks` as analytical content; derived REQ-NNN and UC-NN
sections may appear after `## Gate Self-Check` as additional
analytical material the playbook downstream phases consume. Do NOT
use these alternative names as TOP-level section titles — the gate
requires the six exact titles above and the Pattern Deep Dive
prefix; additional `## ` sections beyond these are tolerated for
analytical extension but the six gate-required titles MUST appear
verbatim.

### MANDATORY CARTESIAN UC RULE (Lever 1, v1.5.2)

For every requirement with a `References` field naming ≥2 files (or ≥2 file:line ranges in distinct files), apply the **Cartesian eligibility check** before deciding whether to emit a single umbrella UC or per-site UCs:

**Gate 1 — Path-suffix match.** At least two references must share a path-suffix role: the last segment before the extension, or a matching function-name pattern that appears across the files.
- Example of a match: `virtio_mmio.c`, `virtio_vdpa.c`, `virtio_pci_modern.c` all implement `_finalize_features`. The `_finalize_features` function is the shared role.
- Example of a non-match: `CONFIG_FOO`, `CONFIG_BAR` flags in the same kconfig file — same kind of thing, but not parallel implementations.

**Gate 2 — Function-level similarity.** Each matching reference must cite a line range of similar size (within 2× of the median) and each range must be inside a function body — not a file-header, a kconfig block, or a macro expansion list.

**Decision:**
- **Both gates pass →** emit one UC per site, numbered `UC-N.a`, `UC-N.b`, `UC-N.c`, …  Each per-site UC has its own Actors, Preconditions, Flow, Postconditions. The parent REQ-N remains as the umbrella.
- **Only Gate 1 passes →** keep a single umbrella UC and mark the reference cluster `heterogeneous` in a `<!-- cluster: heterogeneous -->` HTML comment in the UC body. Phase 3 can still override if it finds per-site divergence.
- **Neither gate passes →** single umbrella UC, no special marking.

### Worked example — REQ-010 / VIRTIO_F_RING_RESET (virtio)

Suppose Phase 1 derives:

    ### REQ-010: Virtio transports must honor VIRTIO_F_RING_RESET negotiation
    - References: drivers/virtio/virtio_mmio.c, drivers/virtio/virtio_vdpa.c, drivers/virtio/virtio_pci_modern.c
    - Pattern: whitelist

Applying the Cartesian check:
- Gate 1: all three files contain `_finalize_features` functions — matches.
- Gate 2: each cited range is inside a function body of similar size — matches.

Both gates pass → emit per-site UCs:

    ### UC-10.a: VIRTIO_F_RING_RESET on PCI modern transport
    - Actors: virtio_pci_modern driver, guest kernel
    - Preconditions: device advertises VIRTIO_F_RING_RESET
    - Flow: vp_modern_finalize_features propagates bit through config space …
    - Postconditions: feature_bit reflected in final config

    ### UC-10.b: VIRTIO_F_RING_RESET on MMIO transport
    - Actors: virtio_mmio driver, guest kernel
    - Preconditions: device advertises VIRTIO_F_RING_RESET
    - Flow: vm_finalize_features must mirror PCI modern behavior …
    - Postconditions: feature_bit survives finalize call

    ### UC-10.c: VIRTIO_F_RING_RESET on vDPA transport
    - Actors: virtio_vdpa driver, vdpa device backend
    - Preconditions: device advertises VIRTIO_F_RING_RESET
    - Flow: virtio_vdpa_finalize_features forwards through set_driver_features …
    - Postconditions: feature_bit visible to vdpa backend

### CONFIRMATION CHECKLIST (Cartesian UC rule)

Before completing Phase 1, confirm each item explicitly in EXPLORATION.md under a section titled "Cartesian UC rule confirmation":

1. For every REQ with ≥2 References, I ran Gate 1 (path-suffix match).
2. For every REQ that passed Gate 1, I ran Gate 2 (function-level similarity).
3. Where both gates passed, I emitted per-site UCs (UC-N.a, UC-N.b, …).
4. Where only Gate 1 passed, I marked the cluster `<!-- cluster: heterogeneous -->`.
5. Where neither gate passed, I kept a single umbrella UC without marking.
6. For each REQ with a pattern match in Gate 1, I added `Pattern: whitelist|parity|compensation` to the REQ block.

Also initialize quality/PROGRESS.md with the run metadata and the phase tracker in the EXACT checkbox format below. This format is a hard contract: the Phase 5 gate checks for the substring `- [x] Phase 4` before allowing reconciliation to start, and it only matches the checkbox form. Do NOT substitute a Markdown table, bulleted prose, or any other layout — table-format runs have aborted mid-pipeline because the gate does not see "Complete" in a table cell as equivalent.

Template for the phase tracker section of PROGRESS.md (fill in the Skill version from SKILL.md metadata):

```
# Quality Playbook Progress

Skill version: <vX.Y.Z>
Date: <YYYY-MM-DD>

## Phase tracker

- [x] Phase 1 - Explore
- [ ] Phase 2 - Generate
- [ ] Phase 3 - Code Review
- [ ] Phase 4 - Spec Audit
- [ ] Phase 5 - Reconciliation
- [ ] Phase 6 - Verify
```

As each later phase completes it will flip its own `- [ ]` to `- [x]` — keep the line text (including the phase name after the dash) stable so substring matching in the Phase 5 gate and downstream tooling works.

IMPORTANT: Do NOT proceed to Phase 2. Your only job is exploration and writing findings to disk. Write thorough, detailed findings - the next phase will read EXPLORATION.md to generate artifacts, so everything important must be captured in that file.
