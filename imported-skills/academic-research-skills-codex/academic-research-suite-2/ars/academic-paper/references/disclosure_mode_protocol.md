# Disclosure Mode Protocol

**Status**: v3.2 (#108 extension: parallel `--policy-anchor=<a>` path; v3.2 venue path unchanged)
**Parent skill**: `academic-paper`
**Mode name**: `disclosure`
**Purpose**: Generate either (a) a venue-specific AI-usage disclosure statement that complies with the target venue's current AI policy (v3.2 path, default), or (b) a policy-anchor-specific disclosure rendered from the 4-anchor matrix (PRISMA-trAIce / ICMJE / Nature / IEEE) when the author targets a policy anchor rather than a specific journal venue (#108 path).

---

## Two parallel tracks (#108 + v3.2)

The `disclosure` mode dispatches on the author-supplied selector:

| Selector | Track | Lookup source | Output shape |
|---|---|---|---|
| `--venue=<v>` (v3.2, default) | Venue track | `venue_disclosure_policies.md` v1 database (ICLR / NeurIPS / Nature / Science / ACL / EMNLP) | Single venue-tailored disclosure paragraph + placement instruction |
| `--policy-anchor=<a>` (#108) | Anchor track | `policy_anchor_table.md` 4-anchor × 16-field matrix | 4-anchor-conditioned render per `policy_anchor_disclosure_protocol.md` |

The two tracks are **selector-mutually-exclusive by default** — one selector picks one track. When the author supplies **both** selectors in the same invocation, the renderer evaluates compatibility per concern #7 rules: a consistent pair (Nature venue + nature anchor, both sourced from `shared/policy_data/nature_policy.md`) proceeds; any other pair is **rejected with an explicit error** listing the policy conflict. Silent precedence between selectors is forbidden. See [policy_anchor_disclosure_protocol.md §5](policy_anchor_disclosure_protocol.md) for the full conflict-resolution detail.

If neither selector is supplied and the pipeline orchestrator does not infer one from upstream context, the mode prompts the user to specify which selector applies. The venue track remains the default for explicit journal submissions; the anchor track applies when targeting policy frameworks (e.g., compliance reporting to ICMJE-adopting journals collectively, or pre-submission alignment to IEEE author guidelines).

**Conflict resolution (concern #7) — exhaustive cases:**
- Supplied both, **consistent pair** (only currently defined case): `--venue=Nature` (any Nature Portfolio variant string) **and** `--policy-anchor=nature` → both target Nature substantive policy via the shared source pointer → **proceed**.
- Supplied both, **any other combination** (e.g., `--venue=Nature` + `--policy-anchor=ieee`; `--venue=ICLR` + `--policy-anchor=icmje`; or a Nature-venue spelling that does not match the canonical set with a non-nature anchor) → **reject** with explicit error citing the policy conflict; require the user to drop one selector. Silent precedence is forbidden by §4.4 #7.
- Supplied only one selector → run that track.
- Supplied neither selector → prompt the user to specify.

---

## Why this mode exists

`academic-paper` already ships two generic AI disclosure templates in `journal_submission_guide.md` ("Minimal Disclosure" and "Detailed Disclosure"). Those templates are a good starting point but they are venue-agnostic: they don't know that Nature requires disclosure in the Methods section specifically, that ICLR requires it in the paper body with acknowledgement that "LLMs were used as general-purpose writing tools", or that ACL requires the disclosure in the Acknowledgements section.

The v3.2 venue track closes the venue-specific gap. The #108 anchor track closes the policy-framework-specific gap that emerges when authors target a policy anchor (PRISMA-trAIce SLR guideline, ICMJE recommendations, Nature Portfolio editorial policy, IEEE author guidelines) rather than a specific journal venue.

---

## Inputs

1. **Paper draft**: current manuscript text (the mode needs to know what the AI actually did in order to describe it accurately).

2. **Selector** (one of):
   - **Target venue (`--venue=<v>`)**: journal or conference name (v3.2 path). If the venue is in the v1 database (ICLR, NeurIPS, Nature, Science, ACL, EMNLP), use the cached policy. If not, refuse to guess — prompt the user to paste the venue's current AI policy text from the venue's submission page.
   - **Policy anchor (`--policy-anchor=<a>`)**: one of `prisma-trAIce, icmje, nature, ieee` (#108 path). Anchor lookup follows `policy_anchor_disclosure_protocol.md`.

3. **Pipeline signal** (#108 anchor path only): `slr_lineage=true|false` set by the upstream pipeline orchestrator. Required for `--policy-anchor=prisma-trAIce` per §4.3 G2 invariant. Cold-start invocation requires explicit `mode=<value>` parameter; silent fallback to general track is forbidden.

4. **What ARS did**: the mode reads the paper's commit history / pipeline log (if using the full `academic-pipeline`) to identify which AI-assisted steps produced which parts of the paper. At minimum: research assistance, drafting assistance, revision assistance, citation checking, peer review simulation. If the pipeline log is not available, ask the user to confirm which categories apply.

---

## Process

### Phase 1: Intake + lookup (selector-aware)

**Step 1a — selector dispatch:**
- Both `--venue=<v>` and `--policy-anchor=<a>` supplied → check policy compatibility per the Two-parallel-tracks section above. **Consistent pair (currently only any Nature Portfolio venue + `--policy-anchor=nature`, where "Nature Portfolio venue" includes canonical labels {"Nature", "Nature Portfolio", "Nature (Nature Publishing Group)", "Nature Publishing Group"} and the journal-family prefix `"Nature "` matching e.g. "Nature Medicine", "Nature Communications", "Nature Climate Change", etc.) → route the consistent pair to **step 1c (anchor path)** so the shared canonical source `shared/policy_data/nature_policy.md` drives rendering; step 1b's v1 venue database does not need to contain every Nature Portfolio journal**. Conflicting pair → reject with explicit error.
- `--venue=<v>` only → step 1b (venue path).
- `--policy-anchor=<a>` only → step 1c (anchor path).
- Neither supplied → prompt the user to specify selector.

**Step 1b — venue lookup (v3.2 path, unchanged):**
- If venue is in the v1 database → load policy from `venue_disclosure_policies.md`.
- If venue is unknown → halt. Print: "I do not have a cached policy for {venue}. Please paste the venue's current AI-usage / generative-AI policy text so I don't guess." Do NOT fabricate a policy.
- If the user pastes a policy for an unknown venue, use it for this session only. Do NOT auto-persist it to the database — policies drift, and the database needs curation.

**Step 1c — anchor lookup (#108 path):**
- Validate `--policy-anchor=<a>` ∈ `{prisma-trAIce, icmje, nature, ieee}`. Other values → reject with the closed-enum error.
- For `--policy-anchor=prisma-trAIce`: confirm `slr_lineage=true` (pipeline signal) or `mode=systematic-review` (cold-start input) per the G2 invariant track gate. Otherwise refuse with G2 invariant citation.
- Delegate Phase 3 + Phase 4 to `policy_anchor_disclosure_protocol.md` per-anchor render flows. Phase 2 (AI usage categorization) and Phase 5 (placement instructions) are shared with the venue path with the anchor-specific routing applied inside Phase 3/4.

### Phase 2: Categorize AI usage

Produce a categorized list of how AI was used in the manuscript:

| Category | Examples |
|---|---|
| Research assistance | Literature search, annotated bibliography, claim verification |
| Drafting assistance | Section drafting, paraphrasing, outline generation |
| Revision assistance | Reviewer response drafting, tracked changes, consistency checking |
| Editing assistance | Grammar, style, formatting, citation format conversion |
| Analysis assistance | Not applicable to pure writing flows; flag if the paper reports any analysis the AI did |
| Peer review simulation | `academic-paper-reviewer` was used on the draft pre-submission |

For each category, mark: USED / NOT USED / UNCERTAIN. UNCERTAIN items require user confirmation before the disclosure text is finalized.

### Phase 3: Match categories to the venue's required phrasing

Each venue in the policy database specifies (a) which categories are mandatory to disclose, (b) which are optional, (c) which are prohibited (e.g., analysis assistance may require separate disclosure at some venues). The mode matches the user's category list against the venue's requirements and flags any mismatch (e.g., "Venue requires disclosure of research assistance; your categorization marked it UNCERTAIN").

### Phase 4: Generate the disclosure text

Generate a single disclosure paragraph using:
- The venue's preferred voice (first person vs passive, past tense vs present)
- The venue's required phrasing elements (many venues require the phrase "The authors take full responsibility for the content" or equivalent)
- The specific tool name — "Claude (Anthropic) via Academic Research Skills pipeline" — not generic "AI tools"
- The specific categories marked USED

Example output for Nature (which requires disclosure in Methods):

```
## AI-assisted tools

The authors used Claude [MODEL_VERSION] (Anthropic), orchestrated via the
Academic Research Skills pipeline (Wu, 2026), during the preparation
of this manuscript. Specifically, the tool was used for literature
search assistance, citation verification, drafting of section outlines,
and internal peer-review simulation prior to submission. All
AI-assisted output was reviewed, edited, and verified by the authors,
who take full responsibility for the content of this article.
```

**Note**: Replace `[MODEL_VERSION]` with the actual model used in this run (e.g., `Fable 5`, `Sonnet 4.6`). Pull the identifier from session metadata rather than hard-coding a version, since Anthropic's lineup changes over time.

### Phase 5: Placement instructions

Output includes explicit placement instructions matching the venue's policy:

```
Placement: Methods section (Nature policy, accessed YYYY-MM-DD from
https://www.nature.com/.../policy-url). Include as the final
subsection of Methods, before Data Availability.
```

If the venue requires placement in multiple locations (e.g., Methods + cover letter + Acknowledgements), the mode generates tailored text for each location rather than a single paragraph.

---

## Failure cases this mode does NOT cover

- **Venues outside the v1 database**: the mode halts and asks the user. It does not guess.
- **Policies that have changed since the database snapshot**: the mode records the access date in the placement instructions. Users should verify against the current venue page before submission.
- **Analysis assistance**: if the AI actually ran computations or generated analysis results (not just writing), most venues require a separate disclosure in a Code Availability or Analysis section. This mode flags the case and produces a separate paragraph; the user must place it manually.
- **Co-authored AI**: as of the 2026 policy snapshot, no venue in the v1 database accepts AI as a listed author. The mode refuses to produce author-list text and instead produces authorship-rejection text plus the disclosure.

---

## Integration with existing journal_submission_guide.md

`journal_submission_guide.md` retains the two generic templates (Minimal / Detailed) as fallback for venues not in the v1 database. Disclosure mode's output supersedes those templates when the venue is known. The guide is updated to point to this mode for known venues.

---

## References

- `venue_disclosure_policies.md` — v1 policy database (ICLR, NeurIPS, Nature, Science, ACL, EMNLP)
- `policy_anchor_table.md` — #108 4-anchor × 16-field matrix (PRISMA-trAIce, ICMJE, Nature, IEEE) for the policy-anchor track
- `policy_anchor_disclosure_protocol.md` — #108 policy-anchor track render protocol (per-anchor flows, G10 7-row precedence table, auto-promotion forbiddance, §4.4 11 concerns resolved paths)
- `journal_submission_guide.md` — existing generic templates (fallback)
- `credit_authorship_guide.md` — existing CRediT authorship best practices
- Lu et al. (2026). Towards end-to-end automation of AI research. *Nature* 651, 914-919 — the ethics statement for Lu 2026 was drafted in compliance with Nature's policy; their methodology is a worked example of what this mode should produce.
- `docs/design/2026-05-14-ai-disclosure-schema-decision.md` — #108 Decision Doc (G1-G10 + §4.3 invariants + §4.4 11 open concerns)
- `docs/design/2026-05-14-ai-disclosure-impl-spec.md` — #108 implementation spec (resolved-paths table)
- ROADMAP_v3.2.md item 6 — design decisions (v1 venue set, unknown-venue halt, education/QA venues deferred to v2)
