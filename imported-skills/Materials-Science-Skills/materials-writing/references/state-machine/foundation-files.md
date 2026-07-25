# Foundation Files

Use the foundation pack when a materials writing task needs continuity across
drafting, revision, or QA rounds. The files establish evidence boundaries
before prose and give future runs a stable project memory.

## Required Files

| File | Role | Minimum completion before drafting |
|---|---|---|
| `00_scope.md` | Defines task, audience, material system, target deliverable, and boundaries. | Text type, material system, deliverable, and blocked claims are named. |
| `01_research_canon.md` | Locks facts, terminology, forbidden claims, and open decisions. | Hard facts and forbidden claims are separated. |
| `02_evidence_table.md` | Maps claims to sources, evidence strength, section use, risk, and status. | Major claims are marked as evidence-backed, plausible-inference, hypothesis, or unsupported. |
| `03_argument_map.md` | Records scientific tension, research question, one-sentence argument, rivals, and final move. | One-sentence argument can be written without inventing facts. |
| `04_section_contracts.md` | Defines each section's purpose, required evidence, allowed claims, forbidden claims, and checklist. | Target section has allowed and forbidden claims. |
| `05_style_guide.md` | Locks language, terminology, claim-strength, and reviewer-safe style choices. | Claim-strength wording rules are stated. |

## Operating Rules

- `compose` mode initializes the foundation pack before drafting.
- `revise` mode backfills missing foundation fields from the existing draft
  before editing prose.
- `hybrid` mode reconciles existing draft text with foundation files, then
  records what was kept, replaced, or deferred.
- `qa` mode reads the foundation pack and updates `state.json`; it does not
  rewrite prose unless the user explicitly asks for revision.
- Foundation files are project artifacts. The skill repository only stores
  templates; a user project stores the active copies and `state.json`.
