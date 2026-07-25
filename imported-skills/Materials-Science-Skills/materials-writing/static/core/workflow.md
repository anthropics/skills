# Writing Workflow

Use the smallest workflow tier that matches the job:

- **Local paragraph edit:** run terminology and argument checks internally,
  then edit only the supplied paragraph when its claim, evidence, and boundary
  are already clear.
- **Section or manuscript job:** run Stages 1-5 and stop at the confirmation
  gate before full prose.
- **QA or multi-round revision:** run the state preflight, content-first QA
  order, and stopping rules.

## State preflight

For `writing_mode: qa` or explicit scored multi-round revision, check the
project's foundation files and `state.json`. Do not create active state inside
the skill package. Load the state-machine references only when needed and
carry forward `writing_mode`, `round`, `scores`, `previous_scores`,
`technical_debts`, `stop_status`, and `artifacts`.
If foundation files or `state.json` are missing, report the missing inputs and
stop before drafting or scoring, or return a project-level init/state patch
when the user requests initialization. If active files cannot be edited
directly, return a state patch; never silently drop the state update.

## Stages

### 1. Identify and lock

Resolve writing mode, paper type, section, language, journal family, material
family, domain, and input source. Build a terminology ledger for materials,
binders, modifiers, methods, standards, units, and abbreviations. Seed it from
`experiment-record.yaml` when provided and flag missing or conflicting fields.

### 2. Build the argument

Write one sentence:

> In [engineering problem], we [advance] using [material/approach], supported
> by [evidence], with [boundary].

Map each major claim to evidence and a boundary before drafting; this is the
claim-evidence-boundary table. Load `evidence-contract.md` for the full audit
format. If the argument cannot be written, stop and surface the missing
decision.

### 3. Map the section

Load the selected section fragment. Use these default orders:

- experimental manuscript: Results -> Introduction -> Conclusion -> Methods -> Abstract
- review paper: synthesis axes -> gap -> trend -> outlook
- methods paper: protocol -> validation -> boundary

Give every paragraph one message: context, gap, approach, result, comparison,
mechanism, implication, or limitation. The first sentence must forecast that
message, and the paragraph must be easy to reverse-outline. Load
`argument-chain.md` or `article-architecture.md` only when the section needs
the deeper map.

### 4. Confirm before full prose

For a complete section or manuscript, show and confirm:

- the one-sentence argument;
- detected paper type, section, journal, material family, domain, and
  paragraph map;
- current writing state and foundation-file status;
- locked terminology;
- inferred assumptions, especially contribution, leading result, and mechanism
  evidence;
- at most 2-3 high-leverage questions.

The local paragraph tier is the only confirmation-gate exemption.

### 5. Draft, calibrate, revise

- Draft from evidence outward; keep claims near their supporting data, figure,
  table, citation, or visible placeholder.
- Use `show`/`demonstrate` for direct evidence, `suggest`/`indicate` for
  trends, and `may`/`could` for plausible mechanisms.
- Downgrade unsupported `first`, `novel`, `proves`, `significantly improves`,
  `environmentally friendly`, and `confirmed mechanism` wording.
- Check one-message paragraphs, topic sentences, causal or comparative
  transitions, and reverse-outline clarity.
- Return the section draft and six-part output in `output-format.md`.
- For revisions, change only flagged paragraphs or claims. Re-run only checks
  affected by the edit; return to Stage 4 if the original premise was wrong.

## Gates

- Claims stay within the evidence contract; missing evidence remains visible.
- Terminology stays canonical after the ledger is locked.
- Complete sections pass the confirmation gate before full prose.
- QA runs content review before language review, then validation and scoring.
- Stop a revision loop after three full rounds, two consecutive gains below
  0.5, missing key evidence, unresolved specialist conflict, or the target
  threshold.

## Handoffs

- `materials-reader`: route source-paper-intensive reading to `materials-reader`; consume
  source-grounded notes and `reader-package`/`source_map`.
- `materials-citation`: claim-evidence-boundary rows.
- `materials-doe`: route experiment-matrix or factor-design requests to `materials-doe`;
  consume the factor matrix and `doe-handoff`.
- `materials-polishing`: draft plus terminology and claim-evidence maps.

Missing handoff artifacts are routed through
`../../../_shared/paper-production/weakness-routing.md`; they are never
silently fabricated.
