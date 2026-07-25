# ARS #439 — User-declared layout/format profile (design-first)

> Status: design. No code until this doc is reviewed. Acceptance per #439.

## 0. TL;DR

A scholar-declared, standalone YAML (`format_profile`) that the Phase 7 `formatter_agent`
**follows** when rendering the final manuscript — fonts, line spacing, caption placement,
margins, table-border style. ARS ships the **contract**, never any school's or journal's
profile content. Separate file from `venue_profile` (decision **B** below). Additive and
backward-compatible: absent profile = today's formatter behavior, byte-for-byte.

## 1. Motivation and honest premises

Today layout is applied only as **prose in `formatter_agent.md`** (`:525-539` style
mapping, `:552-558` font stack, `:536-537` margins/spacing) — LLM best-effort, no
declarable profile. That is adequate for "match a journal's general style," but weak for
the byte-exact, rule-by-rule requirements of an institution's thesis template (fixed point
sizes, fixed line spacing, caption position).

Surfaced by a downstream fork (#436): a user adapting ARS for a Guangxi University thesis
had to fork and add a `python-docx` post-processor + a school-specific format reference +
a `guangxi-undergrad` profile, because there was no upstream way to *declare* a layout
profile without forking. Likely a recurring need for non-English / CJK / regional users.

**Honest premise — this is a contract, not a rendering engine.** The formatter is still an
LLM agent applying a Pandoc/python-docx pipeline; `format_profile` makes the *target rules*
declarable and inspectable. It does not guarantee byte-exact output by itself — it removes
the "the rules live only in prose" gap, not the "LLM rendering is non-deterministic" one.
The determinism ceiling is the renderer's, and that limit is stated, not hidden.

## 2. Decision: separate `format_profile`, not an extension of `venue_profile` (B)

Considered (A) extending `venue_profile` with layout fields vs (B) a new standalone
`format_profile`. **B.** Reasons (independent cross-model consult converged on the same
verdict):

1. **Different consumer = different contract.** `venue_profile` feeds a **verifier**
   (`scripts/verify_submission_package.py`, emits PASS/FAIL/NOT-CHECKED — "does this
   comply?"). `format_profile` feeds a **renderer** (`formatter_agent`, "how should this
   look?"). Mixing verifier-input and renderer-input in one schema is a design smell —
   two different behaviors, two different failure modes.
2. **Different lifecycle.** Submission limits bind to a **journal** (change journal →
   change file). Layout often binds to an **institution** template (one school, all its
   theses share it). A user changes journals without changing layout, or vice versa.
   Separate files keep that natural.
3. **Different data semantics.** `venue_profile` = numeric ceilings + discrete enums.
   `format_profile` = visual rendering rules (pt sizes, placement). Keeping them apart
   avoids one schema becoming a catch-all "publication config."

This also auto-satisfies **Invariant 11** (passport-level structured blocks must be
standalone schema files, never embedded) and keeps the orchestrator carry-forward set
untouched — `format_profile` is re-fed by path, exactly like `venue_profile`.

## 3. The declared-only guard carries over — but *downgraded*

`venue_profile`'s "declared-only, NEVER inferred/looked-up" guard exists to stop ARS
guessing a journal limit it cannot know (an integrity-sensitive lookup; the R-L3-2-D
no-inference threat model). **That threat model does not transfer to layout.** "What font
should the caption be" is a rendering preference, not an integrity-sensitive fact.

So `format_profile` keeps a *single* declared-only rule, stated strongly: **the formatter
follows only the supplied profile and never infers a missing layout field from the venue
name, the institution, the language/locale, or the filename.** The reason is **consistency
and reproducibility**, NOT integrity — so the rule is one strong sentence, not an
apparatus. It does **not** carry `venue_profile`'s heavy provenance machinery (`declared_by`
const, `_inferred`-value lint, source-naming laundering guard). The one place layout *does*
touch integrity (a declared margin/spacing that changes page count and thus a venue page
limit) is handled by the precedence rule in §3a, not by upgrading this guard.

## 3a. Conflict precedence — venue compliance wins (P1)

A declared `format_profile` field can change a compliance-relevant quantity: a larger font,
wider line spacing, or bigger margins increases page count and can push a manuscript past a
venue's page limit; a declared caption placement can interact with a required figure rule.
Layout is therefore not purely cosmetic, and the design must say who wins.

**Rule:** `venue_profile` compliance constraints **take precedence** over `format_profile`
rendering preferences. `format_profile` may only set rendering choices that do **not**
violate a declared venue constraint. When a declared layout field would push the manuscript
out of a declared venue limit, the formatter:

1. applies the venue-compliant value, not the format_profile value, **and**
2. emits a loud, non-silent note in the formatter's quality-checklist report naming the
   field, the venue constraint it would have violated, and the format_profile value that
   was overridden,
3. unless the user has explicitly recorded `accept_noncompliance: true` for that field
   (out of scope for the first slice — default is venue-wins, no override knob shipped
   until a concrete need exists; noted here so the precedence direction is unambiguous).

This keeps the integrity-sensitive half (compliance) governed by the verifier's contract
and the preference half (rendering) governed by format_profile, with a deterministic
tie-break. The formatter NEVER silently produces a noncompliant package to honor a layout
preference.

## 4. `format_profile` schema (draft — additive, standalone)

Path: `shared/contracts/submission/format_profile.schema.json` (alongside `venue_profile`).
Fields are **optional, omission = NOT-DECLARED ⇒ formatter uses its current prose default**
for that aspect (parallel to venue_profile's NOT-CHECKED). Canonical form is **omission, not
explicit `null`** — `null` is accepted only where YAML ergonomics demand it and documented
as equivalent to omission, so the formatter has one "not declared" state to branch on, not
two (codex P2). `additionalProperties: false`.

Minimal field set — **only fields with a concrete declared use case from #436**; speculative
knobs were cut (see "Cut" below):

- `body_font` (object): `{ family, size_pt }`
- `caption` (object): `{ font_family, size_pt, placement: enum[above, below],
  alignment: enum[left, center, right], latin_font_family }` — `latin_font_family` is the
  honest model of the #436 case (a Latin token like `Fig.` set in Times New Roman inside a
  CJK caption), replacing the misnamed `bilingual_caption`. Ordering / numbering / separator
  rules are NOT modeled (no concrete declared need; semantic caption content stays upstream
  per §5).
- `line_spacing` (object): `{ mode: enum[single, onehalf, double, fixed_pt], fixed_pt }`.
  **`fixed_pt` required iff `mode == fixed_pt`; `fixed_pt` present with any other mode is a
  schema-INVALID profile (rejected, not silently ignored)** — codex P2.
- `margins_cm` (object): `{ top, bottom, left, right }` (cm only, intentional — CJK thesis
  use case; unit-bearing values deferred to §10).
- `table_border_style` (enum): `[three_line, full_grid, none]`.

**Cut from the draft** (no concrete use case → no field, per the no-unrequested-abstraction
discipline): `profile_name` (display-only metadata drift — use the filename or a YAML
comment), `heading_font` (a single heading font is underspecified for real theses, which
distinguish title/chapter/section/TOC/bib levels — defer until a level-specific declared
need exists), `caption.bold` (no #436 requirement).

No `declared_by` const, no provenance fields (per §3). The schema description states the
single declared-only rule (§3) and the NOT-DECLARED → default-behavior contract. The lint
(§8) asserts these provenance fields are ABSENT, to guard against accidentally importing
venue_profile's heavy machinery.

## 5. Seams — where it hooks

- **Declare (Phase 0 intake).** `intake_agent.md` gains a follow-up at **Step 5 (Output
  Format)** — only offered for DOCX/PDF/LaTeX targets (no layout profile for raw Markdown).
  Mirrors the existing `venue_profile` follow-up at Step 3 exactly: offer to record a
  layout profile, store as a YAML validating against the schema, **record its path in a new
  PCR row** (`Format Profile`). Declined/skipped = no profile, no PCR value beyond `absent`.
- **Apply (Phase 7 formatter).** `formatter_agent.md` reads the profile **by path from the
  PCR** (alongside the values it already reads back at `:429`), and applies declared fields,
  falling back to its current prose defaults for NOT-DECLARED fields.
- **No intermediate phase (1–6) touched. No orchestrator carry-forward change** (path-fed).
  Semantic caption/table *content* stays upstream; format_profile governs *visual
  placement/style only* at Phase 7 (codex P3 — documented so the "no phase 1–6 change"
  claim is honest).

### 5a. Backward-compatibility invariant — designed, not asserted (P1)

The "absent profile = byte-equivalent to today" claim is only true if it is *built in*. A
new PCR row or a new formatter instruction can perturb an LLM formatter even when the
profile is absent. The invariant, stated as a buildable + testable rule:

> **When the `Format Profile` PCR row is absent OR resolves to no real path, the formatter
> MUST NOT read, mention, branch on, or receive any format-profile instruction.** Its input
> and prompt are byte-identical to the pre-#439 formatter for that run.

Mechanism (mirrors the #392 Invariant-7 seeding discipline): the formatter's new "Format
Profile" subsection is written so its *first* line is a guard — "if no `Format Profile`
path in the PCR, skip this entire section." Intake writes the PCR row **only** when a
profile is actually recorded (a declined follow-up writes nothing, not `absent` — per-row
absence already means not-declared, so writing an explicit `absent` would itself perturb).
A test asserts: a run with no profile produces a formatter input + prompt byte-identical to
the pre-#439 baseline. If that test cannot be made to pass, the byte-equivalence claim is
weakened in the docs rather than overstated.

### 5b. Failure modes — fail closed before formatting (P2)

The formatter reads the profile by path. Define behavior for every bad-path case, fail
**closed before formatting starts** (never half-format then discover the profile is
broken):

| Case | Behavior |
|---|---|
| PCR row absent / no path | NOT-DECLARED — use current defaults (the §5a invariant path). |
| Path present, file missing/unreadable | STOP before formatting; report the missing path; do not silently fall back (a declared-then-vanished profile is a user error worth surfacing, not a silent default). |
| File present, invalid YAML | STOP; report parse error + path. |
| YAML valid, schema-INVALID | STOP; report the schema violation (the lint contract is the same one CI enforces). |
| Path outside the workspace / relative-path resolution | Resolve relative to the PCR's run root; a path escaping the workspace is rejected (STOP), consistent with ARS's existing path-boundary posture (#310). |

"STOP" = the formatter refuses and asks the user to fix the profile, rather than producing
output under an ambiguous contract.

### 5c. Renderer capability boundary — best-effort, declared per target (P2)

A declared field may not be faithfully applicable across all of DOCX / PDF / LaTeX. The
contract does **not** overpromise: each field is **best-effort per output target**, and
when the formatter cannot honor a declared field for the chosen target, it says so in the
quality-checklist report (field + target + reason) rather than silently dropping it. Which
fields are reliably supported on which target is enumerated in Slice C, not promised here.

## 6. Boundary (POSITIONING.md note — required)

Add a POSITIONING.md boundary note: layout profiles are **user-supplied, out-of-tree**.
ARS ships the schema/contract; it ships **no** institution's or journal's profile content.
The suite stays format-agnostic — no school is bound in. Review criterion: a PR that adds a
specific institution's `format_profile.yaml` to this repo crosses the boundary.

**The committed example fixture (for the lint/tests) MUST be explicitly synthetic /
non-institutional** (e.g. fictional values, a `profile_name`-less generic profile) — a
fixture copied from a real school's template would itself violate this boundary while
claiming to enforce it (codex P3).

## 7. Schema deltas (additive only)

- NEW: `shared/contracts/submission/format_profile.schema.json`.
- NEW: PCR row `Format Profile` (path|absent) in `intake_agent.md` Step 5 + the PCR table.
- No change to `venue_profile.schema.json`, no passport envelope change, no Schema 9 change.

## 8. Validation plan (implementation rounds)

- `scripts/check_439_format_profile.py` — validates the schema + a committed example
  fixture, enforces: standalone (not embedded, Invariant 11), `additionalProperties:false`,
  the `line_spacing.fixed_pt` conditional, the NOT-DECLARED contract sentence present, the
  no-provenance-fields assertion (guards against accidentally importing venue_profile's
  heavy machinery). Mutation-tested.
- `tests/.../test_check_439_format_profile.py` — schema-valid + schema-invalid cases,
  including the conditional and the enum closures.
- CI wiring in `.github/workflows/spec-consistency.yml` (the established per-section pattern).
- A formatter behavior test: absent profile ⇒ output byte-equivalent to pre-#439 (the
  backward-compat guarantee), and a declared profile ⇒ the declared field is reflected.

## 9. Slice roadmap (review granularity — all ship in ONE release)

These slices are **NOT independently shippable** as user-facing features: Slice A is a
schema nothing reads, Slice B collects a profile nothing applies. Shipping A or B alone
would publish a contract with no consumer (a dead schema) and overstate that the gap is
closed (codex P1). They are sequenced for **review granularity and bisectability**, and the
**whole feature (A+B+C) ships together in one release** per the scope decision — no slice is
deferred, and none is presented to users as functional before C lands.

- **Slice A — contract.** Schema + synthetic example fixture + lint + tests + CI + PCR row
  spec + POSITIONING boundary note. No behavior change.
- **Slice B — intake wiring.** `intake_agent.md` Step 5 follow-up + PCR `Format Profile`
  row (written only when a profile is recorded, per §5a). Profile is collected and stored;
  formatter still ignores it.
- **Slice C — formatter wiring.** `formatter_agent.md` reads + applies declared fields with
  prose fallback; the §5a byte-equivalence test, the §5b fail-closed tests, the §5c
  capability notes, the §3a precedence test, and a reflected-field test.

## 10. Open items for the implementation round

- **Deterministic format-profile reader (depth gap vs `venue_profile`, recorded post-B/C
  review).** §5b fail-closed lives in formatter PROSE only — at ship there is no
  deterministic script that resolves the path, schema-validates a *user's* declared profile,
  and enforces the workspace-path boundary; CI validates only the synthetic example fixture.
  The named twin `venue_profile` IS deterministically enforced (`verify_submission_package.py`
  `--venue-profile` → `_validate_venue_profile` → schema-validate → fail-closed). So §5b's
  guarantee is prose-tier, one notch below `venue_profile`. This is the correct ceiling for
  this slice (the formatter is an LLM agent; the renderer mechanism was scoped deferred), but
  the parity target is a thin `read_format_profile.py` (resolve → schema-validate → path
  boundary → STOP/OK) that the formatter prose STAMPS rather than evaluates, mirroring #394's
  STAMP-ONLY formatter over a deterministic decision. A future slice, not a B/C blocker.
- Final field set in §4 (the draft is deliberately minimal — add only fields with a
  concrete declared use case; resist speculative layout knobs, per the no-unrequested-
  abstraction discipline).
- Whether `caption.placement` default (when NOT-DECLARED) stays "formatter's current prose
  default." Lean: stay current default — not-declared means "don't change today's behavior,"
  not "apply a new opinion."
- Whether `caption.placement` should later split by object type (figures-below /
  tables-above is the common convention) instead of one global value (codex P3). NOT in the
  first field set — added only if a declared need appears; a single value is enough for #436.
- `margins_cm` is cm-only by intent (CJK thesis use). Unit-bearing values (inch for US
  venues) deferred until a concrete need (codex P3).
- Whether `table_border_style: none` is a real declared case or should be dropped (codex
  P3) — keep only if the #436-class fixture needs it.
- DOCX path: declared fields map to a python-docx post-pass vs a Pandoc `--reference-doc`
  template the formatter generates. Decide in Slice C (renderer-mechanism, not contract).

## 11. Ship gate + definition of done (per slice)

- All §8 validations green.
- `/simplify` pass before report.
- Dual-track ship gate (codex review + security-review), 0 P1/P2, per standing discipline.
- Doc-alignment: if this lands in a `v*` release, the 7-item release invariant set is
  verified (CHANGELOG / README badge / "What's new" / version strings / bilingual parity /
  package metadata + GitHub Release object).
