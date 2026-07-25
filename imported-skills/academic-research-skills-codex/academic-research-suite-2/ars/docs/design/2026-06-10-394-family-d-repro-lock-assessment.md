# #394 Family D — `repro_lock` linkage assessment (slice 3 deliverable)

**Status**: ADJUDICATED — **Option 2** (maintainer, 2026-06-10, recorded on
issue #394). Family D ships nothing, permanently; the `repro_lock`
documentation-only boundary stands untouched, and the venue-facing need is
covered by declaring the artifact in `venue_profile.required_sections`
(enforced deterministically by B4). The verifier's check registry keeps the
`D` id prefix and the `repro_lock_linkage` family vocabulary reserved in the
report schema; no D check is registered or emitted. Should a concrete need
for passport↔package cross-checking emerge later, it is a new issue, not a
reopening of this assessment.

## The question (deliberately narrow)

`repro_lock` is documentation-only and explicitly not read by integrity gates
(`shared/artifact_reproducibility_pattern.md`, a recorded boundary the parent
spec does NOT overturn). The slice-3 question is narrower than that boundary:
when a passport carries `experiment_provenance[]` entries with a `repro_lock`,
should the **submission verifier** (not the integrity gates) check the lock's
**presence and shape** as part of package completeness — the same way B4
checks a Data Availability Statement's presence?

## Option 1 — presence/shape check (advisory-only D1)

A `D1` check, triggered only when the passport declares
`experiment_provenance[]` with a `repro_lock`: validate that the lock object
is present and shape-valid (per the existing `check_repro_lock.py` shape
rules), report `pass | fail | not_applicable`, **never** read or interpret the
lock's content, never strict-eligible (completeness signal, not an integrity
gate).

- For: mirrors B4's "required artifact present" semantics; a scholar who
  declared experiment provenance presumably wants the lock to survive into
  the submission package; the check is deterministic and cheap.
- Against: the lock lives in the **passport**, not in the **package** — the
  verifier's stated object is "the files in the output package" (§1.2). A
  passport-side presence check is a different axis than every other check in
  this tool, and `check_repro_lock.py` already lints the lock's shape at the
  repo layer. The marginal value over the existing lint is small.

## Option 2 — no check; boundary stands untouched

Family D ships nothing, permanently. The `repro_lock` stays
documentation-only end-to-end; submission-package completeness for
experiment-backed work remains the scholar's judgment (optionally encoded as
a `required_sections` entry in the venue profile, which B4 already checks).

- For: keeps the verifier's object pure (package files vs scholar
  declarations); avoids a second tool quietly re-reading a ledger the
  recorded boundary says gates don't read; the B4 + venue-profile path
  already covers the venue-facing version of this need.
- Against: a scholar with experiment provenance gets no automated nudge that
  the lock never made it into the deliverable set.

## Recommendation

**Option 2**, with the B4 escape hatch documented: a venue (or the scholar's
own discipline) that wants a reproducibility artifact in the package can
declare it in `venue_profile.required_sections`, and B4 enforces presence
deterministically without touching the `repro_lock` boundary at all. Option
1's only unique value is passport↔package cross-checking, which is exactly
the kind of scope creep the §1.2 premise ("the verifier reads artifacts, not
intentions") warns against.

**Adjudication (2026-06-10):** the maintainer ruled **Option 2**. The
recommendation above stands as the recorded rationale, with one sharpening:
Option 2's listed "Against" (no automated nudge that the lock missed the
deliverable set) is itself weak — the lock is a passport-side record and was
never required to enter the package; whether a reproducibility artifact
belongs in the package is a venue requirement, which `required_sections` +
B4 already enforce.
