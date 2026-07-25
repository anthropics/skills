# Submission Package Workflow

The workflow follows Route C of the paper-production orchestrator.

## Phase 1: Journal fit confirmation

Load `_shared/journal-formats/<journal>.md` and
`_shared/journal-templates/<journal>.yaml`. Emit a journal-fit note and
mark every `live_verification_fields` entry with a placeholder.

## Phase 2: Manuscript package audit

Load `writing_state_path` before required-field validation when it is set.
Use writing-state title, abstract, authors, corresponding author, and keywords
only to fill blank submission-manifest values; explicit submission values win.
Emit `manuscript/SOURCE.md` and record the parsed input status in
`submission-package.yaml`. If both sources omit required title or
corresponding author data, stop final assembly.

## Phase 3: Figure and graphical abstract intake

If `figure_package_path` is set, load its structured manifest before final
validation. Record the input parse status and declared artifact status in both
`figures/SOURCE.md` and `submission-package.yaml`. If the path is missing or
unparseable, preserve that status rather than implying figure readiness.

## Phase 4: Data and declaration boundary

If `fair_package_path` is set, load its structured FAIR manifest before final
validation and record its input and artifact statuses. A
`data_availability_status: ready` package requires an existing, readable, and
parseable FAIR manifest; otherwise final assembly is blocked and declarations
keep a live-verification placeholder. Empty declaration fields stay as
`[LIVE-VERIFICATION: ...]` placeholders.

## Phase 5: Reviewer-risk regression

If `weakness_routing_path` is set, read the weakness-routing CSV. Compute
G6 (Reviewer Simulation) and G7 (Submission Fit) regression status. Emit
`reviewer-risk-regression.md`. If the path is missing, record G6/G7 as
`not_applicable` with a note that reviewer simulation has not been run.

## Phase 6: Final assembly

Run `build_submission_package.py`. The script creates the
`submission-package/` directory, writes human-readable `MANIFEST.md` and
machine-readable `submission-package.yaml`, calls the three generator scripts,
writes `SOURCE.md` stubs, and writes `reviewer-risk-regression.md`. When an
existing output directory is reused, it removes only stale optional artifacts
owned by this tool. Manually changed stale optional artifacts are preserved and
recorded in `submission-package.yaml` with their path, `ownership` set to
`user-preserved`, and hash. Use `--dry-run` to validate the manifest before
final assembly.
