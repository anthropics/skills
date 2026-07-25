# Judge reasoning excerpts — 2026-07-11 measurements

> Sections below the baseline blocks were appended for the post-#505
> exemption-sharpening runs (same day, same protocol); see
> `measurement-2026-07-11-505.json`.

Verbatim excerpts of the judge agents' prose reasoning, captured alongside the
boolean outcomes in `measurement-2026-07-11.json`. Not every agent produced prose
(several returned bare JSON); this file commits everything that was captured that
bears on a **miss** or a **notable pass**, so the mechanism reading in the audit
report is auditable. Judge: `claude-sonnet-5`, isolated per batch, given only the
advisory section variant + 6 items.

## Off-list title-shell misses — the exemption clause read broadly

- `ti-004` (post-#503 rep2, MISS): "'Beyond Awareness: Cybersecurity Training and
  Employee Security Behavior' — names specific mechanism (training → behavior) and
  domain (cybersecurity); doesn't reduce to a generic 'X and Y' shell despite
  superficial brevity. No match."
- `ti-002` (post-#503 rep2, MISS): "'The Weight of Care: Nurse Workload and the
  Quality of Patient Care' — names a specific mechanism/population (nurse workload
  → patient care quality); domain-native vocabulary, not a swappable shell."
- `ti-012` (post-#503 rep2, MISS): "names a specific mechanism/domain (vocabulary
  acquisition, L2 learners); doesn't survive noun-swap into an arbitrary field
  meaninglessly. No row match."
- `ti-013` (pre-#503, MISS): "'Aging Apart: Social Isolation Among Older Adults'
  is a title, not a frame pattern from the list — no match." (Pre-variant
  reasoning: judged against the table only, as instructed.)

## The same shape caught when the judge reads it as a bare pair

- `ti-004` / `ti-002` (pre-#503, FIRE): "bare 'X and Y' title shell, matches WP06
  (bare study-of frame)." (Same items, opposite call, adjacent runs — the
  decorated-title shape sits exactly on the exemption boundary.)
- `ti-007` (pre-#503, FIRE, cited "off-list shell"); (post-#503 rep1/rep2, FIRE,
  cited WP06).

## Family-variant behavior

- `nat-065` (pre-#503, FIRE): "'How does X affect Y' (SES → access to higher
  education) matches WP01 impact/effect frame." — interrogative rewording of a
  listed family, caught even pre-#503.
- `el-003` (post-#503 rep1, FIRE as off-list): "'What shapes X among Y' …
  matches the generic factors/determinants shell closely enough (off-list but
  clearly a shell: 'what shapes X among Y' swaps trivially)."
- `el-013` (post-#503 rep2, MISS): "'How does material choice bear on the
  durability of concrete structures' names a specific mechanism (material choice
  → durability) and site (concrete structures) — specific, not generic; doesn't
  survive swap." (Stable miss in all runs; same broad-exemption reading.)

## Hard negatives — the exemption working as intended

- `dn-006` (pre-#503, correct SILENT): "highly specific mediator construct, named
  scale, named population — domain-native operationalized wording, not a bare
  shell match despite containing 'mediate the effect.'"
- `dn-009` (pre-#503, correct SILENT): "precise mediation model with named
  instruments (IUS-12, GAD-7) — domain-native, high-confidence no match."
- `nat-077` (pre-#503, MISS): "close to WP16 … but not the canonical 'barriers
  and facilitators to X' pair shell … weak/ambiguous match, not high-confidence."
  (Post-#503: FIRE citing WP16 in both replicates.)

## Post-#505 runs — the decorated-title shape argued through the new rule

- `ti-002` (post-#505 round1 rep1, FIRE): "colon-decorated title; post-colon part is
  'Nurse Workload and the Quality of Patient Care,' a generic swappable
  noun-pair (WP01/WP06 shell). Decoration doesn't exempt it." (Baseline rep2
  argued the same item as "names a specific mechanism/population" and missed.)
- `ti-004` (post-#505 round1 rep2, FIRE): "'Cybersecurity Training and Employee
  Security Behavior' — bare study-of/factors-style noun pair, no named
  instrument or mechanism specified. Swappable shell."
- `ti-013` (post-#505 round1 rep2, FIRE): "'Aging Apart' decorated title; subtitle
  'Social Isolation Among Older Adults' is a bare topic label with no named
  site, instrument, or mechanism." (Rep1 missed the same item as "subtitle is
  named-population topic label … not swappable-shell form" — the single-topic
  subtitle sits nearest the boundary.)
- `el-013` (post-#505 round1 both reps, FIRE): "'How does X bear on Y' … no named
  instrument/theory/site, generic material/durability pairing is swappable."
  (Stable miss in every baseline run under the broad-exemption reading.)

## Post-#505 runs — negatives still exempted, and via the narrow list

- `dn-007` (post-#505 round1 rep1, correct SILENT): "names mechanism (unobtrusive
  indicators in annual reports), specific causal pathway (through TMT power
  centralization) — satisfies specified-pathway exemption."
- `dn-016` (post-#505 round1 rep2, correct SILENT): "names specific mechanism
  (telicity constraints, lexical aspect) and a specified causal pathway (L1
  transfer vs. aspect), plus named population." — the stated-tension /
  pathway arms of the narrow exemption doing the work.
- `nat-044` (post-#505 round1 rep2, MISS): "plain descriptive question without a
  shell connective (impact/relationship/role/factors), so weak match, stay
  silent." — the remaining interrogative off-list miss rides the
  high-confidence bar, not the exemption clause.

## Post-#505 FINAL-wording runs — single-topic subtitles caught; one prose-verdict inversion

- `ti-013` (FINAL rep2, FIRE): "'Social Isolation Among Older Adults' is a
  generic topic label (age group is generic demographic, not named population);
  decorative prefix ignored." — the round-2 demographic-descriptor clause doing
  exactly the work the round-1 miss motivated.
- `ti-012` (FINAL rep2, FIRE): "'Words in the Making' is decorative pre-colon
  phrase, ignored per rule" — single-topic subtitle judged on its own.
- `ti-002`/`ti-004`/`ti-007` (FINAL rep1, MISS — anomaly): the batch judge's
  prose called each "swappable shell / generic 'X and Y' noun-pair, no named
  instrument" yet its JSON verdicts said SILENT — a prose-verdict inversion.
  The boolean record stands per protocol; the same items fired in FINAL rep2
  and both round-1 replicates.
