# QA knowledge graph

_Generated 2026-11-23 14:07. Source: knowledge/graph.json — edit with scripts/kb.py, not by hand._

```mermaid
graph LR
  n0["bug: Status chip label vertically misaligned inside its pill"]
  n1["bug: Loop block's action menu lacked an option the If-branch menu"]
  n2["bug: Called a missing nested option a defect; the feature PR hid "]
  n3["bug: Filed 're-running a step inside a loop does nothing' as a bu"]
  n4["bug: Filed 'edits inside blocks not tracked as out of sync' as a "]
  n5["bug: Never combined user-authored If/While blocks with auto-gener"]
  n6["bug: Nearly blamed the product for 'No devices' / 'already in pro"]
  n7["bug: Probe errors: fill() mangled a rich condition input; fixed-c"]
  n8["bug: Bug cards lacked numbered repro steps, used cryptic setup sh"]
  n9["bug: Over-rated a bug only reachable by bypassing the UI"]
  n10["bug: Started engineering an artificial trigger without asking"]
  n11["bug: False alarm: count parser read chart labels as tile values"]
  n12["bug: False alarm avoided: CTA probe clicked a hidden duplicate ta"]
  n13["bug: QA skill lacked classic techniques and non-functional testin"]
  n14["bug: Count tile not filtered when the count is 0 (fix only covere"]
  n15["bug: 'Open Secrets' opened a blank Settings page"]
  n16["bug: Hidden Priority column showed raw 3/2/0"]
  n17["bug: Blank page with a divider line for 12+ s on first open after"]
  n18["bug: Selecting a live worker doesn't highlight its node in the gr"]
  n19["bug: Graph flickers (seen in a screen recording)"]
  n20["bug: A View-menu toggle switches on and persists but has no visib"]
  n21["bug: Filed 'open tab doesn't refresh after a background sync' as "]
  n22["bug: Three bugs filed that the owner rejected as invalid: legacy "]
  n23["bug: Zoom bug's screenshot taken at 27% while the overlap only ha"]
  n24["bug: Summary panel truncation not reported although the same defe"]
  n25["bug: Filed toolbar 'unreachable at 1024 px'; the inner content ar"]
  n26["bug: Filed a CLI defaulting to prod unless an env var selects sta"]
  n27["bug: Summary panel rows cut at the panel edge with no ellipsis in"]
  n28["bug: Several View-menu options shown in the prototype were missin"]
  n29["bug: One panel lists items as Failing that two other views show a"]
  n30["bug: Items with 0 tests labelled 'Not verified yet' instead of 'N"]
  n31["bug: Out-of-date filter drops 17 of 41 stale items; Summary shows"]
  n32["bug: A report ignores the data its header says it covers"]
  n33["bug: Raw ids, enums and escaped markdown shown in a detail panel"]
  n34{{"cause: baseline-gap"}}
  n35{{"cause: coverage-gap"}}
  n36{{"cause: instrument-gap"}}
  n37{{"cause: judgement"}}
  n38{{"cause: oracle-gap"}}
  n39{{"cause: probe-error"}}
  n40[["check: API: status codes per error class, error body format, schema"]]
  n41[["check: Another user/org can't read or change entities by ID; role l"]]
  n42[["check: List cases to automate as regression tests and generate them"]]
  n43[["check: BVA on every length/number/count/time input: testgen.py bva "]]
  n44[["check: After the last deploy, re-run every bug's original steps; re"]]
  n45[["check: Before publishing: every bug card has preconditions, numbere"]]
  n46[["check: Every failure names the real failed step and what is missing"]]
  n47[["check: Every sentence of helper/banner/empty-state copy is observab"]]
  n48[["check: Supported browsers and viewports tested, or recorded as out "]]
  n49[["check: At the start of every engagement walk references/competencie"]]
  n50[["check: Every count/state/name shown in 2+ places (headline, tiles, "]]
  n51[["check: For every re-run/run-this-step inside a block: note which in"]]
  n52[["check: Build the container x child-kind matrix (authored If/Else-If"]]
  n53[["check: Create in CLI/API, view in UI and vice versa; open page noti"]]
  n54[["check: CRUD × surface (UI/API/CLI) for every entity: possible, corr"]]
  n55[["check: contrast_scan.js on every view/drawer/dialog in dark and lig"]]
  n56[["check: Decision table for every outcome that depends on combined co"]]
  n57[["check: Before judging a fix: PR merged, deploy run's failing step i"]]
  n58[["check: EP: one representative per valid class and one test per inva"]]
  n59[["check: Error guessing from kb.py misses and this product's bug hist"]]
  n60[["check: cta_destinations.js on every state with CTAs (empty, failed,"]]
  n61[["check: Before attaching evidence: confirm the screenshot's state ma"]]
  n62[["check: flicker_scan.js on the region while data refreshes (positive"]]
  n63[["check: For every view/display toggle: measure the affected elements"]]
  n64[["check: Time zones, midnight crossings, date/number formats, long an"]]
  n65[["check: Keyboard only: every action reachable, visible focus, logica"]]
  n66[["check: For every new chip/pill/badge label: screenshot at 100% zoom"]]
  n67[["check: Data created before the change (old runs, notes, states) sti"]]
  n68[["check: Re-read the dev/PM thread at every resume and add new expect"]]
  n69[["check: loading_sweep.js: frames every 0.5 s for tab click, direct U"]]
  n70[["check: Re-run original steps; ask before forcing a trigger; use the"]]
  n71[["check: testgen.py pairwise over the feature's parameters (policy, c"]]
  n72[["check: Open the / (or action) menu inside EVERY container type at l"]]
  n73[["check: Time main API calls (p50/p95 over 10-20 requests), page-to-c"]]
  n74[["check: Repeat key flows as another member and as a UI-only user wit"]]
  n75[["check: Record every bug in ./qa-bugs/<feature>.json and run prerepo"]]
  n76[["check: Extract each prototype menu/toolbar/strip option list (from "]]
  n77[["check: No raw codes, enums, CLI flags, placeholders or backend erro"]]
  n78[["check: For every bug state the user path; if it needs API/crafted r"]]
  n79[["check: For any 'cut off / unreachable' claim: list scrollable ances"]]
  n80[["check: List the feature's PRs; grep their diffs for the gating of e"]]
  n81[["check: A late partial failure (one worker, one slot, an outage) doe"]]
  n82[["check: Before filing any target-specific or parity bug, reproduce t"]]
  n83[["check: Go / No-go / Go-with-conditions against exit criteria, with "]]
  n84[["check: Refresh/back/close mid-action, network drop and return, retr"]]
  n85[["check: Every saved field at 1, limit, limit+1 is read back whole vi"]]
  n86[["check: Use-case scenarios end to end: main, alternative and excepti"]]
  n87[["check: Before filing a staleness bug: find the requirement or on-sc"]]
  n88[["check: Secrets never in URLs, page source, logs, evidence, screensh"]]
  n89[["check: Run sentinel_start.js at the start of every session and labe"]]
  n90[["check: When a resource is unavailable or locked: look for other use"]]
  n91[["check: For each layout bug filed, enumerate all panels/lists/cards "]]
  n92[["check: Smoke test the main job end to end before deep testing; stop"]]
  n93[["check: testgen.py states: every valid transition, critical 2-step p"]]
  n94[["check: UI state (badge, stepper, banner) matches backend session + "]]
  n95[["check: Syntax/format: each valid form once, then missing/extra/wron"]]
  n96[["check: Plan from references/competencies.md: scope/out-of-scope, ri"]]
  n97[["check: In dark AND light: open every panel/drawer/summary/menu and "]]
  n98[["check: Re-check every surprising input result with real keyboard ty"]]
  n99[["check: XSS/injection-shaped strings in every text field render as t"]]
  n100(["lesson: A behaviour on one target is only a parity bug if the refere"])
  n101(["lesson: A bug card is for someone who was not there: numbered steps "])
  n102(["lesson: A button's label is a promise about where it goes; untested "])
  n103(["lesson: A control-flow feature must be tested as a composition matri"])
  n104(["lesson: A display option is verified by the change it makes on scree"])
  n105(["lesson: A new labeled chip/pill is a layout surface: check vertical "])
  n106(["lesson: A prototype is a list of controls: diff every option in ever"])
  n107(["lesson: A theme pass is a full pass: every panel, drawer and card ty"])
  n108(["lesson: Auto-refresh of an open page after background work is a prod"])
  n109(["lesson: Before calling something unreachable, scroll every scrollabl"])
  n110(["lesson: Before filing a claim-gap, plan-gap or raw-value bug, confir"])
  n111(["lesson: Build a role top-down from its full competency model (ISTQB-"])
  n112(["lesson: DOM sampling can't see repaints; use pixel frame-diff for vi"])
  n113(["lesson: Environment selection in internal/stage tooling (env vars, p"])
  n114(["lesson: Every container type (top level, If branch, Else, Else-If, W"])
  n115(["lesson: Expectations arrive mid-test; the baseline must be refreshed"])
  n116(["lesson: Measure what the screen shows while waiting, not only how lo"])
  n117(["lesson: Most false alarms come from the probe; confirm with a screen"])
  n118(["lesson: On shared accounts or single-device envs, contention and slo"])
  n119(["lesson: Re-running a child of a container (loop, branch, module) re-"])
  n120(["lesson: Retest with the original steps first; artificial triggers ne"])
  n121(["lesson: Severity follows how a real user reaches the bug; a UI that "])
  n122(["lesson: Synthetic input and coordinate clicks misrepresent rich inpu"])
  n123(["lesson: The screenshot must show the exact state the bug describes; "])
  n124(["lesson: What is hidden by default is still product; inspect it"])
  n125(["lesson: When a feature ships with PRs, read the diff for the gates o"])
  n126(["lesson: When a layout defect (clipping, truncation, overlap) is foun"])
  n127>"oracle: O1"]
  n128>"oracle: O10"]
  n129>"oracle: O13"]
  n130>"oracle: O14"]
  n131>"oracle: O15"]
  n132>"oracle: O17"]
  n133>"oracle: O18"]
  n134>"oracle: O19"]
  n135>"oracle: O2"]
  n136>"oracle: O20"]
  n137>"oracle: O21"]
  n138>"oracle: O3"]
  n139>"oracle: O4"]
  n140>"oracle: O5"]
  n141>"oracle: O6"]
  n142>"oracle: O7"]
  n143>"oracle: O8"]
  n144>"oracle: O9"]
  n145(("surface: accessibility"))
  n146(("surface: actor"))
  n147(("surface: api"))
  n148(("surface: compatibility"))
  n149(("surface: copy"))
  n150(("surface: cta"))
  n151(("surface: data"))
  n152(("surface: error-state"))
  n153(("surface: form-field"))
  n154(("surface: hidden-option"))
  n155(("surface: i18n"))
  n156(("surface: integration"))
  n157(("surface: list"))
  n158(("surface: live-view"))
  n159(("surface: loading"))
  n160(("surface: navigation"))
  n161(("surface: overview"))
  n162(("surface: performance"))
  n163(("surface: planning"))
  n164(("surface: reliability"))
  n165(("surface: retest"))
  n166(("surface: run-state"))
  n167(("surface: security"))
  n168(("surface: settings"))
  n169(("surface: signals"))
  n170(("surface: theme"))
  n50 -- applies_to --> n161
  n50 -- applies_to --> n157
  n50 -- uses --> n127
  n94 -- applies_to --> n166
  n94 -- uses --> n135
  n46 -- applies_to --> n152
  n46 -- uses --> n138
  n85 -- applies_to --> n153
  n85 -- uses --> n139
  n85 -- uses --> n143
  n47 -- applies_to --> n149
  n47 -- uses --> n140
  n81 -- applies_to --> n166
  n81 -- uses --> n141
  n74 -- applies_to --> n146
  n74 -- uses --> n144
  n53 -- applies_to --> n156
  n53 -- uses --> n128
  n53 -- uses --> n129
  n55 -- applies_to --> n170
  n55 -- uses --> n131
  n77 -- applies_to --> n149
  n77 -- uses --> n130
  n57 -- applies_to --> n165
  n44 -- applies_to --> n165
  n15 -- found_on --> n150
  n15 -- missed_because --> n35
  n15 -- taught --> n102
  n102 -- enforced_by --> n60
  n60 -- applies_to --> n150
  n60 -- uses --> n132
  n16 -- found_on --> n154
  n16 -- missed_because --> n35
  n16 -- taught --> n124
  n124 -- enforced_by --> n63
  n63 -- applies_to --> n154
  n63 -- uses --> n133
  n63 -- uses --> n130
  n17 -- found_on --> n159
  n17 -- missed_because --> n36
  n17 -- taught --> n116
  n116 -- enforced_by --> n69
  n69 -- applies_to --> n159
  n69 -- uses --> n142
  n18 -- found_on --> n158
  n18 -- missed_because --> n34
  n18 -- taught --> n115
  n115 -- enforced_by --> n68
  n68 -- applies_to --> n158
  n68 -- uses --> n134
  n19 -- found_on --> n158
  n19 -- missed_because --> n36
  n19 -- taught --> n112
  n112 -- enforced_by --> n62
  n62 -- applies_to --> n158
  n62 -- uses --> n136
  n11 -- found_on --> n161
  n11 -- missed_because --> n39
  n11 -- taught --> n117
  n117 -- enforced_by --> n98
  n98 -- applies_to --> n161
  n98 -- uses --> n127
  n9 -- found_on --> n147
  n9 -- missed_because --> n37
  n9 -- taught --> n121
  n121 -- enforced_by --> n78
  n78 -- applies_to --> n147
  n78 -- uses --> n137
  n10 -- found_on --> n165
  n10 -- missed_because --> n37
  n10 -- taught --> n120
  n120 -- enforced_by --> n70
  n70 -- applies_to --> n165
  n69 -- applies_to --> n160
  n43 -- applies_to --> n153
  n43 -- uses --> n143
  n43 -- uses --> n139
  n58 -- applies_to --> n153
  n95 -- applies_to --> n153
  n56 -- applies_to --> n168
  n56 -- applies_to --> n153
  n71 -- applies_to --> n168
  n93 -- applies_to --> n166
  n54 -- applies_to --> n156
  n86 -- applies_to --> n156
  n59 -- applies_to --> n161
  n96 -- applies_to --> n163
  n92 -- applies_to --> n163
  n83 -- applies_to --> n163
  n40 -- applies_to --> n147
  n41 -- applies_to --> n167
  n41 -- applies_to --> n146
  n99 -- applies_to --> n167
  n99 -- applies_to --> n153
  n88 -- applies_to --> n167
  n73 -- applies_to --> n162
  n65 -- applies_to --> n145
  n48 -- applies_to --> n148
  n64 -- applies_to --> n155
  n84 -- applies_to --> n164
  n67 -- applies_to --> n151
  n42 -- applies_to --> n163
  n13 -- found_on --> n163
  n13 -- missed_because --> n34
  n13 -- taught --> n111
  n111 -- enforced_by --> n49
  n49 -- applies_to --> n163
  n89 -- applies_to --> n169
  n89 -- uses --> n135
  n89 -- uses --> n138
  n75 -- applies_to --> n163
  n1 -- found_on --> n154
  n1 -- missed_because --> n35
  n1 -- taught --> n114
  n114 -- enforced_by --> n72
  n72 -- applies_to --> n154
  n72 -- uses --> n133
  n3 -- found_on --> n166
  n3 -- missed_because --> n37
  n3 -- taught --> n119
  n119 -- enforced_by --> n51
  n51 -- applies_to --> n166
  n51 -- uses --> n138
  n4 -- found_on --> n166
  n4 -- missed_because --> n37
  n4 -- taught --> n100
  n100 -- enforced_by --> n82
  n82 -- applies_to --> n166
  n82 -- uses --> n127
  n2 -- found_on --> n154
  n2 -- missed_because --> n34
  n2 -- taught --> n125
  n125 -- enforced_by --> n80
  n80 -- applies_to --> n154
  n8 -- found_on --> n149
  n8 -- missed_because --> n37
  n8 -- taught --> n101
  n101 -- enforced_by --> n45
  n45 -- applies_to --> n149
  n6 -- found_on --> n166
  n6 -- missed_because --> n37
  n6 -- taught --> n118
  n118 -- enforced_by --> n90
  n90 -- applies_to --> n166
  n7 -- found_on --> n153
  n7 -- missed_because --> n39
  n7 -- taught --> n122
  n122 -- enforced_by --> n98
  n98 -- applies_to --> n153
  n5 -- found_on --> n166
  n5 -- missed_because --> n35
  n5 -- taught --> n103
  n103 -- enforced_by --> n52
  n52 -- applies_to --> n166
  n29 -- found_on --> n161
  n29 -- caught_by --> n50
  n30 -- found_on --> n166
  n30 -- caught_by --> n94
  n31 -- found_on --> n157
  n31 -- caught_by --> n50
  n32 -- found_on --> n149
  n32 -- caught_by --> n47
  n33 -- found_on --> n149
  n33 -- caught_by --> n77
  n27 -- found_on --> n170
  n27 -- missed_because --> n35
  n27 -- taught --> n107
  n107 -- enforced_by --> n97
  n97 -- applies_to --> n170
  n97 -- uses --> n131
  n24 -- found_on --> n161
  n24 -- missed_because --> n38
  n24 -- taught --> n126
  n126 -- enforced_by --> n91
  n91 -- applies_to --> n161
  n91 -- uses --> n127
  n28 -- found_on --> n154
  n28 -- missed_because --> n34
  n28 -- taught --> n106
  n106 -- enforced_by --> n76
  n76 -- applies_to --> n154
  n76 -- uses --> n130
  n22 -- found_on --> n149
  n22 -- missed_because --> n37
  n22 -- taught --> n110
  n110 -- enforced_by --> n87
  n87 -- applies_to --> n149
  n87 -- uses --> n130
  n20 -- found_on --> n154
  n20 -- missed_because --> n38
  n20 -- taught --> n104
  n104 -- enforced_by --> n63
  n26 -- found_on --> n156
  n26 -- missed_because --> n37
  n26 -- taught --> n113
  n113 -- enforced_by --> n87
  n87 -- applies_to --> n156
  n21 -- found_on --> n158
  n21 -- missed_because --> n37
  n21 -- taught --> n108
  n108 -- enforced_by --> n87
  n87 -- applies_to --> n158
  n25 -- found_on --> n160
  n25 -- missed_because --> n39
  n25 -- taught --> n109
  n109 -- enforced_by --> n79
  n79 -- applies_to --> n160
  n79 -- uses --> n137
  n23 -- found_on --> n161
  n23 -- missed_because --> n39
  n23 -- taught --> n123
  n123 -- enforced_by --> n61
  n61 -- applies_to --> n161
  n61 -- uses --> n127
  n14 -- found_on --> n161
  n14 -- caught_by --> n43
  n12 -- found_on --> n150
  n12 -- caught_by --> n98
  n0 -- found_on --> n170
  n0 -- missed_because --> n35
  n0 -- taught --> n105
  n105 -- enforced_by --> n66
  n66 -- applies_to --> n170
  n66 -- uses --> n131
```

## Mandatory checks

- **api-contract** — API: status codes per error class, error body format, schema/types, limits = UI, idempotency/double submit, pagination/sort/filter edges (surfaces: api)
- **authz-idor** — Another user/org can't read or change entities by ID; role limits enforced server-side (surfaces: security, actor)
- **automation-candidates** — List cases to automate as regression tests and generate them where the team's tooling allows (e.g. a test-generation CLI) (surfaces: planning)
- **boundary-values** — BVA on every length/number/count/time input: testgen.py bva → min-1, min, min+1, max-1, max, max+1, empty, multi-byte at the boundary; in UI, API and after reload (surfaces: form-field)
- **bug-by-bug-rerun** — After the last deploy, re-run every bug's original steps; record verified-on-build per bug (surfaces: retest)
- **bug-card-complete** — Before publishing: every bug card has preconditions, numbered steps, expected, actual and embedded screenshots; setups have descriptive names, no shorthand; run prereport.py check (surfaces: copy)
- **causality** — Every failure names the real failed step and what is missing, and offers the fix (surfaces: error-state)
- **claims** — Every sentence of helper/banner/empty-state copy is observably true (surfaces: copy)
- **compat-matrix** — Supported browsers and viewports tested, or recorded as out of scope with reason (surfaces: compatibility)
- **competency-audit** — At the start of every engagement walk references/competencies.md; every area planned or N/A with reason; when building or changing the skill, audit it against the competency list (surfaces: planning)
- **consistency** — Every count/state/name shown in 2+ places (headline, tiles, badges, list, API) matches (surfaces: overview, list)
- **container-rerun-semantics** — For every re-run/run-this-step inside a block: note which instruction ids the request targets, compute the expected outcome from the container's current condition, and only file what differs from that (e.g. stale display) (surfaces: run-state)
- **control-flow-composition-matrix** — Build the container x child-kind matrix (authored If/Else-If/Else/While x natural if-else, wait-until, scroll-until, click-until, nested if) with testgen.py pairwise and run each cell with a deterministic oracle (surfaces: run-state)
- **cross-surface** — Create in CLI/API, view in UI and vice versa; open page notices changes made elsewhere (surfaces: integration)
- **crud-matrix** — CRUD × surface (UI/API/CLI) for every entity: possible, correct, reflected everywhere, survives reload, permission-checked (surfaces: integration)
- **dark-contrast** — contrast_scan.js on every view/drawer/dialog in dark and light; eyeball graphs, toggles, avatars (surfaces: theme)
- **decision-table** — Decision table for every outcome that depends on combined conditions (e.g. can Start be pressed): one expected result per column (surfaces: settings, form-field)
- **deploy-verified** — Before judging a fix: PR merged, deploy run's failing step inspected, build live (surfaces: retest)
- **equivalence-classes** — EP: one representative per valid class and one test per invalid reason (wrong type/format/range, empty, forbidden) (surfaces: form-field)
- **error-guessing** — Error guessing from kb.py misses and this product's bug history (surfaces: overview)
- **every-cta-destination** — cta_destinations.js on every state with CTAs (empty, failed, warnings, Needs Attention, toasts, drawers): no BLANK or MISMATCH landing (surfaces: cta)
- **evidence-matches-state** — Before attaching evidence: confirm the screenshot's state matches the steps (zoom %, width, theme) and that every quoted string is visible in it (surfaces: overview)
- **frame-diff-flicker** — flicker_scan.js on the region while data refreshes (positive control first); ask for the action/timing shown in any recording (surfaces: live-view)
- **hidden-options-on** — For every view/display toggle: measure the affected elements (labels, rows, lines) off vs on; the label's promise ('on every line') sets the expected count (surfaces: hidden-option)
- **i18n-time** — Time zones, midnight crossings, date/number formats, long and non-Latin strings (surfaces: i18n)
- **keyboard-a11y** — Keyboard only: every action reachable, visible focus, logical order, Escape closes dialogs, no traps; screen-reader names; zoom 200% (surfaces: accessibility)
- **labeled-chip-centering** — For every new chip/pill/badge label: screenshot at 100% zoom; assert text optically centered (equal padding top/bottom); if a twin surface exists (two views showing the same label), diff both. (surfaces: theme)
- **legacy-data** — Data created before the change (old runs, notes, states) still displays and works (surfaces: data)
- **linked-views-and-thread** — Re-read the dev/PM thread at every resume and add new expectations; select each entity and check every linked view follows (surfaces: live-view)
- **loading-frames** — loading_sweep.js: frames every 0.5 s for tab click, direct URL, reload, first open after ~15 min idle, sub-tabs, drawers, fast+throttled; look at blank frames (surfaces: loading, navigation)
- **original-steps-first** — Re-run original steps; ask before forcing a trigger; use the Not reproduced status (surfaces: retest)
- **pairwise-settings** — testgen.py pairwise over the feature's parameters (policy, concurrency, sign-in, tunnel, actor, entry…) + known risky full combinations (surfaces: settings)
- **per-container-menus** — Open the / (or action) menu inside EVERY container type at least once and diff its entries against the expected per-container list (surfaces: hidden-option)
- **perf-measured** — Time main API calls (p50/p95 over 10-20 requests), page-to-content, large data, repeated actions, long-open pages (surfaces: performance)
- **permission** — Repeat key flows as another member and as a UI-only user without the creator's setup (surfaces: actor)
- **prereport-gate** — Record every bug in ./qa-bugs/<feature>.json and run prereport.py check <feature>; nothing is reported or published until it passes (surfaces: planning)
- **proto-control-diff** — Extract each prototype menu/toolbar/strip option list (from its source when possible), diff with the build's, and cite the decision for every intentional removal (surfaces: hidden-option)
- **rawness** — No raw codes, enums, CLI flags, placeholders or backend error text reach the user (surfaces: copy)
- **reachability** — For every bug state the user path; if it needs API/crafted request/race, mark it and lower severity (surfaces: api)
- **reachability-scroll** — For any 'cut off / unreachable' claim: list scrollable ancestors (overflow auto/scroll with scrollWidth > clientWidth), scroll each, and click the control (surfaces: navigation)
- **read-pr-gating** — List the feature's PRs; grep their diffs for the gating of every option/menu under test and cite the line when classifying a missing option (surfaces: hidden-option)
- **recovery** — A late partial failure (one worker, one slot, an outage) doesn't erase or misdescribe completed work (surfaces: run-state)
- **reference-parity-first** — Before filing any target-specific or parity bug, reproduce the same steps on the reference target/env and record its result next to the bug; if identical, classify as shared behaviour or by design (surfaces: run-state)
- **release-recommendation** — Go / No-go / Go-with-conditions against exit criteria, with coverage line and open risks (surfaces: planning)
- **reliability** — Refresh/back/close mid-action, network drop and return, retries, timeouts, double submit (surfaces: reliability)
- **round-trip** — Every saved field at 1, limit, limit+1 is read back whole via UI and API after reload (surfaces: form-field)
- **scenarios** — Use-case scenarios end to end: main, alternative and exception flows with real data (surfaces: integration)
- **scope-confirm** — Before filing a staleness bug: find the requirement or on-screen promise of live updates; without one, log it as a question (surfaces: copy, integration, live-view)
- **secrets-hygiene** — Secrets never in URLs, page source, logs, evidence, screenshots or activity; masked in UI (surfaces: security)
- **sentinel-triaged** — Run sentinel_start.js at the start of every session and label states; before sign-off, every group in sentinel_report.js is triaged: bug filed (with state/page), known bug id, or expected with reason (surfaces: signals)
- **shared-env-contention** — When a resource is unavailable or locked: look for other users' artifacts (new records, sessions), wait one full release window, retry, and note the shared-env caveat on the bug (surfaces: run-state)
- **sibling-sweep** — For each layout bug filed, enumerate all panels/lists/cards of the same kind and record pass/fail for each in the bug (surfaces: overview)
- **smoke-first** — Smoke test the main job end to end before deep testing; stop and report if it fails (surfaces: planning)
- **state-transitions** — testgen.py states: every valid transition, critical 2-step paths, and every invalid event blocked in UI and refused by API; UI shown in and during each state (surfaces: run-state)
- **state-truth** — UI state (badge, stepper, banner) matches backend session + job log at every lifecycle state (surfaces: run-state)
- **syntax-malformed** — Syntax/format: each valid form once, then missing/extra/wrong-delimiter/case/whitespace/unicode look-alike/injection-shaped inputs (surfaces: form-field)
- **test-plan** — Plan from references/competencies.md: scope/out-of-scope, risks, entry+exit criteria, environments, test data; every competency area applicable or N/A with reason (surfaces: planning)
- **theme-full-sweep** — In dark AND light: open every panel/drawer/summary/menu and each card type; screenshot each; flag text cut without ellipsis, clipped descenders and low contrast (surfaces: theme)
- **verify-probe** — Re-check every surprising input result with real keyboard typing; never click by coordinates in a live session (surfaces: overview, form-field)
- **xss-injection** — XSS/injection-shaped strings in every text field render as text everywhere they appear (lists, drawers, activity, exports) (surfaces: security, form-field)

## Missed bugs and what now prevents them

| Bug | Product | Found by | Cause | Lesson | Check |
|---|---|---|---|---|---|
| M01 Status chip label vertically misaligned inside its pill | Web app | user | coverage-gap | A new labeled chip/pill is a layout surface: check vertical centering and padding symmetry in the shipped UI (light and dark), and compare both views when two of them render the same label. | labeled-chip-centering |
| M02 Loop block's action menu lacked an option the If-branch menu had; only the If-branch menu was opened | Mobile app | user | coverage-gap | Every container type (top level, If branch, Else, Else-If, While body, nested block) has its OWN slash/action menu; inventory each one separately and compare it with the design, never infer one from another | per-container-menus |
| M03 Called a missing nested option a defect; the feature PR hid it inside containers on purpose | Mobile app | self | baseline-gap | When a feature ships with PRs, read the diff for the gates on what you test (menus, flags, mode checks); a deliberate gate in code makes the gap a requirements question, not a regression | read-pr-gating |
| M04 Filed 're-running a step inside a loop does nothing' as a bug; re-running a child restarts its loop from the condition (by design) | Mobile app | user | judgement | Re-running a child of a container (loop, branch, module) re-runs the container; derive the expected result from the container's semantics at the moment of re-run (is the condition still true?), read the request payload, and ask the dev before filing | container-rerun-semantics |
| M05 Filed 'edits inside blocks not tracked as out of sync' as a mobile bug; counters track parent steps and web behaves the same | Mobile app | user | judgement | A behaviour on one target is only a parity bug if the reference target differs; before filing, run the same steps on the reference (web, stage or prod) and confirm what the counter or state model counts | reference-parity-first |
| M06 Never combined user-authored If/While blocks with auto-generated conditions or nested conditionals | Mobile app | user | coverage-gap | A control-flow feature must be tested as a composition matrix: every container (If, Else-If, Else, While) x every child kind the product can produce, including AI-derived conditionals and until-loops (wait/scroll/click-until) and nested conditionals, not only the slash commands | control-flow-composition-matrix |
| M07 Nearly blamed the product for 'No devices' / 'already in progress' while another user held the only device on a shared account | Mobile app | self | judgement | On shared accounts or single-device envs, contention and slow resource release look like product bugs; check for other users' activity and wait out the release before attributing them to the product | shared-env-contention |
| M08 Probe errors: fill() mangled a rich condition input; fixed-coordinate clicks hit an upsell button and a step checkbox | Mobile app | self | probe-error | Synthetic input and coordinate clicks misrepresent rich inputs; confirm any odd input result with real keystrokes and target by role/label, never by screen coordinates | verify-probe |
| M09 Bug cards lacked numbered repro steps, used cryptic setup shorthand and did not embed screenshots | Process | user | judgement | A bug card is for someone who was not there: numbered steps from a named setup, expected vs actual, ids, and the screenshots embedded in the published report | bug-card-complete |
| M10 Over-rated a bug only reachable by bypassing the UI | Process | user | judgement | Severity follows how a real user reaches the bug; a UI that blocks the action means the UI bug is fixed | reachability |
| M11 Started engineering an artificial trigger without asking | Process | user | judgement | Retest with the original steps first; artificial triggers need the user's go-ahead; not reproduced is not fixed | original-steps-first |
| M12 False alarm: count parser read chart labels as tile values | Process | self | probe-error | Most false alarms come from the probe; confirm with a screenshot and a real user action before filing | verify-probe |
| M14 QA skill lacked classic techniques and non-functional testing until asked | Process | user | baseline-gap | Build a role top-down from its full competency model (ISTQB-level), then layer project lessons; audit against the standard before calling it complete | competency-audit |
| M16 'Open Secrets' opened a blank Settings page | Web app | user | coverage-gap | A button's label is a promise about where it goes; untested destinations hide broken links | every-cta-destination |
| M17 Hidden Priority column showed raw 3/2/0 | Web app | user | coverage-gap | What is hidden by default is still product; inspect it | hidden-options-on |
| M18 Blank page with a divider line for 12+ s on first open after idle | Web app | user | instrument-gap | Measure what the screen shows while waiting, not only how long it takes; include first open after idle | loading-frames |
| M19 Selecting a live worker doesn't highlight its node in the graph | Web app | dev | baseline-gap | Expectations arrive mid-test; the baseline must be refreshed from the thread every session; selection in one view must reflect in linked views | linked-views-and-thread |
| M20 Graph flickers (seen in a screen recording) | Web app | dev | instrument-gap | DOM sampling can't see repaints; use pixel frame-diff for visual stability, and get exact steps from recordings | frame-diff-flicker |
| M21 A View-menu toggle switches on and persists but has no visible effect; it was marked as working | Web app | user | oracle-gap | A display option is verified by the change it makes on screen, not by its checkmark or persistence: count the affected elements with it off and on, and compare with what the label promises | hidden-options-on |
| M22 Filed 'open tab doesn't refresh after a background sync' as a bug; owner says not valid | Web app | user | judgement | Auto-refresh of an open page after background work is a product choice, not a defect, unless the spec or UI copy promises live updates; record it as an observation and ask | scope-confirm |
| M23 Three bugs filed that the owner rejected as invalid: legacy page content, tab gating for new projects, panel values | Web app | user | judgement | Before filing a claim-gap, plan-gap or raw-value bug, confirm the surface is in the feature's scope and the value isn't intended; a plan line or a pre-existing surface alone is not enough evidence | scope-confirm |
| M24 Zoom bug's screenshot taken at 27% while the overlap only happens at 20%; quoted text came from a DOM read, not the picture | Web app | user | probe-error | The screenshot must show the exact state the bug describes; quote only what is visible in it | evidence-matches-state |
| M25 Summary panel truncation not reported although the same defect was filed for a sibling panel | Web app | user | oracle-gap | When a layout defect (clipping, truncation, overlap) is found in one container, sweep every container of the same kind before filing, and list every place in the one bug | sibling-sweep |
| M26 Filed toolbar 'unreachable at 1024 px'; the inner content area scrolls sideways and every control is reachable | Web app | user | probe-error | Before calling something unreachable, scroll every scrollable ancestor (not just the window) and try to reach it with a real action | reachability-scroll |
| M27 Filed a CLI defaulting to prod unless an env var selects stage as a bug; owner says expected | CLI | user | judgement | Environment selection in internal/stage tooling (env vars, profiles) is a deliberate design choice; an internal-only setup step is a note for the testers, not a product bug, unless docs or the owner say the profile should drive it | scope-confirm |
| M28 Summary panel rows cut at the panel edge with no ellipsis in dark mode; dark mode was only contrast-scanned on one view | Web app | user | coverage-gap | A theme pass is a full pass: every panel, drawer and card type is re-opened in the other theme and judged for clipping and truncation too, not just contrast on the main view | theme-full-sweep |
| M29 Several View-menu options shown in the prototype were missing from the build; not reported | Web app | user | baseline-gap | A prototype is a list of controls: diff every option in every menu, toolbar and strip against the build, item by item, and report each missing one unless a decision (thread/PR) removed it | proto-control-diff |
