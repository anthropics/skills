# Test design for each kind of testing

For the step-by-step derivation of cases (EP, BVA, decision tables, state transitions, pairwise, CRUD, scenarios) see `references/techniques.md`; generate values with `scripts/testgen.py`.

How a QA engineer designs tests for a feature. Each section: what it is for, techniques, a checklist, and a real example from a real project (details made generic).

## Contents
1. Functional
2. Edge cases
3. Negative cases
4. UI/UX
5. Exploratory
6. Regression
7. Retest of fixes
8. Cross-cutting: integration, permissions, data, environment
9. Prioritising when time is short

---

## 1. Functional
**Goal:** every requirement and every claim works as stated.
**Techniques:**
- *Requirement → test mapping:* one or more tests per claim from the baseline; mark which claims have no test.
- *State-transition testing:* draw the states (empty → queued → running → stopping → stopped / failed / cancelled / completed) and test every allowed transition and a few forbidden ones (stop a stopped run, delete a running one).
- *Decision tables* for settings that combine (policy × allowed domains × keywords × sign-in steps).
- *CRUD round-trips:* create, read back, update, read back, delete, reload.
**Checklist:** happy path end to end · each state reachable and shown correctly · each setting actually sent and honoured (check the request body) · results persist after reload · counts agree everywhere.
**Example:** the setup form sent `deny: ["Logout"]` and `max_runs: 4` exactly as edited; the run stopped at its limit.

## 2. Edge cases
**Goal:** behaviour at the edges of every input and condition.
**Techniques:**
- *Boundary values:* 0, 1, limit−1, limit, limit+1, max; empty string; whitespace only.
- *Equivalence partitions:* one representative per class (valid URL / http / uppercase HTTPS / localhost / bare host / ftp).
- *Shape and encoding:* very long text, unicode, emoji, RTL, quotes, HTML/markup, leading/trailing spaces, case variants.
- *Time and order:* first use, empty state, first open after idle, after a deploy, two actions back to back, refresh mid-action.
- *Scale:* 1 item, many items, a large dataset (17 pages / 85 results), long names.
- *Concurrency:* same action from two tabs/users, action while a run is live.
**Checklist:** every field at limit and limit+1 in UI **and** API · empty/first-run states · huge and tiny data · slow network · long names wrap.
**Examples:** a 9,991-char note saved but read back cut to 2,000 (UI and API limits disagreed); an emoji keyword chip shortened mid-character; a long project name overflowing the empty state.

## 3. Negative cases
**Goal:** the product fails safely and tells the user what to do.
**Techniques:**
- *Invalid input:* wrong formats, out-of-range numbers, missing required fields, unsupported protocols.
- *Missing prerequisites:* no permission, no secrets, no tunnel, no sign-in, expired session, deleted dependency.
- *Broken dependencies:* unreachable host, tunnel drop mid-run, backend/DB outage, third-party 5xx, slow responses/timeouts.
- *Interrupted flows:* cancel while queued, stop while running, abort the job from the infrastructure side, close the tab, reload mid-step.
- *Bypassing the UI:* send the same request straight to the API (to see what the backend does) — then judge severity by reachability (oracle 21).
- *Error guessing:* from past bugs in this product (failed states that blame the wrong step, raw codes, partial failures that erase work).
**Checklist for every failure:** a plain message · it blames the step that actually failed · it names what is missing · it offers the fix (link, retry) · completed work is kept · no raw codes · the failure is recorded once, correctly, in history.
**Examples:** unreachable host → plain reason + tunnel hint + job link (good); tunnel dropped mid-run → filed as app "Network error" and run ended "Completed" (bad); refused start blamed "Worker assigned" (only reachable via API).

## 4. UI/UX
**Goal:** the feature is clear, honest and comfortable to use.
**Checklist:**
- *Copy:* plain words, no internal flags (`--deny`), no raw enums (`3`, `Sync_failed`), no placeholders (`{n}`); every promise is true (oracle 5).
- *States:* empty, loading, partial, error, success all designed; nothing blank without a loader (loading_sweep.js).
- *Navigation:* every CTA lands on the right page (oracle 17); deep links and back button work; tabs keep their URL.
- *Hidden surface:* every optional column, filter, menu item and view mode turned on once (oracle 18).
- *Linked views:* selecting something in one view is reflected in others (oracle 19).
- *Feedback:* actions show progress ("Stopping…"), confirmations match the risk, toasts readable and not see-through.
- *Visual stability:* no flicker or jumps while data refreshes (flicker_scan.js).
- *Accessibility:* contrast in light and dark (contrast_scan.js), focus order, keyboard shortcuts, labels for screen readers, target sizes.
- *Responsiveness:* narrow width, zoom 200%, long text.
**Examples:** priority shown as 3/2/0; "Open Secrets" opened a blank page; dark-mode avatars invisible (1.05:1); blank page with a divider line for 12 s.

## 5. Exploratory
**Goal:** find what nobody thought to write down.
**How:** time-boxed sessions (30–60 min) with a charter: "Explore *area* with *resources* to discover *information*". Take notes as you go: what you tried, what surprised you, questions, bugs.
**Charter ideas:**
- Explore the lifecycle of a run with interruptions (stop, cancel, abort, tunnel drop) to discover misleading states.
- Explore the same flow as a second user who never used the CLI, to discover hidden setup assumptions.
- Explore re-runs on existing data with changed settings, to discover what is kept, dropped or ignored.
- Explore every number on the overview against its source, to discover inconsistencies.
**Heuristics:** follow the data (create it in one place, look for it everywhere); change one thing at a time; do things in an unusual order; repeat an action quickly; go back and forward; leave and return after idle.

## 6. Regression
**Goal:** prove the fixes didn't break anything.
**How:**
1. Re-run the main flow end to end on fresh data (setup → launch → live → stop/cancel → re-run → results → delete), on every entry surface.
2. Re-run every previously fixed bug's original steps on the new build — a main-flow pass alone is not enough.
3. Re-run the risky neighbours of each change (same component, same API).
4. Quick sweeps: loading states, contrast, one negative case per area.
**Record:** a table of area / what was checked / result, plus a per-bug "verified on build X".

## 7. Retest of fixes
See SKILL.md §4. Exact original steps first, then one variation; one result per bug; check the deploy; never call "not reproduced" fixed on your own.

## 8. Cross-cutting
- **Integration:** UI ↔ API ↔ CLI ↔ background jobs ↔ logs. Start in one, verify in the others (a CLI run should appear live in the UI; a UI stop should end the job).
- **Permissions:** owner vs other member vs UI-only user; per-user secrets and tunnels.
- **Data integrity:** round-trip every field; counts match; nothing silently truncated or dropped.
- **Environment:** throttled network, local apps via tunnel, outages; first load after idle.
- **Security basics:** secrets never shown in UI/logs/evidence; tokens not in URLs; redaction in captured requests.

## 9. Prioritising when time is short
1. The main job of the feature (can a user do the thing at all?) — Critical if broken.
2. Data loss or wrong results (truncation, misreported state, work erased).
3. Paths every user hits (first run, sign-in, empty state, loading).
4. Recently changed areas and fixed bugs (regression risk).
5. Negative paths with misleading messages.
6. Cosmetic and copy issues.
