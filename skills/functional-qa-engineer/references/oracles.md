# Oracle catalogue

Each oracle: what it asserts, how to apply it, and a real bug it caught on a real project (details made generic) so you can recognise the pattern elsewhere.

## Contents
1. Consistency
2. State truth
3. Causality
4. Round-trip
5. Claim
6. Recovery
7. Loading state
8. Limits
9. Permission / actor
10. Cross-surface
11. Persistence
12. Destructive action
13. Concurrency
14. Copy and rawness
15. Theme / contrast
16. Defaults
17. Destination
18. Hidden options
19. Linked views
20. Visual stability (flicker)
21. Reachability
— Why manual finds were missed

---

## 1. Consistency
**Asserts:** one fact has one value everywhere it is shown.
**Apply:** for each number or state, list every place it appears (headline sentence, stat tiles, tab badges, table row count, export, API response) and compare. Also compare timestamps/durations between header and activity log.
**Caught:** header "Queued" while the progress stepper said "Starting workers"; "Items written 0" beside "3 items listed"; header and Activity disagreeing on run age. (A tiles-vs-headline mismatch that did not reproduce on reload was dropped — confirm before filing.)

## 2. State truth
**Asserts:** what the UI says happened is what the backend recorded.
**Apply:** keep the API (session/state endpoint) or CLI status open beside the UI; for background jobs read the job log. Compare state, stop reason, counts and timestamps.
**Caught:** a job aborted while queued showed "Worker assigned → Starting workers" and stayed queued forever; a UI-started job that never got a worker was blamed on the infrastructure after a 10-minute wait, when the log showed the CLI exiting on a missing flag.

## 3. Causality
**Asserts:** an error names the step that actually failed and what is missing.
**Apply:** for every failure, find the real cause (response body, log) and check the UI's step highlight and message.
**Caught:** a start refused with `422 MISSING_CONFIG` highlighted "Worker assigned" in red though no worker was requested, and "Add the missing secret" did not say which one.

## 4. Round-trip
**Asserts:** saved == read back, for every field, at every size.
**Apply:** write a value with a start and end marker (`QA START … QA END`) at 1, limit-1, limit, limit+1; reload; check the end marker and length via the UI and the API.
**Caught:** notes accepted at 9,991 characters (201) but read back cut to exactly 2,000 — silent data loss; earlier, cut at ~2,000 with no counter.

## 5. Claim
**Asserts:** every promise the UI makes is observably true.
**Apply:** read all helper text, banners, empty states and tooltips; turn each into a check.
**Caught:** "New items now have a dashed border" with no dashed item; "Read-only by default" while the form defaulted to Allow changes.

## 6. Recovery
**Asserts:** a partial failure does not erase or misdescribe completed work; one bad worker does not fail the whole job.
**Apply:** let a long run hit a late failure (expired login, dropped tunnel, one bad item) and read the final state.
**Caught:** a job that signed in and processed 3 pages / 5 records over 20 min ended "Didn't start · No results yet" because one late re-login failed; a tunnel drop mid-run was filed as app bugs and the run ended "Completed".

## 7. Loading state
**Asserts:** no blank or half-built screen longer than ~1 s without a visible loader; no wrong shell.
**Apply:** `scripts/loading_sweep.js` — sample screenshots every 0.5 s for: tab click from another section, direct URL, reload, first open after ~15 min idle, sub-tab switches, drawers; fast and throttled network. Look at the frames; DOM "loader" hits can be invisible.
**Caught:** first open after idle showed only a divider line for 12+ s (found manually by the user first — this oracle exists because it was missed); earlier, account-level tabs flashed before project tabs.

## 8. Limits
**Asserts:** the UI limit, the API limit and the stored limit agree; limits are announced before you hit them.
**Apply:** find each limit (counter, maxlength, server error) and test at limit and limit+1 in both UI and API. Check budgets (time, count, credits) stop where they say.
**Caught:** UI counter at 10,000 while the API still truncated at 2,000. (A run limit overshoot under parallelism was confirmed expected by dev — record and drop.)

## 9. Permission / actor
**Asserts:** another legitimate user can do the same thing, and is told up front if they cannot.
**Apply:** repeat key flows as a second org member and as a user who never used the CLI and has no personal secrets or local tunnel.
**Caught:** a second user could not re-run because secrets are per-user, and only found out after pressing Start; another user saw "No tunnel is running" with no hint whose tunnel was needed.

## 10. Cross-surface
**Asserts:** something created or changed in one surface (CLI, API, another tab) shows up correctly in the others.
**Apply:** create via CLI → view in UI; re-run from UI something the CLI created; leave a page open while another surface changes it.
**Caught:** a CLI-created job invisible in the UI until a separate sync step; re-running a CLI-created job from the UI dropped its sign-in steps and allowed domains; the UI's "copy CLI command" produced an invalid command.

## 11. Persistence
**Asserts:** after reload, the state is what you left.
**Apply:** after every write (label, note, delete, setting), reload and re-check.
**Caught:** delete appeared to work but a reload brought the item back (no backend call).

## 12. Destructive action
**Asserts:** confirmation proportional to the damage; disabled while unsafe; the effect is real and permanent.
**Caught:** Cancel Run acted with no confirmation while Stop Run had one. Good pattern seen after the fix: Delete disabled with "Stop the run first", typed-name confirmation, gone after reload.

## 13. Concurrency
**Asserts:** actions during an active process are blocked or safe; live pages notice changes made elsewhere.
**Caught:** an open page did not notice a run started from the CLI until reload.

## 14. Copy and rawness
**Asserts:** no raw codes, enum values, internal flags, placeholders or backend error text reach the user.
**Caught:** "Sync_failed", "{n} items", raw priority numbers 3/2/0, CLI flags in result text, a raw upstream error "empty response from provider".

## 15. Theme / contrast
**Asserts:** every text and control meets contrast in light and dark.
**Apply:** `scripts/contrast_scan.js` on each view, tab, drawer and dialog in dark mode; then eyeball graphs, toggles and avatars (non-text elements the scan misses).
**Caught:** avatar initials at 1.05:1 in dark mode; graph links and toggles nearly invisible.

## 16. Defaults
**Asserts:** defaults are safe, match the copy, and survive re-runs.
**Caught:** re-running with edited settings marked a new name and domains as "Changed" but never sent them.

## 17. Destination
**Asserts:** every link and button goes where its label says, and the page it opens is usable (not blank, not a generic settings page, correct product).
**Apply:** list every CTA on every state (empty, failed, needs-attention, warnings, toasts, drawers). Click each one; record the URL and the first heading of the page it lands on; compare with the label ("Open Secrets" must land on Secrets). Include new-tab links.
**Caught (manually, by the user):** "Open Secrets" opened a blank generic Settings page instead of the Secrets page.

## 18. Hidden options
**Asserts:** everything the UI can show is correct, not only what it shows by default.
**Apply:** turn on every optional column, filter, group-by, toggle, expandable section and setting at least once; open every "More actions" item; switch every view mode. Then apply the copy/rawness, consistency and persistence oracles to what appears.
**Caught (manually, by the user):** the **Priority** column (hidden by default) showed raw numbers 3/2/0 instead of labels.

## 19. Linked views
**Asserts:** selecting an entity in one view is reflected in every related view (select a worker → its node highlights on the graph; select a result → its source; select a step → its path).
**Apply:** for each selectable entity (worker, job, page, step, result), select it and check every other visible view for focus/highlight/scroll. Also re-read the latest dev and PM messages for newly stated expectations of this kind and add them to the baseline.
**Caught (by dev):** choosing a live worker opens a panel over the graph but doesn't highlight the node it is on.

## 20. Visual stability (flicker)
**Asserts:** nothing on screen blinks, repaints blank, or jumps while data refreshes.
**Apply:** DOM counts are not enough: a node can stay mounted while it repaints, an image reloads, or a layer flashes. Use `scripts/flicker_scan.js` on the region under test while the update is happening (a live run, polling, a re-render), and run a positive control first. If a teammate's recording shows it, get the exact action and timing from them before concluding "not reproduced".
**Status here:** reported by dev with a screen recording; not reproduced by DOM sampling or interactions; the frame-diff scan was added afterwards.

## 21. Reachability
**Asserts:** a bug's severity matches how a real user reaches it.
**Apply:** when a repro needs a direct API call, a crafted request, or a race (deleting a secret between review and Start), say so in the bug and lower the severity; confirm the UI path first. A UI that blocks the action correctly means the UI bug is fixed even if the backend still behaves badly when bypassed — record that as a note for devs, not an open UI bug.
**Caught:** a refused start still showed "Worker assigned" and no secret name, but only via a direct API call; the user (rightly) called the UI bug fixed.

---

## Why manual finds were missed (and what now catches them)

| Found by | Bug | Why the oracles missed it | Now caught by |
|---|---|---|---|
| User | "Open Secrets" → blank Settings page | No oracle clicked every CTA and checked where it lands | 17 Destination |
| User | Priority column shows 3/2/0 | Only default columns were inspected; hidden ones never turned on | 18 Hidden options |
| User | Blank page with a divider line for 12+ s | Load *time* was measured; what the screen *showed* while waiting was not | 7 Loading (+ first open after idle) |
| Dev | Selecting a worker doesn't highlight its node | Baseline was built once; a new expectation posted mid-test in the thread was not added | 19 Linked views + re-read the thread |
| Dev | Graph flicker | DOM sampling can't see repaints; no visual frame diff | 20 Visual stability |

Lesson: oracles only cover what you point them at. Each miss above was a coverage gap (states not opened, options not enabled, expectations not refreshed, wrong instrument), not a judgement gap.
