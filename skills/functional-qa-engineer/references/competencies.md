# QA competency baseline

What a QA engineer does. **Default scope (always): §1 planning, §2 test design, §3 functional/UI-UX/exploratory/edge/negative, §13 defect management, §14 regression and automation, §15 release recommendation.** **Optional (only when the user asks): §4 API, §5 security, §6 performance, §7 accessibility, §8 compatibility, §9 i18n, §10 reliability, §11 data/migration** — list them as out of scope in the plan otherwise. This is the top-down model of the role; project lessons (knowledge graph) layer on top of it. At the start of every engagement, walk this list and put each applicable area into the plan; for each area you skip, write "N/A because …" in the plan. Based on the ISTQB Advanced syllabi (test analysis, technical test analysis, test management) plus practice.

## 1. Plan before testing
- Scope and out-of-scope (say what you will *not* test and why).
- Risks: likelihood × impact per area (test-design.md §9); depth follows risk, breadth follows the coverage gate.
- Entry criteria: build deployed and identified, test data ready, accounts/permissions, environment reachable.
- Exit criteria: coverage gate 100%, no open Critical, Highs accepted by the owner, regression of fixed bugs done.
- Environments and test data: what's real, what's seeded, what gets cleaned up.
- Smoke test first (can the main job be done at all?) before deep testing; stop and report if it fails.

## 2. Test design (always)
All of `references/techniques.md`: EP, BVA, syntax, decision tables, state transitions, pairwise, classification tree, scenarios, CRUD matrix, error guessing — generated with `scripts/testgen.py`.

## 3. Functional, UI/UX, exploratory, edge, negative
`references/test-design.md` §1–5.

## 4. API testing (whenever there is an API, even if "UI only")
- Status codes for success, validation error, auth error, not found, conflict, server error; error body format consistent and readable.
- Schema/contract: required fields, types, nullability; unknown fields ignored or rejected consistently.
- Limits match the UI (round-trip at limit/limit+1 through the API directly).
- Idempotency and double submit (same POST twice, retry after timeout).
- Pagination, sorting, filtering: first/last page, empty page, page size limits, stable ordering.
- The UI's checks are re-checked server-side (bypass the UI once) — then rate severity by reachability (oracle 21).

## 5. Security (basic, every feature)
- AuthN/AuthZ: another user/org can't read or change your entities by ID (IDOR); role differences enforced server-side.
- Input handling: XSS-shaped strings in every text field render as text everywhere they appear (lists, drawers, activity, exports); injection-shaped input doesn't break queries.
- Secrets: never in URLs, page source, logs, evidence, screenshots, activity; masked in UI; redacted in captured requests.
- Session: expired session handled; actions not replayable across users; CSRF on state-changing requests where cookies are used.
- Out of scope unless asked: penetration testing, DoS, anything destructive to shared systems.

## 6. Performance (perceived and basic measured)
- Perceived: what the screen shows while loading (loading_sweep.js), first open after idle, throttled network.
- Measured: API p50/p95 for the main calls (time 10–20 requests), page load to content, behaviour with large data (many pages/results/rows), repeated actions, long-running pages (memory/timers after 30 min).
- Out of scope unless asked: load/stress testing against shared environments.

## 7. Accessibility
- Contrast in light and dark (contrast_scan.js).
- Keyboard only: every action reachable, visible focus, logical order, Escape closes dialogs, no focus traps.
- Screen-reader names: buttons, icons, inputs and status changes announced (aria-label / role=status).
- Zoom 200% and narrow width without lost content.

## 8. Compatibility
- Browsers the product supports (state which were tested; if told "Chrome only", record the others as out of scope).
- Viewports: desktop, small laptop, narrow; OS-specific behaviour if relevant.

## 9. Internationalisation
- Time zones (timestamps, "today/yesterday", durations across midnight), date and number formats, long translated strings, non-Latin input.

## 10. Reliability and recovery
- Refresh, back button, closing the tab mid-action; network drop and return; dependency outage mid-run; retries; timeouts; partial failure keeps completed work (oracle 6).

## 11. Data integrity and migration
- Existing data created before the change still displays and works (old runs, old notes, old states).
- Nothing silently truncated, duplicated or dropped; counts consistent (oracles 1, 4).

## 12. Observability
- Failures leave enough in logs/job output to diagnose; IDs in the UI let a dev find them (run, job, request).

## 13. Defect management
- Severity (impact) vs priority (urgency) both stated; duplicates merged; root cause labelled as hypothesis unless proven; one bug per card; filed where the team tracks work when asked (e.g. Jira) with repro, evidence and IDs.

## 14. Regression and automation
- Regression: main flow + bug-by-bug re-run after every deploy (test-design.md §6).
- Recommend which cases to automate as regression tests (stable, high-value, deterministic) and, where the team uses it, generate them (e.g. via a test-generation CLI or skill).

## 15. Release recommendation
- Go / No-go / Go with conditions, against the exit criteria, with the open risks named. Never "looks good" without the coverage line.
