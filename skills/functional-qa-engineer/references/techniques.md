# Test design techniques (black-box)

How to derive test cases systematically. `scripts/testgen.py` computes the values for the mechanical ones (boundaries, partitions, pairwise, state transitions) so they are not improvised. Every technique here maps to a mandatory check in the knowledge graph, so the coverage gate asks for it.

## Contents
1. Equivalence partitioning (EP)
2. Boundary value analysis (BVA)
3. Syntax / format testing
4. Decision tables (cause–effect)
5. State-transition testing
6. Pairwise / combinatorial testing
7. Classification tree
8. Use-case / scenario testing
9. CRUD matrix
10. Error guessing
11. Checklist-based and risk-based testing
12. Which technique for which surface

---

## 1. Equivalence partitioning (EP)
Split each input (and output) into classes the product should treat the same; test one representative per class, valid **and** invalid.
- Derive classes from the spec, the UI copy, validation messages and the API schema.
- Always include: valid typical, each distinct valid sub-type, each invalid reason as its own class (wrong type, wrong format, out of range, empty, forbidden value).
- One invalid class per test case (don't combine two invalid inputs, or you won't know which one was rejected).
**Example (Application URL):** valid `https://` · valid `http://` · uppercase scheme `HTTPS://` · localhost · IP · with path/query · invalid: no scheme, `ftp://`, spaces, `javascript:`, empty.

## 2. Boundary value analysis (BVA)
Bugs cluster at edges. For every ordered input (length, number, count, date, size, time limit), test at and around each boundary.
- **3-value BVA** per boundary: just below, on, just above (min−1, min, min+1, max−1, max, max+1).
- Add: empty / zero, one, maximum the UI allows vs the API allows (they often differ), and the type's own limits (int overflow, very large).
- For text: count in the unit the product counts (characters vs bytes vs UTF-16 units); test a multi-byte character exactly at the boundary.
- Check the boundary in **UI and API** and after **reload** (round-trip).
**Examples:** note limit 10,000 → 9,999 / 10,000 / 10,001 (UI counter, API 422, read-back length) — this found the UI-at-10k / API-cut-at-2k silent truncation; run limit 1 / 0 / blank ("no limit") / 20 / 21; concurrency 0, 1, 20, 21.

## 3. Syntax / format testing
For structured inputs (URLs, domains, emails, variables like `{{NAME}}`, paths, JSON), test the grammar: each valid production once, then each kind of malformation — missing part, extra part, wrong delimiter, wrong case, unicode look-alikes, leading/trailing whitespace, injection-shaped strings (`<script>`, `'; --`, `../`).
**Example:** `{{API_KEY}}`, `{{ API_KEY }}`, `{{API_KEY}`, `{{global.X}}`, `${param}` (unsupported), an undefined variable.

## 4. Decision tables (cause–effect)
When the outcome depends on a combination of conditions, list conditions as rows, enumerate combinations as columns, write the expected action for each, then collapse columns whose conditions don't matter ("–").
**Example (can Start be pressed?):** conditions = variable secrets present · account login available · tunnel needed · tunnel running · run already active. Each column has one expected outcome (enabled / disabled with which message / refused with which error). This is how the "refused start but Start enabled" gap shows up.

## 5. State-transition testing
Model the entity's lifecycle as states and events. Cover:
- **every valid transition** at least once (0-switch coverage);
- **every pair of consecutive transitions** for critical paths (1-switch), e.g. stop → re-run → cancel;
- **invalid transitions**: each event in each state where it shouldn't be allowed (delete while running, stop when stopped, re-run while queued) — the UI must block it and the API must refuse it;
- what the UI shows **in** each state and **during** each transition (Stopping…, Cancelling…).
`testgen.py states` prints the transition and invalid-event lists from a simple spec.
**Example states:** empty → queued → claimed → running → stopping → stopped | completed | limit-reached | failed | cancelled | didn't-start.

## 6. Pairwise / combinatorial testing
When many parameters each have a few values, test every **pair** of values at least once instead of every combination (most interaction bugs involve two factors). `testgen.py pairwise` builds a small all-pairs set.
**Example parameters:** policy {allow, read-only} × concurrency {1, 3} × sign-in {none, steps} × tunnel {no, yes} × actor {owner, other} × entry {UI, CLI} → 64 combinations, ~8–10 pairwise cases. Add the known-risky full combinations on top (e.g. other user + tunnel + secrets).

## 7. Classification tree
For complex inputs, draw the input as a tree of classifications (each with its EP classes), then pick combinations: minimum (every class once), pairwise, or full for critical branches. Good for setup forms with many sections.

## 8. Use-case / scenario testing
Write end-to-end scenarios from the user's goal, including the main flow, alternative flows and exception flows, with real data. Each scenario crosses many screens and is where integration bugs live (UI-started job that signs in, runs 20 min, then one worker fails).

## 9. CRUD matrix
For every entity (job, run, note, label, keyword, secret…) × operation (create, read, update, delete) × surface (UI, API, CLI): is it possible, is it correct, is it reflected everywhere, does it survive reload, is it permission-checked? Empty cells are either missing features or untested paths.

## 10. Error guessing
Use the knowledge graph (`kb.py misses`) and the bug history of this product as a list of likely faults: failed states that blame the wrong step, partial failures that erase work, UI ahead of API limits, raw codes, hidden options with raw values, buttons that go to the wrong page, blank loads after idle, flicker on refresh.

## 11. Checklist-based and risk-based testing
- *Checklist:* the coverage matrix's mandatory checks are the checklist; nothing is signed off until they're all done.
- *Risk-based:* rank areas by likelihood × impact (see test-design.md §9) and spend depth there first — but the coverage gate still requires breadth everywhere.

## 12. Which technique for which surface

| Surface | Techniques (mandatory checks) |
|---|---|
| form-field | EP + BVA + syntax/format + round-trip |
| combined settings | decision table + pairwise |
| run-state / lifecycle | state transitions incl. invalid events |
| entity (job, note, label…) | CRUD matrix |
| end-to-end flows | use-case scenarios (main, alternative, exception) |
| everything | error guessing from the knowledge graph |
