# Provider-agnostic cross-model verifier (PR #453 reframe)

**Issue/PR:** reworks external PR #453 (`kzccIneko:feat/openai-compatible-cross-model`)
**Date:** 2026-06-16
**File touched:** `shared/cross_model_verification.md` + `scripts/check_cross_model_verification_sync.py` + `scripts/test_check_cross_model_verification_sync.py`
**Status:** design approved, pre-implementation

## Problem

The cross-model verification layer hardcodes the verifier endpoint to `api.openai.com`, and the model-detection `case` statement only recognises `gpt-5.*` / `gemini-*`. Researchers without an OpenAI account but with access to an OpenAI-Chat-Completions-compatible provider (Xiaomi MiMo, DeepSeek, or a self-hosted endpoint) cannot use the cross-model layer at all. The intent is legitimate: make the verifier **provider-agnostic** for any endpoint speaking the OpenAI Chat Completions protocol.

The contributor's PR delivers this intent but, read as **actual diff** (not PR prose), introduces three real defects confirmed by an independent codex review (REWORK verdict):

- **P1 — laundering:** the compatible path emits the model's raw `VERIFIED` text with no grounding trace and no downgrade, so an ungrounded from-memory verdict can be counted as an agreement in the integrity results table. This violates the protocol's load-bearing invariant (grounding evidence, not prompt wording, is the safety boundary).
- **P1 — passive downgrade:** the detection logic routes any model id to `openai_compatible` whenever the **standard SDK env var** `OPENAI_BASE_URL` is set. Existing GPT users who set `OPENAI_BASE_URL` for an Azure/proxy/local route get silently downgraded from grounded first-party OpenAI to ungrounded Chat Completions. Behaviour changes for users who never opted in.
- **P2 cluster:** documented endpoints build to `…/v1/v1/chat/completions` (double `/v1`); the setup guide exports `OPENAI_API_KEY` twice and leaves a misleading `gpt-5.5`; the compatible prompt collapses `NOT_SEARCHED` into `NOT_FOUND`; the Integrity section and the new compatible section contradict each other on the guard.

## Security invariant (must hold after this change)

A cross-model `VERIFIED` verdict counts as agreement **only** when backed by API-level grounding evidence (OpenAI `web_search_call` / Gemini `groundingMetadata`). Compatible providers have no hosted web-search tool, so they can never produce that evidence. Therefore: **compatible-provider verdicts are never counted as grounded agreement in citation verification.** The line is drawn on the "needs grounding?" axis, not the "is it compatible?" axis — so a compatible provider is a first-class verifier for tasks that don't need grounding (Devil's Advocate critique) and a non-confirming voice for tasks that do (citation existence).

**Producer/consumer split (dual-track review, 2026-06-16).** Holding the invariant requires pinning BOTH ends, not just the producer. The producer (handler) emits a normalized machine-readable status; the consumer (agreement counting) must read ONLY that normalized status, never the raw model text. The compatible provider's raw text must never land in a verdict column or any parseable verdict slot — otherwise a raw `VERIFIED` substring leaks back into the agreement count even though the status field says `NOT_SEARCHED`. The behavioral fixture that proves this (compatible returns `VERIFIED` → final agreement count is 0) is the load-bearing test, more than any doc-string lint.

## Design

### D1 — Explicit opt-in via `ARS_OPENAI_COMPAT_BASE_URL`

A dedicated, ARS-namespaced env var both signals opt-in and supplies the endpoint. The standard `OPENAI_BASE_URL` is **never** read by the detection or call logic — removing the PR's passive `OPENAI_BASE_URL`-triggered downgrade is the fix for the P1 passive-downgrade defect.

**Precedence: first-party recognized model ids always win the grounded route.** Detection `case` after change, in order:

- `gpt-5.5*|gpt-5.4*` → `openai` (grounded; key check unchanged) — **even if `ARS_OPENAI_COMPAT_BASE_URL` is set.**
- `gemini*` → `google` (grounded; key check unchanged) — likewise.
- `*)` catch-all (an otherwise-unrecognized model id) → if `ARS_OPENAI_COMPAT_BASE_URL` is set **and** `ARS_OPENAI_COMPAT_API_KEY` is set (see D6) → `openai_compatible`; else warn + `none`. **No `OPENAI_BASE_URL` branch.**
- The `mimo*|deepseek*` prefixes from the PR are dropped as load-bearing routing — they're documented as *examples* of compatible model ids, but routing is governed solely by `ARS_OPENAI_COMPAT_BASE_URL` (so "any self-hosted OpenAI-compatible endpoint", the broadest case the contributor wanted, works without a prefix allowlist to maintain).

**The explicit precedence trade-off (dual-track review divergence, resolved toward safety).** The two reviewers split here: one flagged "first-party-first" as a bug that locks out a user running `gpt-5.5` through a LiteLLM/proxy; the other flagged "compat-first" as the real hazard, because a recognized first-party model id silently routed to the ungrounded compatible path is a grounded→ungrounded **downgrade** — the exact regression class this rework exists to kill. We choose first-party-first: a recognized `gpt-*`/`gemini-*` id never loses its grounding guard to an opt-in env var. The cost is acknowledged and documented: a user who wants to verify *through* a compatible proxy must name the model with an id that does not match a first-party prefix (the proxy's own model id), not `gpt-5.5`. First-party grounded verification through `OPENAI_BASE_URL`-style proxies is a separate, currently-absent feature (see Follow-up), not this PR's job.

### D2 — Compatible verdicts: only `VERIFIED` is downgraded; rejections pass through

When `CROSS_MODEL_AVAILABLE=openai_compatible`, the citation-verification call:

- builds the endpoint as `endpoint="${ARS_OPENAI_COMPAT_BASE_URL%/}/chat/completions"` (base URL is the API root including `/v1`; trailing slash normalised — fixes double-`/v1`).
- on transport failure (non-2xx / curl 000) → `CROSS-MODEL-ERROR: openai_compatible_http_<code>` (unchanged contract: transport error ≠ NOT_SEARCHED).

**Selective normalization (not a blanket downgrade).** The first spec draft downgraded *every* compatible verdict to `NOT_SEARCHED`. That was too blunt — the invariant only forbids an ungrounded *positive* confirmation; it says nothing about rejections. A compatible model that correctly flags a hallucinated paper as `NOT_FOUND`/`MISMATCH` produces a **valid disagreement** worth keeping; throwing it away forces needless human review of a hallucination the model already caught. So the handler normalizes by verdict:

- model says `VERIFIED` → **downgrade to `NOT_SEARCHED`** (no grounding trace to evidence the positive claim; an ungrounded confirmation can never count as agreement — the existing line-127 rule "VERIFIED with no source → NOT_SEARCHED" applies, intensified here because no source channel exists at all).
- model says `NOT_FOUND` / `MISMATCH` → **pass through unchanged** as a disagreement (a rejection needs no grounding evidence to be useful; it is surfaced for human review either way).
- model says `NOT_SEARCHED` or returns unparseable text → `NOT_SEARCHED`.

**Producer/consumer contract (the load-bearing part).** The handler emits exactly ONE machine-readable normalized status. The compatible model's raw text is NOT placed in the verdict column or any slot the agreement counter parses; if shown at all it is in a clearly-labelled context/notes field the counter ignores. Agreement counting consumes only the normalized status. This closes the leak where a raw `VERIFIED` substring (e.g. `NOT_SEARCHED\nraw: VERIFIED`) is re-grepped into the agreement total. The behavioral fixture in D5 proves: compatible returns `VERIFIED` → normalized status `NOT_SEARCHED` → grounded-agreement count increments by 0.

This holds the invariant with the minimal change: it reuses the existing `NOT_SEARCHED` channel (no new status enum), keeps genuinely useful rejections, and a compatible provider still appears in the results table without a positive verdict being laundered into a confirmation.

### D3 — Task scope: citation downgraded, DA equivalent *for critique only*, peer-review untouched

- **Citation existence verification** (Stage 2.5/4.5): compatible → handled per D2.
- **Devil's Advocate critique** (deep-research + academic-paper-reviewer): compatible is a **first-class verifier for idea generation and critique** — surfacing weaknesses, alternative framings, and attack angles needs no web grounding, so DeepSeek/MiMo findings are used like GPT/Gemini findings *at that layer*. **But "first-class" is scoped to critique, not factual adjudication.** An ungrounded model can invent missing literature, assert a methodological flaw resting on a false fact, or fabricate a policy constraint. So the contract narrows: a DA finding from **any** provider (compatible or first-party) is an adversarial hypothesis, never standalone evidence, unless it carries an independently-checkable source. The spec wording in the DA section must state this explicitly so a compatible-provider DA "finding" is not mistaken for a verified defect. The DA section already routes through the shared "API Call Patterns"; no DA agent file hardcodes an endpoint (verified by grep), so no agent file changes.
- **Peer-review sixth reviewer:** remains `Planned, not yet implemented`. Out of scope for this change.

### D4 — Setup guide: mutually exclusive provider blocks

Replace the single copy-paste block (which exports `OPENAI_API_KEY` twice and leaves a misleading `gpt-5.5`) with three mutually exclusive examples, each a complete self-consistent tuple:

- **OpenAI (first-party, grounded):** `OPENAI_API_KEY` + `ARS_CROSS_MODEL=gpt-5.5`.
- **Gemini (first-party, grounded):** `GOOGLE_AI_API_KEY` + `ARS_CROSS_MODEL=gemini-3.1-pro-preview`.
- **OpenAI-compatible (ungrounded):** `ARS_OPENAI_COMPAT_API_KEY=<provider key>` + `ARS_OPENAI_COMPAT_BASE_URL=https://api.deepseek.com/v1` (or MiMo / self-hosted) + `ARS_CROSS_MODEL=<provider model id, not gpt-*/gemini-*>`, with a one-line note that this path is ungrounded (positive verdicts never count as citation-agreement confirmations) and that the model id must not collide with a first-party prefix (per D1 precedence).

The Supported Models table keeps the compatible row but states the ungrounded boundary in the table itself (not only in a footnote that the Integrity section can contradict).

### D5 — Verification: behavioral fixtures first, lint second

Both reviewers landed on the same correction: the load-bearing proof is **behavioral** (does an ungrounded `VERIFIED` reach the agreement count?), not a doc-string lint (does the block contain the word `NOT_SEARCHED`?). So the verification has two tiers, behavioral first.

**Tier 1 — behavioral fixtures (the real guard).** Drive the documented handler logic against canned compatible-provider responses and assert the normalized output + agreement effect:

1. compatible returns `VERIFIED` (with a plausible-looking DOI) → normalized status `NOT_SEARCHED`, grounded-agreement count increments by 0, raw `VERIFIED` text appears in no parseable verdict slot.
2. compatible returns `NOT_FOUND` → passes through as a disagreement (not silently dropped).
3. compatible returns `MISMATCH` → passes through as a disagreement.
4. base URL with a trailing slash → endpoint has exactly one `/chat/completions` and no `/v1/v1`.

These mirror the existing canonical-jq behavioral tests (`test_cross_model_verification_guards.py`): extract the handler's verdict-normalization into a small testable unit so the fixtures run in CI, rather than asserting against prose.

**Tier 2 — doc-sync lint (regression backstop, narrowed).** Extend `check_cross_model_verification_sync.py` to pin, against **executable bash only** (the lint already strips comments/prose via `_bash_code_lines` + `_strip_trailing_comment`):

1. **Compatible downgrade present:** the compatible block's executable bash references `NOT_SEARCHED`.
2. **No passive base-url downgrade:** no executable *assignment or expansion* of `OPENAI_BASE_URL` in the detection/call blocks — match `OPENAI_BASE_URL=` and `${OPENAI_BASE_URL` patterns, not a raw substring anywhere (so explanatory prose/comments like "we deliberately do not read `OPENAI_BASE_URL`" don't false-fail, and `${OPENAI_BASE_URL:-…}` variants don't false-pass).
3. **Endpoint normalised:** executable bash constructing the compatible endpoint contains no literal `/v1/v1` and no hardcoded `api.openai.com` fallback.

Mutation discipline (per prior linter-mutation lessons): commit working tree before mutating; align mutation string case with the lint's matching (avoid IGNORECASE false-greens); each new check gets a red-then-green mutation proving it fails when the contract is broken.

### D6 — Credential isolation: `ARS_OPENAI_COMPAT_API_KEY`

The compatible path must NOT reuse `OPENAI_API_KEY` as its bearer token. A user who sets `ARS_OPENAI_COMPAT_BASE_URL=https://api.deepseek.com/v1` but still has a real, billing-enabled `OPENAI_API_KEY` in their environment would otherwise send that OpenAI key in the `Authorization` header to a third-party endpoint — a real credential-leak across a trust boundary. The compatible call uses a dedicated `ARS_OPENAI_COMPAT_API_KEY`:

- detection's `openai_compatible` branch requires `ARS_OPENAI_COMPAT_API_KEY` (not `OPENAI_API_KEY`) to be set; missing → warn + `none`.
- the compatible curl uses `Authorization: Bearer $ARS_OPENAI_COMPAT_API_KEY`.
- `OPENAI_API_KEY` is sent only to `api.openai.com` (the grounded first-party path), never to a compatible endpoint.

This is the same trust-boundary class as the prior path-fix POSIX side-effect lesson: fixing one defect (passive downgrade) must not silently open another (key egress to an untrusted host).

## Out of scope

- Peer-review sixth reviewer (stays planned).
- Any new status enum beyond the existing `NOT_SEARCHED` (decision A in brainstorm: reuse, don't invent).
- DA agent file edits (no hardcoded endpoint exists; grep-verified).
- Grounding for compatible providers (structurally impossible; not a goal).
- First-party grounded verification *through* an `OPENAI_BASE_URL`-style Azure/proxy (see Follow-up).

## Follow-up (separate issue, not this PR)

The dual-track review surfaced a genuine pre-existing gap: ARS has no way to run **grounded first-party OpenAI** verification through an enterprise proxy / Azure endpoint. This predates PR #453 (the original code hardcodes `api.openai.com`) and is a distinct feature, not a regression introduced here. File it as its own enhancement issue; do not bundle it into this rework. The D1 precedence note documents the current limitation for users.

**Altitude follow-up (from the /simplify altitude review, 2026-06-16).** The first-party blocks use a *canonical-and-referenced* pattern: the grounding logic lives in `.jq` files the doc bash **executes** via `jq -f`, so there is one definition, no drift, and no parity-lint needed. The compatible block instead **inlines** the normalization in bash while `normalize_compat_verdict.py` is referenced only in comments (never executed) — which is why lint check 8 (token-set parity) and check 5's literal-endpoint block-locator exist at all. The deeper altitude: have the compatible bash *call* `python3 normalize_compat_verdict.py` (the way other blocks call their `.jq`), making the Python canonical, letting the behavioral test cover the executed path, and dissolving check 8 + check 5's fragility. Deferred, not done in this PR, because it adds a `python3` runtime assumption to a call path that currently needs only curl+jq+grep (jq is already in the first-party path; python3 in the verdict-parse step is new surface for agents running the bash in varied environments). Worth a separate issue weighing the python3-in-call-path cost against the canonical-unit win.

## Adoption

Local rebuild (not fetch+cherry-pick of the fork) per repo fork-PR discipline: a single commit on a feature branch off `main`, carrying `Co-Authored-By: kzccIneko`. Then a courteous PR reply crediting the contributor and stating the provider-agnostic intent was adopted with a grounding-aware reshaping — without dissecting their diff line by line.

## Files

| File | Change |
|------|--------|
| `shared/cross_model_verification.md` | D1 precedence rewrite, D2 selective normalization + producer/consumer contract, D3 DA critique-only scope, D4 setup guide, D6 credential isolation, contradiction cleanup |
| `scripts/check_cross_model_verification_sync.py` | D5 Tier-2 three narrowed contract checks (executable-bash only) |
| `scripts/test_check_cross_model_verification_sync.py` | D5 Tier-2 mutation tests (red-then-green per check) |
| `scripts/cross_model_verification/` + a new behavioral test | D5 Tier-1 verdict-normalization unit + fixtures (compatible `VERIFIED`→`NOT_SEARCHED`, agreement 0; `NOT_FOUND`/`MISMATCH` pass-through; endpoint normalization) |
