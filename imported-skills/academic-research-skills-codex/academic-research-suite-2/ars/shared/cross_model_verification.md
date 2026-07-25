# Cross-Model Verification Protocol (v3.0)

## Overview

This protocol enables optional cross-model verification for high-stakes AI judgments. When enabled, a second AI model independently reviews outputs from the primary model, reducing shared-bias blind spots.

**This is entirely optional.** All ARS skills work with the primary Claude model alone. Cross-model verification is an additional layer for users who want higher confidence in integrity checks, devil's advocate challenges, and review judgments.

**Consent boundary:** Before unpublished manuscripts, private notes, corpus text,
reviewer comments, decision letters, response letters, or other review material
is sent to an external provider, the agent must identify the provider, model,
and content class that would be sent, then obtain explicit user consent. An
environment variable alone is not consent to upload user content. If consent is
not granted, continue with single-model verification.

## Why Cross-Model Verification

A stress test of 68 AI-generated citations found 31% had problems — and all passed three rounds of same-model integrity checks. The root cause: the verifying AI and the generating AI share the same training data distribution, so they share the same blind spots. A different model (trained on overlapping but not identical data, with different RLHF tuning) can catch errors that the primary model systematically misses.

**What it improves:** Error rate reduction (estimated 31% → ~5-10%). Different models catch different types of hallucination patterns.

**What it doesn't solve:** Frame-lock (all LLMs share most training data), sycophancy (all RLHF models have this tendency). These are degree improvements, not kind improvements.

## Supported Models

| Model | API ID | Provider | Best For |
|-------|--------|----------|----------|
| Claude (session model) | _(inherited Claude Code session model — e.g., Fable 5)_ | Anthropic | Primary model (default for all ARS skills) |
| GPT-5.5 | `gpt-5.5` | OpenAI | Cross-verification — recommended balance (supports `xhigh` reasoning) |
| GPT-5.5 Pro | `gpt-5.5-pro` | OpenAI | Cross-verification — strongest reasoning (premium pricing: ~6× GPT-5.5) |
| GPT-5.6 Sol | `gpt-5.6-sol` | OpenAI | Cross-verification — frontier tier, **provisional pending ARS validation** (same standard rates as GPT-5.5) |
| Gemini 3.1 Pro | `gemini-3.1-pro-preview` | Google | Cross-verification — strong at factual verification |

### OpenAI-compatible providers (Chat Completions API — UNGROUNDED, opt-in)

| Provider | Example API ID(s) | Endpoint (`ARS_OPENAI_COMPAT_BASE_URL`) | Notes |
|----------|-------------------|------------------------------------------|-------|
| Xiaomi MiMo | `mimo-v2.5-pro` | `https://token-plan-cn.xiaomimimo.com/v1` | Set `ARS_OPENAI_COMPAT_API_KEY` + `ARS_CROSS_MODEL`. Ungrounded: positive verdicts never count as citation agreement. |
| DeepSeek | `deepseek-v4-pro` | `https://api.deepseek.com/v1` | Set `ARS_OPENAI_COMPAT_API_KEY` + `ARS_CROSS_MODEL`. Ungrounded. |
| Any OpenAI-compatible | any non-`gpt-*`/`gemini-*` id | any `/v1/chat/completions` endpoint | Routing is governed solely by `ARS_OPENAI_COMPAT_BASE_URL`; the model id must NOT match a first-party prefix or it takes the grounded first-party route instead. |

> **Compatible providers are ungrounded.** They expose no hosted web-search tool, so there is no grounding evidence behind a verdict. A positive `VERIFIED` is downgraded to `NOT_SEARCHED` and never counts as agreement in citation verification; a `NOT_FOUND`/`MISMATCH` survives as a disagreement. They ARE first-class for Devil's Advocate critique (which needs no grounding) — but a DA finding from any provider is an adversarial hypothesis, not standalone evidence, unless independently sourced.

**Recommended cross-verification pair:** the inherited Claude session model (primary) + GPT-5.5 or Gemini 3.1 Pro (verifier).

> The primary row deliberately names no version: the primary is always the session model, so the row cannot go stale on the next Anthropic release. Verifier IDs stay concrete because they are literal API strings the user must export. (`gpt-5.4` / `gpt-5.4-pro` remain accepted for existing setups.)

> **GPT-5.6 Sol is provisional (listed 2026-07-11, three days after release).** Its endpoint support (Responses API), hosted `web_search` tool, and reasoning-effort values are confirmed against OpenAI's model documentation, but its ARS-specific behavior — grounded-search completion rate, citation-mismatch recall, false-disagreement rate, response-shape stability against the jq grounding guards, p95 latency — is unvalidated. **GPT-5.5 remains the recommended default** until `gpt-5.6-sol` passes the § Promotion Bakeoff below (non-inferiority on those measures earns `validated`) AND a separate superiority or operational-benefit case is stated for the default flip; run `scripts/cross_model_smoke_test.sh` against your key before adopting it. Two facts that differ from the GPT-5.5 lineup: GPT-5.6 ships **no `-pro` model ID** — premium operation is standard `gpt-5.6-sol` plus `reasoning: {mode: "pro"}` in the request, billed at standard token rates with more model work per request (the old fixed ~6× unit-price split does not carry over); and its reasoning effort accepts `none|low|medium|high|xhigh|max` (GPT-5.5 tops out at `xhigh`), defaulting to `medium` in both standard and pro modes.

Using two non-Anthropic models as primary+verifier is possible but not tested with ARS prompts.

## Setup Guide

### Prerequisites

You need API keys from at least one additional provider. ARS itself runs inside Claude Code, so Claude is always available as the primary model.

### Step 1: Get API Keys

**OpenAI (GPT-5.5 / GPT-5.6 Sol):**
1. Go to [platform.openai.com/api-keys](https://platform.openai.com/api-keys)
2. Create a new API key
3. Copy the key (starts with `sk-`)

**Google (Gemini 3.1 Pro):**
1. Go to [aistudio.google.com/apikey](https://aistudio.google.com/apikey)
2. Create a new API key
3. Copy the key (starts with `AIza`)

**OpenAI-compatible providers (MiMo / DeepSeek / self-hosted):**
1. Get an API key from your provider (e.g. [platform.deepseek.com](https://platform.deepseek.com) or the Xiaomi MiMo platform)
2. Note the provider's API root including `/v1` (e.g. `https://api.deepseek.com/v1`)
3. The key goes in `ARS_OPENAI_COMPAT_API_KEY` and the endpoint in `ARS_OPENAI_COMPAT_BASE_URL` — NOT in `OPENAI_API_KEY`/`OPENAI_BASE_URL` (your real OpenAI key is never sent to a third-party endpoint)
4. The compatible model id (`ARS_CROSS_MODEL`) must NOT begin with a `gpt-` or `gemini-` prefix. Any such id is claimed by the first-party grounded route, so a self-hosted compatible model named that way would be routed to the (unavailable) first-party path instead of your compatible endpoint.

### Step 2: Set Environment Variables

Add to your shell profile (`~/.zshrc` or `~/.bashrc`):

```bash
# Cross-model verification for ARS — pick exactly ONE provider tuple.

# --- Option A: OpenAI (first-party, grounded) ---
export OPENAI_API_KEY="<your-openai-api-key>"
export ARS_CROSS_MODEL="gpt-5.5"
# Frontier alternative, provisional pending ARS validation (see Supported Models):
# export ARS_CROSS_MODEL="gpt-5.6-sol"
# Optional: reasoning effort for OpenAI verifier calls (unset = the provider's own
# default for the chosen model). GPT-5.6 accepts none|low|medium|high|xhigh|max;
# GPT-5.5 tops out at xhigh.
# export ARS_CROSS_MODEL_REASONING_EFFORT="medium"

# --- Option B: Google Gemini (first-party, grounded) ---
export GOOGLE_AI_API_KEY="<your-google-ai-api-key>"
export ARS_CROSS_MODEL="gemini-3.1-pro-preview"

# --- Option C: OpenAI-compatible provider (MiMo / DeepSeek / self-hosted) — UNGROUNDED ---
# Uses a DEDICATED key; your real OPENAI_API_KEY is never sent to a third-party endpoint.
export ARS_OPENAI_COMPAT_BASE_URL="https://api.deepseek.com/v1"   # API root incl. /v1
export ARS_OPENAI_COMPAT_API_KEY="<your-provider-api-key>"
export ARS_CROSS_MODEL="deepseek-v4-pro"                          # provider id, NOT gpt-*/gemini-*
```

Then reload: `source ~/.zshrc`

### Step 3: Verify Setup

In Claude Code, you can test by asking:
```
Check if cross-model verification is available for ARS
```

The system will check for the environment variables and report which models are available.

### Step 4: Enable Per-Session (Optional)

If you don't want cross-model verification running all the time, you can enable it per session:

```bash
# Enable for this session only
export ARS_CROSS_MODEL="gpt-5.5"

# Disable for this session
unset ARS_CROSS_MODEL
```

## How It Works in Each Skill

### Integrity Verification (academic-pipeline, Stage 2.5 / 4.5)

**When `ARS_CROSS_MODEL` is set:**
- Primary model (Claude) runs full Phase A-E verification as normal
- After Phase A completes, a **risk-stratified** selection of references is sent to the cross-model for independent verification (see step 2 below; replaces the pre-#518 uniform random 30%)
- Cross-model receives only the reference text and paper context — not Claude's verification result (to prevent anchoring)
- Disagreements are flagged as `[CROSS-MODEL-DISAGREEMENT]` and prioritized for human review

**When `ARS_CROSS_MODEL` is not set:**
- Standard single-model verification (unchanged from v2.7+)

**Implementation for agents:**

When the integrity_verification_agent detects `ARS_CROSS_MODEL` in the environment, it should:

1. Complete Phase A verification normally
2. Select references by **risk stratification** (#518; replaces uniform random 30%). Classify each reference at selection time and record the tier in the results table. Four tiers; a reference qualifying for more than one is classified once at the highest tier that applies (precedence: `HIGH-IMPACT` > `NEW-CHANGED` > `CONTROL`/`RANDOM`) and verified once:
   - **HIGH-IMPACT — verify 100%, no cap (both gates).** A reference is high-impact if it supports any of: (a) a headline conclusion (abstract- or conclusions-level claim); (b) a numerical claim (statistic, effect size, percentage, threshold); (c) a causal claim; (d) a methods-critical claim (the validity of the chosen method rests on it); (e) a disputed claim (already carrying a contradiction disclosure or reviewer split).
   - **RANDOM (Stage 2.5 only) — the non-high-impact remainder**, sampled at 10%, rounded up (minimum 3, maximum 10; if the remainder has fewer than 3 references, sample all of it).
   - **NEW-CHANGED (Stage 4.5 only) — verify 100%, no cap:** every reference supporting a claim that is **new or changed** since Stage 2.5, whatever its impact class.
   - **CONTROL (Stage 4.5 only) — the unchanged, non-high-impact remainder**, sampled at 10%, rounded up (minimum 3, maximum 10; fewer than 3 → all of it) to catch silent drift. At Stage 4.5, CONTROL replaces RANDOM — there is no separate RANDOM tier at the final gate.
   - Cost scales with the count of high-impact (and, at Stage 4.5, new/changed) citations instead of total reference count — a results-dense paper approaches 100% coverage, which is the point: verification budget concentrates where the paper's weight rests. The old flat cap (max 15) is retired; only the sampled tiers (RANDOM/CONTROL) carry a cap (max 10 each).
3. Issue **one API call per reference** — not a batch. (Batching hides which reference the model actually grounded: a single grounding-metadata trace on a 5-reference response proves *something* was searched, not that *each* reference was. One reference per call makes the grounding evidence 1:1 with the verdict.) For each reference, construct a verification prompt:
   ```
   Verify this academic reference. Check: Does it exist? Are the author
   names, year, title, journal, and DOI correct? Search the web to
   confirm — do not answer from memory.

   Respond with exactly one verdict:
   - VERIFIED  — found online; include at least one source URL or DOI you found
   - MISMATCH  — found, but a field is wrong (state which); include the source
   - NOT_FOUND — searched, no matching record exists
   - NOT_SEARCHED — you could not actually search the web for this reference

   Reference: [full reference text] — Context: [sentence where cited]
   ```
   A `VERIFIED` verdict with no accompanying source URL/DOI is treated as `NOT_SEARCHED` (the model claimed a result it cannot evidence).
4. Send to the cross-model via the appropriate API (see API Call Patterns below). **For first-party providers the call patterns enable the hosted web-search/grounding tool and reject the response as `NOT_SEARCHED` when the API returns no grounding evidence** — a model that ignores the "search the web" instruction cannot fake an absent grounding trace, so this is the real safety boundary, not the prompt wording. **An OpenAI-compatible provider has no grounding tool, so its positive verdicts are downgraded to `NOT_SEARCHED` by the handler (rejections pass through); a compatible provider therefore never contributes a grounded agreement.**
5. Compare results: if Claude said VERIFIED but cross-model said NOT_FOUND or MISMATCH, flag as `[CROSS-MODEL-DISAGREEMENT]`. Treat `NOT_SEARCHED` / ungrounded exactly as **not verified** — it never counts as agreement with a Claude `VERIFIED`, and a sample that returns `NOT_SEARCHED` is surfaced for re-run or human review, never silently passed.
6. Include disagreements in the integrity report under a new section:
   ```markdown
   ### Cross-Model Verification Results
   - References selected: X/Y (Z%) — HIGH-IMPACT: H (100% of tier), RANDOM: R (Stage 2.5), NEW-CHANGED: N + CONTROL: C (Stage 4.5)
   - Agreements: N
   - Disagreements: M (listed below, prioritized for human review)
   - Ungrounded (NOT_SEARCHED): U (the cross-model could not actually search — these are NOT confirmations; re-run or human-review)

   | # | Reference | Tier | Claude | Cross-Model | Source (URL/DOI) | Status |
   |---|-----------|------|--------|-------------|------------------|--------|
   ```
   The `Tier` column is `HIGH-IMPACT` / `RANDOM` / `NEW-CHANGED` / `CONTROL` per step 2 (one tier per reference, highest-precedence tier wins). The `Source` column carries the URL/DOI the cross-model returned for a `VERIFIED` row; a blank source on a `VERIFIED` verdict downgrades it to `NOT_SEARCHED`.

### Devil's Advocate (deep-research + academic-paper-reviewer)

**When `ARS_CROSS_MODEL` is set:**
- After the DA completes its standard review/checkpoint, the cross-model receives the same material and generates an independent critique
- The DA then compares: any CRITICAL or MAJOR issues found by the cross-model but not by the DA are added as `[CROSS-MODEL-FINDING]`
- This directly addresses frame-lock — a different model may attack from a different angle

> A compatible (ungrounded) provider is first-class for DA critique — surfacing weaknesses and attack angles needs no web grounding. But "first-class" is scoped to critique, not factual adjudication: a DA finding from any provider is an adversarial hypothesis, never standalone evidence, unless it carries an independently-checkable source. Do not treat a compatible-provider DA "finding" as a verified defect.

**When `ARS_CROSS_MODEL` is not set:**
- Standard single-model DA (unchanged)

**Implementation:**

The DA agent, after completing its checkpoint report, should:

1. Send the reviewed material + a simplified DA prompt to the cross-model:
   ```
   You are a devil's advocate reviewing this [research/paper].
   Find the 3 most serious weaknesses. For each, state:
   - What the weakness is
   - Why it matters
   - What the strongest counter-argument would be

   Material: [the reviewed content]
   ```
2. Compare cross-model findings with own findings
3. Any cross-model finding not already covered → add to report as `[CROSS-MODEL-FINDING]`
4. Log: `[CROSS-MODEL: X findings received, Y novel (not in primary DA report)]`

### Blind Disagreement Checkpoints (research-design freeze + final editorial decision)

Two irreversible checkpoints gain an optional cross-model check when `ARS_CROSS_MODEL` is set and the consent gate has been passed:

| Checkpoint | Primary owner | Cross-model input (never the primary's decision) | Structured decision enum |
|---|---|---|---|
| Research-design freeze | `research_architect_agent` (deep-research) | RQ Brief + draft Methodology Blueprint | `sound` / `revise_before_freeze` / `fundamental_concern` |
| Final editorial decision | `editorial_synthesizer_agent` (academic-paper-reviewer) | The panel's usable reviewer cards (all `panel_size` N of them — 5 in the default full-mode panel, 2 under `methodology_focus`) + paper metadata | `accept` / `minor_revision` / `major_revision` / `reject` |

**Mechanics:**

1. The primary reaches its decision as normal and records it in the SAME structured form (the enum + up to 3 drivers) **before** the cross-model is called — both sides commit blind, so the comparison in step 4 is enum-against-enum, not enum-against-prose. Under a sprint contract, the editorial checkpoint runs **after** the mechanical three-step protocol has emitted `editorial_decision` (a post-Step-3 comparison; the contract arithmetic itself is never extended or re-run).
2. The cross-model receives the same input material and a structured-decision prompt. It **never** sees the primary's decision, scores, or reasoning first — the same anchoring-prevention rule as the integrity samples.
3. Output contract: `{decision: <enum>, drivers: [up to 3 one-sentence reasons], confidence: low|medium|high}`.
4. Mechanical comparison: **material divergence = differing enum values.** Adjacent categories (e.g. minor vs major revision) are still material; the report notes adjacency.
5. On divergence: a **targeted rebuttal** — the primary must address each cross-model driver specifically against the evidence already on file (reviewer cards / blueprint content), no generic reassurance. Both decisions and the rebuttal surface to the user. The primary's decision stands unless the **user** changes it: disagreement is a review trigger, never a vote, and the two decisions are never averaged.
6. On agreement: one log line `[CROSS-MODEL-CHECKPOINT: agreement — <checkpoint>]`; both structured decisions are still recorded.
7. Graceful degradation: transport failure → `[CROSS-MODEL-ERROR]`, proceed single-model, note in the report (see § Graceful Degradation).

Checkpoint decisions are judgment, not lookup — an ungrounded/compatible provider is first-class here, with the same scoping as DA critique: a divergence from any provider is an adversarial hypothesis and a review trigger, never a confirmed defect.

> **Why there is no generic "6th reviewer."** An earlier version of this document planned a cross-model 6th reviewer for peer review. That design is retired, not deferred (#518, 2026-07): the conditions under which an extra generic reviewer becomes counterproductive — score averaging, role duplication, findings treated as confirmed defects, majority-vote false confidence, synthesizer context burn — match ARS's documented anti-patterns one-for-one. The blind disagreement checkpoints above are the replacement: cross-model judgment concentrated at the two decisions that are hardest to reverse, compared blind, with divergence escalated to the human instead of blended into a consensus.

## API Call Patterns

Three patterns are documented below. The first two (OpenAI and Gemini) are first-party and share the same contract: enable the provider's hosted web-search tool, and **gate the model's text on proof that a search actually happened** — no grounding evidence (an OpenAI `web_search_call` item / a Gemini `groundingMetadata` block) emits `NOT_SEARCHED` and the text is discarded, so this guard, not the prompt wording, is what prevents a from-memory guess being laundered into `VERIFIED`. Both first-party web-search tools are hosted/server-side: one request, no client-side tool-call round-trip. The third (OpenAI-compatible) is ungrounded by construction: it has no web-search tool, so the handler downgrades positive verdicts to `NOT_SEARCHED` and lets rejections through, and a compatible verdict never counts as a grounded agreement. `PROMPT` holds the single-reference verification prompt from step 3.

### OpenAI (GPT-5.5 / GPT-5.5 Pro / GPT-5.6 Sol)

Use the **Responses API** (`/v1/responses`) — the hosted `web_search` tool lives there. (Chat Completions does not take `tools: [{type: "web_search"}]`; web search on that endpoint requires the separate `gpt-5-search-api` model, so this example targets Responses to stay model-agnostic across `gpt-5.5` / `gpt-5.5-pro` / `gpt-5.6-sol` / the legacy `gpt-5.4*` ids.)

```bash
# PROMPT holds the single-reference verification prompt (step 3). One reference per call.
resp="$(curl -sS -w '\n%{http_code}' https://api.openai.com/v1/responses \
  -H "Authorization: Bearer $OPENAI_API_KEY" \
  -H "Content-Type: application/json" \
  -d "$(jq -n --arg model "$ARS_CROSS_MODEL" --arg prompt "$PROMPT" \
        --arg effort "${ARS_CROSS_MODEL_REASONING_EFFORT:-}" '{
    model: $model,
    instructions: "You are a citation-verification assistant. Search the web before every verdict; never answer from memory. If you could not search, respond NOT_SEARCHED.",
    input: $prompt,
    tools: [{type: "web_search"}],
    temperature: 0.1
  } + (if $effort == "" then {} else {reasoning: {effort: $effort}} end)')")"

http="${resp##*$'\n'}"; body="${resp%$'\n'*}"
# The grounding guard and source extraction are kept as canonical jq filters under
# scripts/cross_model_verification/ so they are behavior-tested in CI (a from-memory verdict, a
# malformed grounding index, etc.) and cannot silently stop failing closed. Reference them via
# `jq -f` rather than inlining, so the doc and the test share one definition.
GUARD=scripts/cross_model_verification
if [ "$http" -lt 200 ] || [ "$http" -ge 300 ]; then
  # Transport/API failure (401/429/5xx, or curl's 000 on a network error) — NOT the same as
  # "searched but found nothing". Surface as a transport error so the consumer falls back to
  # single-model (see § Graceful Degradation); never relabel it NOT_SEARCHED, which would
  # imply a completed-but-ungrounded lookup.
  echo "CROSS-MODEL-ERROR: openai_http_$http"
elif ! jq -e -f "$GUARD/openai_has_completed_web_search.jq" <<<"$body" >/dev/null; then
  echo "NOT_SEARCHED: no_web_search_call"           # no search happened at all — discard the text
else
  # A completed web_search_call proves *a* search ran, not that THIS reference's verdict
  # is supported by it. Emit the verdict text together with the url_citation annotations the
  # model attached; step 5 downgrades a VERIFIED with no citation to NOT_SEARCHED.
  text="$(jq -r -f "$GUARD/openai_text.jq" <<<"$body")"
  cites="$(jq -r -f "$GUARD/openai_sources.jq" <<<"$body")"
  printf '%s\nSOURCES: %s\n' "$text" "${cites:-(none)}"
fi
```

### Google Gemini (Gemini 3.1 Pro)

The hosted grounding tool is `google_search` (REST uses snake_case; the JS SDK's `googleSearch` is the same tool). A grounded response carries `candidates[].groundingMetadata`; its absence means the model did not search.

```bash
# PROMPT holds the single-reference verification prompt (step 3). One reference per call.
resp="$(curl -sS -w '\n%{http_code}' \
  "https://generativelanguage.googleapis.com/v1beta/models/${ARS_CROSS_MODEL}:generateContent?key=$GOOGLE_AI_API_KEY" \
  -H "Content-Type: application/json" \
  -d "$(jq -n --arg prompt "$PROMPT" '{
    contents: [{parts: [{text: $prompt}]}],
    tools: [{google_search: {}}],
    generationConfig: {temperature: 0.1}
  }')")"

http="${resp##*$'\n'}"; body="${resp%$'\n'*}"
# Grounding guard + source extraction are canonical jq filters under scripts/cross_model_verification/
# (same rationale as the OpenAI block: behavior-tested, referenced via `jq -f`). The guard is
# rederived from the source extractor: it passes iff the SAME extraction the source filter performs
# yields at least one url AND the model issued a search (a non-empty webSearchQueries). So
# guard-pass ⟹ a source is extractable — a groundingSupports linking to no valid chunk
# (empty/negative/string/out-of-range/fractional index), the wrong candidate, or a non-string uri
# all leave the extraction blank and fail the guard closed. See the .jq file headers for the full
# contract.
GUARD=scripts/cross_model_verification
if [ "$http" -lt 200 ] || [ "$http" -ge 300 ]; then
  # Transport/API failure (401/429/5xx, or curl's 000) — surface as a transport error so the
  # consumer falls back to single-model (see § Graceful Degradation), not NOT_SEARCHED.
  echo "CROSS-MODEL-ERROR: gemini_http_$http"
elif ! jq -e -f "$GUARD/gemini_is_grounded.jq" <<<"$body" >/dev/null; then
  echo "NOT_SEARCHED: no_grounding_support"           # no search, or text not supported by it — discard
else
  text="$(jq -r '.candidates[0].content.parts[]?.text // empty' <<<"$body")"
  cites="$(jq -r -f "$GUARD/gemini_sources.jq" <<<"$body")"
  printf '%s\nSOURCES: %s\n' "$text" "${cites:-(none)}"
fi
```

> **Why `temperature: 0.1`:** reference existence/metadata checking is a deterministic factual task, so low temperature reduces run-to-run variance in the verdict. It is not a grounding control — the grounding guard above is what enforces an actual lookup.

> **Reasoning effort (OpenAI only):** when `ARS_CROSS_MODEL_REASONING_EFFORT` is set, the payload passes it as `reasoning.effort`, making the effort a verification run uses visible and reproducible. When it is **unset, the field is omitted entirely and the provider's own default for the chosen model applies** — defaults differ across the lineup (GPT-5.6 documents `medium`; other ids carry their own), so forcing one value here would silently change behavior for existing setups. Citation lookup is search-bound, not reasoning-bound, so higher efforts mostly buy latency and cost; set the variable deliberately (never silently run at `xhigh`) if a run shows shallow search behavior. The value is passed through unvalidated (the API rejects unknown values): GPT-5.5 accepts up to `xhigh`, GPT-5.6 adds `max`.

### OpenAI-Compatible API (MiMo, DeepSeek, self-hosted) — ungrounded

When `CROSS_MODEL_AVAILABLE=openai_compatible`, use the **Chat Completions API** at
`ARS_OPENAI_COMPAT_BASE_URL`, authenticated with the dedicated `ARS_OPENAI_COMPAT_API_KEY`.
These providers expose no hosted web-search tool, so there is **no grounding guard**. The
handler therefore normalizes the verdict by invoking the canonical
`normalize_compat_verdict.py` unit, which emits a single-line JSON object
(`{"status","provider","context"}`): a positive `VERIFIED` is downgraded to `NOT_SEARCHED` (an
ungrounded confirmation can never count as a grounded agreement), while a genuine rejection
(`NOT_FOUND` / `MISMATCH`) passes through as a useful disagreement. The consumer reads `.status`
only; the raw model text is JSON-escaped into `.context` as human-readable context and is
**never** placed in a verdict slot the agreement counter parses — embedded newlines become
literal `\n` inside the string, so a model response cannot inject a second status line. `PROMPT`
holds the single-reference verification prompt from step 3.

```bash
# ARS_OPENAI_COMPAT_BASE_URL is the API root INCLUDING /v1 (e.g. https://api.deepseek.com/v1).
# Trailing slash is normalized so the endpoint is built exactly once — no double /v1.
endpoint="${ARS_OPENAI_COMPAT_BASE_URL%/}/chat/completions"
GUARD=scripts/cross_model_verification

resp="$(curl -sS -w '\n%{http_code}' "$endpoint" \
  -H "Authorization: Bearer $ARS_OPENAI_COMPAT_API_KEY" \
  -H "Content-Type: application/json" \
  -d "$(jq -n --arg model "$ARS_CROSS_MODEL" --arg prompt "$PROMPT" '{
    model: $model,
    messages: [
      {role: "system", content: "You are a citation-verification assistant. If you did not actually perform an external lookup, respond NOT_SEARCHED. Use NOT_FOUND only if you are confident no such record exists; MISMATCH if a field is wrong; VERIFIED only with a source URL/DOI."},
      {role: "user", content: $prompt}
    ],
    temperature: 0.1
  }')")"

http="${resp##*$'\n'}"; body="${resp%$'\n'*}"
if [ "$http" -lt 200 ] || [ "$http" -ge 300 ]; then
  # Transport/API failure (401/429/5xx, or curl's 000) — distinct from NOT_SEARCHED, so the
  # consumer falls back to single-model (see § Graceful Degradation), never an ungrounded verdict.
  echo "CROSS-MODEL-ERROR: openai_compatible_http_$http"
else
  text="$(jq -r '.choices[0].message.content // empty' <<<"$body")"
  if [ -z "$text" ]; then
    echo "CROSS-MODEL-ERROR: openai_compatible_empty_response"
  else
    # Canonical normalization lives in scripts/cross_model_verification/normalize_compat_verdict.py
    # (behavior-tested in scripts/test_normalize_compat_verdict.py) and is INVOKED here rather than
    # re-implemented in bash — the same canonical-and-referenced pattern the first-party blocks use
    # with `jq -f`. It emits ONE line of JSON: {"status","provider","context"}. The consumer reads
    # .status only; raw model text is JSON-escaped in .context so it can never inject a second
    # status line (the producer/consumer anti-laundering contract holds at the output-format level).
    #   VERIFIED            -> status NOT_SEARCHED  (ungrounded positive can never agree)
    #   NOT_FOUND/MISMATCH  -> status passes through (useful disagreement)
    #   anything else/empty -> status NOT_SEARCHED  (fail closed)
    printf '%s' "$text" | python3 "$GUARD/normalize_compat_verdict.py"
  fi
fi
```

> **No grounding guard for compatible providers.** The grounding guard (an API-level
> `web_search_call` / `groundingMetadata` trace) exists only for first-party OpenAI and
> Gemini. A compatible provider cannot evidence a lookup, so its positive verdicts are
> downgraded to `NOT_SEARCHED` and never count as agreement. Its rejections survive as
> disagreements. The block emits a single-line JSON object (`{"status","provider","context"}`)
> from `normalize_compat_verdict.py`, and the grounded-agreement count is computed solely from
> its `.status` field — never from the raw text, which lives JSON-escaped in `.context`.
> For the OpenAI-compatible block, read the verdict from the JSON `.status` field only
> (e.g. `jq -r .status`); never grep the emitted line or `.context` for a verdict token — the
> raw model text is preserved JSON-escaped in `.context` precisely so it cannot be mistaken for
> a verdict.

### Detecting Available Models

Agents should check at the start of a verification/review session:

```bash
# Check which cross-model APIs are available
# Requires: jq (for JSON parsing). Fallback: python3 -c "import sys,json; ..."
if ! command -v jq &>/dev/null; then
  echo "WARNING: jq not installed. Cross-model API calls will use python3 fallback."
fi

if [ -n "$ARS_CROSS_MODEL" ]; then
  # PRECEDENCE: a first-party model id ALWAYS takes the grounded route, even if
  # ARS_OPENAI_COMPAT_BASE_URL is set. This prevents a grounded->ungrounded downgrade. ANY gpt-*
  # id (not just today's gpt-5.5/gpt-5.4) and any gemini-* id route grounded, so a future
  # first-party release keeps the grounded path instead of silently falling through to the
  # ungrounded compatible branch. The compatible path is reachable only for a model id that
  # matches no first-party prefix, and only when its dedicated opt-in env vars are both present.
  # OPENAI_BASE_URL is never read.
  # ID STATUS is a separate axis from routing (#518): routing answers "which provider
  # endpoint", the allowlist answers "is this id known-good". An unlisted gpt-*/gemini-* id
  # still routes grounded (never falls through to the ungrounded compatible branch) but is
  # announced as unlisted so nobody trusts results from a typo'd or made-up id the API has
  # never accepted. Applies to first-party routes only — compatible-route ids are
  # user-declared and carry no allowlist.
  id_status() {
    case " gpt-5.5 gpt-5.5-pro gpt-5.4 gpt-5.4-pro gemini-3.1-pro-preview " in
      *" $1 "*) echo "validated"; return ;;
    esac
    case " gpt-5.6-sol " in
      *" $1 "*) echo "provisional"; return ;;
    esac
    echo "unlisted"
  }
  announce_id_status() {
    status="$(id_status "$ARS_CROSS_MODEL")"
    echo "CROSS_MODEL_ID_STATUS=$status"
    case "$status" in
      provisional) echo "NOTE: $ARS_CROSS_MODEL is provisional — endpoint support confirmed, ARS-specific behavior unvalidated (see Supported Models). Run scripts/cross_model_smoke_test.sh before relying on it." ;;
      unlisted)    echo "WARNING: $ARS_CROSS_MODEL matches a first-party prefix and routes grounded, but is NOT a known-good id — the API may reject it. Check the id, or run scripts/cross_model_smoke_test.sh before trusting results." ;;
    esac
  }
  case "$ARS_CROSS_MODEL" in
    gpt-*)
      if [ -n "$OPENAI_API_KEY" ]; then
        echo "CROSS_MODEL_AVAILABLE=openai"; announce_id_status
      else
        echo "WARNING: ARS_CROSS_MODEL=$ARS_CROSS_MODEL but OPENAI_API_KEY is not set"
      fi ;;
    gemini*)
      if [ -n "$GOOGLE_AI_API_KEY" ]; then
        echo "CROSS_MODEL_AVAILABLE=google"; announce_id_status
      else
        echo "WARNING: ARS_CROSS_MODEL=$ARS_CROSS_MODEL but GOOGLE_AI_API_KEY is not set"
      fi ;;
    *)
      # Unrecognized id: only an explicit, credential-isolated opt-in enables the ungrounded
      # OpenAI-compatible path. Both the base URL AND the dedicated key are required; the
      # standard OPENAI_API_KEY is NEVER sent to a third-party endpoint (see Credential
      # isolation in the API Call Patterns section).
      if [ -n "$ARS_OPENAI_COMPAT_BASE_URL" ] && [ -n "$ARS_OPENAI_COMPAT_API_KEY" ]; then
        echo "CROSS_MODEL_AVAILABLE=openai_compatible"
      elif [ -n "$ARS_OPENAI_COMPAT_BASE_URL" ]; then
        echo "WARNING: ARS_OPENAI_COMPAT_BASE_URL is set but ARS_OPENAI_COMPAT_API_KEY is not — refusing to send another provider's key. Set ARS_OPENAI_COMPAT_API_KEY."
        echo "CROSS_MODEL_AVAILABLE=none"
      else
        echo "WARNING: ARS_CROSS_MODEL=$ARS_CROSS_MODEL is not a recognized model. First-party grounded route: any gpt-* id (e.g. gpt-5.5, gpt-5.5-pro, gpt-5.6-sol, legacy gpt-5.4*) or gemini-* id (e.g. gemini-3.1-pro-preview). For an OpenAI-compatible provider set ARS_OPENAI_COMPAT_BASE_URL + ARS_OPENAI_COMPAT_API_KEY and use that provider's model id (must not match a gpt-*/gemini-* prefix, or it takes the grounded first-party route instead)."
        echo "CROSS_MODEL_AVAILABLE=none"
      fi ;;
  esac
else
  echo "CROSS_MODEL_AVAILABLE=none"
fi
```

If `ARS_CROSS_MODEL` is set but the corresponding API key is missing or the model name is unsupported, the agent should warn the user and proceed with single-model verification.

### Promotion Bakeoff (provisional → validated → recommended default)

The run that flips a provisional id (today: `gpt-5.6-sol`) to validated is defined here so a future promotion argues against numbers, not vibes (#518). Validation and the recommended-default flip are two separate promotions — see the Outcome bullet: a bare non-inferiority pass never flips the default by itself.

- **Entry gate:** `scripts/cross_model_smoke_test.sh` passes against the candidate id.
- **Probe-set precondition (reproducibility):** before any run counts, the probe set must be committed as a versioned fixture (under `evals/` or `audits/`) listing each reference's full text, its ground-truth label (`real` / `fabricated`, with source DOI/URL for the real ones), and the file's sha256 recorded in the run report. A bakeoff against an ad-hoc, unversioned probe set is not a gate result. Composition: 30 references — 20 real (10 easy: DOI-keyed journal articles; 10 hard: preprints, DOI-less, non-English) + 10 synthetic plausible fabrications.
- **Procedure:** run the baseline (`gpt-5.5`) and the candidate the same day, one call per reference, 3 repeats. Per-reference verdict = the verdict returned by ≥ 2 of 3 repeats; if no verdict reaches 2 (a 1–1–1 split), the reference is **indeterminate** and scored conservatively against the model that produced it — a miss for recall (measure 2), a false disagreement for measure 3. Grounded-search completion (measure 1) is computed per call, so ties don't apply.
- **Non-inferiority thresholds — all five must pass:**
  1. **Grounded-search completion rate** (share of calls returning grounding evidence) ≥ baseline − 5 pp.
  2. **Citation-mismatch recall** on the 10 fabrications (share flagged `NOT_FOUND`/`MISMATCH`) ≥ baseline − 5 pp AND ≥ 80% absolute.
  3. **False-disagreement rate** on the 20 real references (share incorrectly flagged `NOT_FOUND`/`MISMATCH`) ≤ baseline + 5 pp.
  4. **jq-guard shape stability:** zero guard misfires attributable to response-shape change across all calls (hard requirement — a shape change that trips the fail-closed guards disqualifies regardless of the other measures).
  5. **p95 latency** ≤ 2× baseline.
- **Outcome — two distinct promotions, not one:**
  - **All five pass → `provisional` becomes `validated`** (the id-status allowlist and the Supported Models note update; a promotion PR records the run under `audits/` with the probe-set hash). Non-inferiority earns trust, nothing more.
  - **Recommended default flips only with a separate, stated reason on top of the validated pass** — superiority on at least one measure with no inferiority elsewhere, or a concrete operational benefit (cost, latency, capability) the promotion PR names explicitly. A candidate that merely scraped under every tolerance (−5 pp grounding, −5 pp recall, +5 pp false disagreements, 2× latency) is validated but NOT the new recommendation.
  - Any fail → the id stays provisional; the results are still recorded.

Web-search results vary day to day; the 3-repeat majority verdict and same-day paired runs are what make the comparison fair. Thresholds are the #518 spec's choice and are tunable in a future spec without redesigning the procedure.

## Cost Considerations

Cross-model verification adds API costs from the second provider:

| Scenario | Additional Calls | Estimated Additional Cost |
|----------|-----------------|--------------------------|
| Integrity verification (risk-stratified: HIGH-IMPACT — and at Stage 4.5 NEW-CHANGED — 100% uncapped + sampled remainder, min 3 / max 10; **one call per reference**) | worked example: 60 refs, 12 high-impact → 12 + 5 = 17 calls. No fixed upper bound — a results-dense paper approaches all references | ~$1.35-2.95 (the example; scales linearly with calls) |
| DA cross-check (1 per checkpoint, 3 checkpoints) | 3 calls | ~$0.30-0.55 |
| Blind disagreement checkpoints (design freeze + final editorial decision, 1 structured-decision call each; editorial repeats on re-review) | 2-3 calls | ~$0.20-0.55 |
| **Full pipeline (the worked example)** | **~22-23 calls** | **~$1.85-4.05 — no fixed ceiling; grows with the high-impact / new-changed count** |

These are rough estimates based on GPT-5.5 pricing ($5/1M input, $30/1M output) and typical prompt sizes; GPT-5.5 Pro runs ~6× higher ($30/1M input, $180/1M output). GPT-5.6 Sol bills at the same standard rates as GPT-5.5 ($5/1M input, $0.50/1M cached input, $30/1M output); its pro mode keeps those rates but performs more model work per request, so total tokens (and latency) rise instead of the unit price. One-call-per-reference (rather than batching) is a deliberate cost-for-provenance trade: it is the only way the grounding-evidence check maps 1:1 to each verdict. Web-search-tool calls also cost more than plain completions.

## Limitations

1. **Does not solve frame-lock fully.** All major LLMs share substantial training data. Cross-model catches different surface errors but may share deep structural biases.
2. **API latency.** Cross-model calls add 2-5 seconds per call, plus web-search round-trip time. With one call per reference (no batching) and a web-search tool, a risk-stratified integrity selection (uncapped HIGH-IMPACT plus the capped RANDOM sample at Stage 2.5; uncapped HIGH-IMPACT + NEW-CHANGED plus the capped CONTROL sample at Stage 4.5) can add several minutes on a results-dense paper; the calls can be issued concurrently to bound wall-clock time.
3. **Response format differences.** Different models structure responses differently. The agent must parse varied formats — keep verification prompts simple and structured to minimize parsing issues.
4. **Cost scales with paper size.** Longer papers with more references = more cross-model calls.

## Graceful Degradation

If cross-model verification fails **at the transport level** (API error, rate limit, key expired):
- Log the failure: `[CROSS-MODEL-ERROR: reason]`
- Continue with single-model verification — never block the pipeline on cross-model failure
- Include a note in the report: "Cross-model verification was configured but unavailable for this run. Results are single-model only."

A `NOT_SEARCHED` result is **not** a transport failure and is handled differently. It means the call succeeded but the model could not (or did not) ground the lookup, so its verdict carries no evidence. Do not fall back to single-model and do not treat it as agreement: record the reference as `NOT_SEARCHED` in the results table, count it separately from agreements/disagreements, and surface it for re-run or human review. The distinction matters — a transport failure means "we have no cross-model opinion"; a `NOT_SEARCHED` means "the cross-model gave an opinion we have decided not to trust as a confirmation."
