#!/usr/bin/env bash
# Live smoke test for the OpenAI grounded cross-model verifier route.
#
# Purpose: validate that a given OpenAI verifier model (ARS_CROSS_MODEL, gpt-* id)
# behaves correctly against the documented call pattern in
# shared/cross_model_verification.md BEFORE it is used in a real pipeline run.
# Primary use case: vetting a newly released model id (e.g. gpt-5.6-sol, listed
# as provisional) whose response shape / grounding behavior has no ARS operating
# history yet.
#
# This is a LIVE test: it issues one real Responses API call (with hosted
# web_search) against a stable, known-good reference. It costs a fraction of a
# cent and needs OPENAI_API_KEY, so it is NOT wired into CI — run it manually:
#
#   export OPENAI_API_KEY="sk-..."
#   export ARS_CROSS_MODEL="gpt-5.6-sol"            # model under test
#   export ARS_CROSS_MODEL_REASONING_EFFORT="medium" # optional (default: medium)
#   bash scripts/cross_model_smoke_test.sh
#
# Checks (exit 0 only if all hard checks pass):
#   1. HTTP 2xx (transport)
#   2. completed web_search_call present  — canonical jq guard, fail-closed
#   3. non-empty verdict text carrying exactly ONE whole-word verdict token —
#      single occurrence enforced (a substring hit inside e.g. "UNVERIFIED"
#      does not count; a repeated token FAILS: the fixture prompt demands
#      exactly one verdict, and a model that cannot comply with that
#      instruction is itself a gate signal)
#   4. a VERIFIED verdict carries at least one url_citation source
#   5. response model echo matches the requested model id (prefix match on
#      snapshot suffixes, e.g. gpt-5.5 -> gpt-5.5-2026-xx-xx)
#   6. when ARS_CROSS_MODEL_REASONING_EFFORT is set: the response must echo the
#      requested effort — a missing or mismatched echo FAILS (fail-closed; a
#      provisional model silently ignoring the setting is exactly what this
#      gate exists to catch). Skipped when the variable is unset (the request
#      omits the field, so there is nothing to confirm).
#
# The known-good reference is deliberately famous and stable so a NOT_FOUND /
# MISMATCH verdict indicates a broken search path or parser, not a bad fixture.
set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GUARD="$REPO_ROOT/scripts/cross_model_verification"
FAILURES=0

note() { printf '%s\n' "$*"; }
pass() { printf 'PASS: %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*"; FAILURES=$((FAILURES + 1)); }

# --- Preconditions -----------------------------------------------------------
command -v jq >/dev/null 2>&1 || { echo "ERROR: jq is required"; exit 1; }
command -v curl >/dev/null 2>&1 || { echo "ERROR: curl is required"; exit 1; }
[ -n "${OPENAI_API_KEY:-}" ] || { echo "ERROR: OPENAI_API_KEY is not set"; exit 1; }
[ -n "${ARS_CROSS_MODEL:-}" ] || { echo "ERROR: ARS_CROSS_MODEL is not set"; exit 1; }
case "$ARS_CROSS_MODEL" in
  gpt-*) : ;;
  *) echo "ERROR: this smoke test covers the OpenAI grounded route only (gpt-* ids); got '$ARS_CROSS_MODEL'"; exit 1 ;;
esac
[ -f "$GUARD/openai_has_completed_web_search.jq" ] || {
  echo "ERROR: canonical jq guards not found under $GUARD (run from a repo checkout)"; exit 1; }

EFFORT="${ARS_CROSS_MODEL_REASONING_EFFORT:-}"
note "model=$ARS_CROSS_MODEL effort=${EFFORT:-(provider default — reasoning field omitted)}"

# --- One real call against a stable reference --------------------------------
PROMPT='Verify this academic reference. Check: Does it exist? Are the author
names, year, title, and venue correct? Search the web to confirm — do not
answer from memory.

Respond with exactly one verdict:
- VERIFIED  — found online; include at least one source URL or DOI you found
- MISMATCH  — found, but a field is wrong (state which); include the source
- NOT_FOUND — searched, no matching record exists
- NOT_SEARCHED — you could not actually search the web for this reference

Reference: Vaswani, A., Shazeer, N., Parmar, N., Uszkoreit, J., Jones, L.,
Gomez, A. N., Kaiser, L., & Polosukhin, I. (2017). Attention is all you need.
Advances in Neural Information Processing Systems, 30.
— Context: cited as the origin of the Transformer architecture.'

resp="$(curl -sS -w '\n%{http_code}' https://api.openai.com/v1/responses \
  -H "Authorization: Bearer $OPENAI_API_KEY" \
  -H "Content-Type: application/json" \
  -d "$(jq -n --arg model "$ARS_CROSS_MODEL" --arg prompt "$PROMPT" \
        --arg effort "$EFFORT" '{
    model: $model,
    instructions: "You are a citation-verification assistant. Search the web before every verdict; never answer from memory. If you could not search, respond NOT_SEARCHED.",
    input: $prompt,
    tools: [{type: "web_search"}],
    temperature: 0.1
  } + (if $effort == "" then {} else {reasoning: {effort: $effort}} end)')")"

http="${resp##*$'\n'}"; body="${resp%$'\n'*}"

# --- Check 1: transport -------------------------------------------------------
if [ "$http" -ge 200 ] 2>/dev/null && [ "$http" -lt 300 ]; then
  pass "HTTP $http"
else
  fail "HTTP $http (transport/API error — body follows)"
  printf '%s\n' "$body" | head -5
  echo "RESULT: FAIL ($FAILURES check(s) failed)"
  exit 1
fi

# --- Check 2: grounding guard (canonical, fail-closed) ------------------------
if jq -e -f "$GUARD/openai_has_completed_web_search.jq" <<<"$body" >/dev/null; then
  pass "completed web_search_call present (grounding guard)"
else
  fail "no completed web_search_call — the model did not search; a real run would emit NOT_SEARCHED"
fi

# --- Check 3: verdict text ----------------------------------------------------
text="$(jq -r -f "$GUARD/openai_text.jq" <<<"$body")"
if [ -z "$text" ]; then
  fail "empty verdict text"
else
  # Whole-word match: a bare substring hit would extract VERIFIED out of
  # "UNVERIFIED" and false-pass an invalid status.
  all_hits="$(printf '%s' "$text" | grep -oE '\b(VERIFIED|MISMATCH|NOT_FOUND|NOT_SEARCHED)\b')"
  verdicts="$(printf '%s' "$all_hits" | sort -u | grep . || true)"
  distinct="$(printf '%s' "$verdicts" | grep -c . || true)"
  total="$(printf '%s' "$all_hits" | grep -c . || true)"
  if [ "$distinct" -eq 1 ] && [ "$total" -eq 1 ]; then
    pass "verdict token: $verdicts"
  elif [ "$distinct" -eq 1 ]; then
    fail "verdict token '$verdicts' repeated $total times — the single-verdict contract requires exactly one occurrence (the prompt demands exactly one verdict; non-compliance is a gate signal)"
    verdicts=""
  elif [ "$distinct" -eq 0 ]; then
    fail "no whole-word verdict token in response text (parser would reject) — text: $(printf '%s' "$text" | head -c 200)"
    verdicts=""
  else
    fail "multiple distinct verdict tokens ($(printf '%s' "$verdicts" | tr '\n' ' ')) — ambiguous for the consumer"
    verdicts=""
  fi
fi

# --- Check 4: VERIFIED must carry a source ------------------------------------
cites="$(jq -r -f "$GUARD/openai_sources.jq" <<<"$body")"
if [ "${verdicts:-}" = "VERIFIED" ]; then
  if [ -n "$cites" ]; then
    pass "VERIFIED carries url_citation source(s): $(printf '%s' "$cites" | head -1)"
  else
    fail "VERIFIED with no url_citation source — a real run downgrades this to NOT_SEARCHED"
  fi
else
  note "SKIP: source check (verdict was '${verdicts:-none}', not VERIFIED — expected VERIFIED for this fixture)"
  # A famous, indexed reference should verify; anything else means the search
  # or parse path is off even if individual guards passed.
  [ "${verdicts:-}" = "" ] || fail "fixture reference did not come back VERIFIED (got '${verdicts}')"
fi

# --- Check 5: model echo -------------------------------------------------------
resp_model="$(jq -r '.model // empty' <<<"$body")"
case "$resp_model" in
  "$ARS_CROSS_MODEL"|"$ARS_CROSS_MODEL"-*)
    pass "model echo: $resp_model" ;;
  "")
    fail "response carries no model field" ;;
  *)
    fail "model echo '$resp_model' does not match requested '$ARS_CROSS_MODEL' (silent rerouting?)" ;;
esac

# --- Check 6: reasoning effort accepted (fail-closed when requested) -----------
if [ -z "$EFFORT" ]; then
  note "SKIP: effort echo check (ARS_CROSS_MODEL_REASONING_EFFORT unset — reasoning field omitted from the request)"
else
  resp_effort="$(jq -r '.reasoning.effort // empty' <<<"$body")"
  if [ "$resp_effort" = "$EFFORT" ]; then
    pass "reasoning effort echo: $resp_effort"
  elif [ -z "$resp_effort" ]; then
    fail "requested reasoning effort '$EFFORT' but the response carries no reasoning.effort echo — the setting may have been ignored or the response shape changed (fail-closed for a promotion gate)"
  else
    fail "reasoning effort echo '$resp_effort' does not match requested '$EFFORT'"
  fi
fi

# --- Result --------------------------------------------------------------------
if [ "$FAILURES" -eq 0 ]; then
  echo "RESULT: PASS — $ARS_CROSS_MODEL behaves correctly against the documented verifier pattern"
  exit 0
else
  echo "RESULT: FAIL ($FAILURES check(s) failed) — do not adopt $ARS_CROSS_MODEL for verification runs yet"
  exit 1
fi
