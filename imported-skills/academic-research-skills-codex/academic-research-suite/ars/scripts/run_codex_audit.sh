#!/usr/bin/env bash
# version: 1.0.0
#
# This wrapper is NOT to be invoked by an in-LLM Bash tool call from the same
# session producing the audited deliverable. Allowed invokers: human interactive
# shell, CI workflow step, SubagentStop hook, second-terminal Bash from outside
# the LLM session. Same-session in-LLM invocation creates Pattern C3 exposure.
# See spec §4.7.
#
# Usage:
#   scripts/run_codex_audit.sh \
#     --stage <1-6> \
#     --agent <synthesis_agent|research_architect_agent|report_compiler_agent> \
#     --deliverable <repo-relative-path> \
#     --round <N> \
#     [--target-rounds <N>]       # default 3
#     [--supporting <p1,p2,...>]  # comma-separated repo-relative paths
#     [--previous-findings <path>] # required when --round > 1
#     [--bundle-id <string>]
#     [--output-dir <dir>]        # default audit_artifacts/
#     [--dry-run]                 # validate inputs only; write nothing
#
# Exit codes (§4.6):
#   0    Audit complete; verdict is PASS / MINOR / MATERIAL
#   64   EX_USAGE  — input validation failed (no files written)
#   70   EX_SOFTWARE — AUDIT_FAILED (JSONL parse error or bundle mutation)
#   73   EX_CANTCREAT — tee write failed; JSONL integrity not guaranteed
#   75   EX_TEMPFAIL — codex rate-limited / transient error (retry candidate)
#   other  codex non-zero exit (preserved as-is; AUDIT_FAILED artifact set written)

set -euo pipefail

# ---------------------------------------------------------------------------
# Bash version guard — §4.1 requires Bash 4+ for indexed arrays, read -ra, <<<
# ---------------------------------------------------------------------------
if [[ "${BASH_VERSINFO[0]}" -lt 4 ]]; then
  printf '[run_codex_audit] error: Bash 4+ required (found %s). On macOS: brew install bash\n' \
    "${BASH_VERSION}" >&2
  exit 64
fi

# ---------------------------------------------------------------------------
# Helper functions — defined before the dependency preflight so they are
# available for the _sha256 check itself.
# ---------------------------------------------------------------------------

# SHA-256 backend selection — cached once to avoid forking `command -v` per call
# (Step 0b + Step 3a together produce 8+ hash calls).
if command -v sha256sum >/dev/null 2>&1; then
  _SHA256_CMD=(sha256sum)
else
  _SHA256_CMD=(shasum -a 256)
fi

# _sha256 <path>
# Portable SHA-256 hex digest. Prefers GNU sha256sum (Linux / coreutils);
# falls back to BSD shasum -a 256 (macOS stock).
_sha256() {
  "${_SHA256_CMD[@]}" "$1" | awk '{print $1}'
}

# _sha256_str <string>
# SHA-256 of an in-memory string (for the bundle manifest).
_sha256_str() {
  printf '%s' "$1" | "${_SHA256_CMD[@]}" | awk '{print $1}'
}

# _atomic_write <dest-path>
# Reads stdin, writes to <dest>.tmp, fsyncs, then renames over <dest>.
# Used for sidecar, verdict, and proposal entry — the three files §4.4 §4.8
# guarantees orchestrator observes whole-or-not-at-all. JSONL is exempt
# because codex streams it over the audit's runtime; see §4.4 atomicity note.
#
# F-010 (§3.6): each sub-step (cat, fsync, mv) is explicitly error-checked.
# A raw cat/fsync/mv failure with set -euo pipefail would abort the wrapper
# before AUDIT_FAILED artifacts are written, violating §4.6 invariant E8.
# All three failure cases now emit a diagnostic and exit 73 (EX_CANTCREAT).
_atomic_write() {
  local path="$1"
  local tmp="${path}.tmp"
  if ! cat > "${tmp}" 2>/dev/null; then
    printf '[run_codex_audit] error: failed to write %s\n' "${tmp}" >&2
    exit 73
  fi
  if command -v python3 >/dev/null 2>&1; then
    if ! python3 -c "import os,sys; f=open(sys.argv[1],'rb'); os.fsync(f.fileno()); f.close()" "${tmp}" 2>/dev/null; then
      rm -f "${tmp}"
      printf '[run_codex_audit] error: fsync failed for %s\n' "${tmp}" >&2
      exit 73
    fi
  else
    sync
  fi
  if ! mv -f "${tmp}" "${path}" 2>/dev/null; then
    rm -f "${tmp}"
    printf '[run_codex_audit] error: rename failed for %s\n' "${path}" >&2
    exit 73
  fi
}

# _extract_jsonl_thread_id <jsonl-path>
# Returns the thread_id from the first thread.started event, or empty string
# when JSONL is missing / empty / lacks a parseable thread.started event.
# codex 0.125+ emits thread_id only on the opening thread.started event (§3.3).
#
# F-001 (§3.6): jq must be non-fatal. A SIGKILL'd or disk-full partial JSONL can
# make jq exit non-zero; with set -euo pipefail that would abort the wrapper BEFORE
# the mandatory AUDIT_FAILED sidecar/verdict/proposal trio is written, violating §4.6
# invariant E8. The `|| printf ''` ensures the function always returns success.
_extract_jsonl_thread_id() {
  local path="$1"
  if [[ ! -s "${path}" ]]; then
    printf ''
    return 0
  fi
  # F-015 (§3.1): jq emits the literal string "null" when thread_id is absent or
  # non-string; a malformed thread.started event would then propagate "null" into
  # the sidecar's stream.jsonl_thread_id, failing the schema UUID regex.
  # Chain select(type == "string") + UUID-pattern guard to degrade gracefully to
  # empty string (permitted by schema when companion verdict is AUDIT_FAILED).
  jq -r '
    select(.type == "thread.started")
    | .thread_id
    | select(type == "string")
    | select(test("^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$"))
  ' "${path}" 2>/dev/null \
    | head -1 \
    || printf ''
}

# _codex_version
# Extracts bare semver from `codex --version`. codex 0.125+ prints
# "codex-cli X.Y.Z" (e.g., "codex-cli 0.128.0"); we strip the prefix and return just the dotted-triple.
# Exits 64 if no semver-shaped token is found — guards against future CLI
# format changes silently leaking garbage into the sidecar's codex_cli_version.
_codex_version() {
  local v
  v=$(codex --version 2>/dev/null \
    | awk 'match($0, /[0-9]+\.[0-9]+\.[0-9]+/) { print substr($0, RSTART, RLENGTH); exit }')
  if [[ -z "${v}" ]]; then
    printf '[run_codex_audit] error: cannot parse semver from `codex --version`\n' >&2
    exit 64
  fi
  printf '%s\n' "${v}"
}

# _now_rfc3339_ms
# UTC timestamp with millisecond precision in RFC 3339 format.
# Format: YYYY-MM-DDTHH:MM:SS.mmmZ  (colons in time — JSON field format).
# This is the JSON/sidecar field format; run_id uses hyphens instead.
_now_rfc3339_ms() {
  python3 -c "
import datetime
now = datetime.datetime.now(datetime.timezone.utc)
ms = now.strftime('%Y-%m-%dT%H:%M:%S') + '.{:03d}Z'.format(now.microsecond // 1000)
print(ms)
"
}

# _random_4hex
# Four random lowercase hex characters from /dev/urandom.
# Used as the run_id suffix to disambiguate sub-second concurrent runs.
_random_4hex() {
  od -An -N2 -tx1 < /dev/urandom | tr -d ' \n'
}

# _make_run_id
# Generates a run_id per §3.1 / §3.7 F1 contract:
#   <ISO-8601-Z>-<4-hex>
# where the date-time portion uses HYPHENS in place of colons (filename safe).
# Example: 2026-04-30T15-22-04Z-d8f3
# Note: JSON field values (started_at, ended_at) use colons per RFC 3339.
_make_run_id() {
  local dt
  dt=$(python3 -c "
import datetime
now = datetime.datetime.now(datetime.timezone.utc)
print(now.strftime('%Y-%m-%dT%H-%M-%SZ'))
")
  printf '%s-%s\n' "${dt}" "$(_random_4hex)"
}

# _duration_seconds <started_at_rfc3339_ms> <ended_at_rfc3339_ms>
# Returns elapsed seconds as a float.
# F-009 (§3.1): clamp to minimum 0.001 — audit_sidecar.schema.json sets
# duration_seconds exclusiveMinimum: 0; very fast failures (codex exits before
# 1ms) would produce 0.000 which violates the schema constraint.
_duration_seconds() {
  python3 -c "
import datetime, sys
fmt = '%Y-%m-%dT%H:%M:%S.%fZ'
t0 = datetime.datetime.strptime(sys.argv[1], fmt)
t1 = datetime.datetime.strptime(sys.argv[2], fmt)
secs = (t1-t0).total_seconds()
# Clamp to schema exclusiveMinimum: 0
if secs <= 0:
    secs = 0.001
print('{:.3f}'.format(secs))
" "$1" "$2"
}

# _git_dirty
# Prints 'true' when the working tree is dirty, 'false' otherwise.
# Uses `--exit-code` so diff exits non-zero on dirty state; we catch that.
_git_dirty() {
  if git diff --quiet 2>/dev/null && git diff --cached --quiet 2>/dev/null; then
    printf 'false'
  else
    printf 'true'
  fi
}

# _to_repo_relative <path>
# If <path> is absolute, strip the leading slash (unlikely — §4.2 says
# deliverable is repo-relative, but belt-and-suspenders). If it starts with
# ./ normalize that away. Does not validate ..; that is the caller's job.
_to_repo_relative() {
  local p="$1"
  # Remove leading ./
  p="${p#./}"
  printf '%s' "${p}"
}

# _validate_repo_relative <path> <flag-name>
# F-006 (§3.1): Validates the path satisfies the audit_sidecar.schema.json
# repo_relative_path constraint: no leading /, no whitespace, no .. segments.
# Absolute paths, .. traversals, or whitespace paths fail schema validation
# downstream (proposal entry artifact_paths.{jsonl,sidecar,verdict} regex).
# Exits EX_USAGE 64 on violation.
_validate_repo_relative() {
  local path="$1"
  local flag="$2"
  # Must not be empty
  if [[ -z "${path}" ]]; then
    printf '[run_codex_audit] error: %s path must not be empty\n' "${flag}" >&2
    exit 64
  fi
  # Must not be absolute (leading /)
  if [[ "${path}" == /* ]]; then
    printf '[run_codex_audit] error: %s path must be repo-relative (no leading /): %s\n' \
      "${flag}" "${path}" >&2
    exit 64
  fi
  # Must not contain whitespace
  if [[ "${path}" =~ [[:space:]] ]]; then
    printf '[run_codex_audit] error: %s path must not contain whitespace: %s\n' \
      "${flag}" "${path}" >&2
    exit 64
  fi
  # Must not contain .. segments (path traversal)
  if [[ "${path}" =~ (^|/)\.\.(/|$) ]]; then
    printf '[run_codex_audit] error: %s path must not contain .. segments: %s\n' \
      "${flag}" "${path}" >&2
    exit 64
  fi
}

# _json_escape <string>
# Minimal JSON string escaping (backslash, double-quote, control chars).
_json_escape() {
  python3 -c "import json,sys; print(json.dumps(sys.argv[1]))" "$1"
}

# _yaml_escape_oneline <string>
# Produce a safe single-quoted YAML scalar. Single-quotes are escaped by
# doubling them per YAML spec.
_yaml_escape_oneline() {
  local s="$1"
  # Replace ' with '' for YAML single-quote escaping
  s="${s//\'/\'\'}"
  printf "'%s'" "${s}"
}

# ---------------------------------------------------------------------------
# Dependency preflight — exits 64 with "missing dependency: <name>" before
# any artifact write. Checked: bash (version already done above), git, awk,
# jq, od, tr, uname, sort, head, tee, mv, python3, codex, sha256sum|shasum.
# ---------------------------------------------------------------------------
_check_dep() {
  local cmd="$1"
  if ! command -v "${cmd}" >/dev/null 2>&1; then
    printf '[run_codex_audit] error: missing dependency: %s\n' "${cmd}" >&2
    exit 64
  fi
}

for _dep in git awk jq od tr uname sort head tee mv python3 codex; do
  _check_dep "${_dep}"
done

# SHA-256 helper: need at least one of sha256sum or shasum
if ! command -v sha256sum >/dev/null 2>&1 && ! command -v shasum >/dev/null 2>&1; then
  printf '[run_codex_audit] error: missing dependency: sha256sum or shasum\n' >&2
  exit 64
fi

# ---------------------------------------------------------------------------
# Input parsing
# ---------------------------------------------------------------------------
STAGE=""
AGENT=""
DELIVERABLE=""
SUPPORTING_CSV=""
ROUND=""
TARGET_ROUNDS="3"
PREV_FINDINGS=""
OUT_DIR="audit_artifacts"
BUNDLE_ID=""
DRY_RUN=false

# F-005 (§3.5): require_arg guards all value-taking flags so a missing operand
# (e.g. `--stage --agent foo`) exits EX_USAGE 64, not set -u unbound-variable
# exit 1. Checks $# >= 2 AND next token doesn't look like a flag (^--).
_require_arg() {
  local flag="$1"
  # $# here is the caller's argument count after its own shift operations.
  # We receive $# from the while-loop via the special `shift` semantics below;
  # instead test the second positional ($2) of the calling while iteration.
  # Because this is called from within the case block, $2 is the while-loop's $2.
  if [[ $# -lt 3 || "$3" =~ ^-- ]]; then
    printf '[run_codex_audit] error: %s requires a value\n' "${flag}" >&2
    exit 64
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --stage)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --stage requires a value\n' >&2; exit 64
      fi
      STAGE="$2"; shift 2 ;;
    --agent)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --agent requires a value\n' >&2; exit 64
      fi
      AGENT="$2"; shift 2 ;;
    --deliverable)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --deliverable requires a value\n' >&2; exit 64
      fi
      DELIVERABLE="$2"; shift 2 ;;
    --supporting)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --supporting requires a value\n' >&2; exit 64
      fi
      SUPPORTING_CSV="$2"; shift 2 ;;
    --round)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --round requires a value\n' >&2; exit 64
      fi
      ROUND="$2"; shift 2 ;;
    --target-rounds)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --target-rounds requires a value\n' >&2; exit 64
      fi
      TARGET_ROUNDS="$2"; shift 2 ;;
    --previous-findings)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --previous-findings requires a value\n' >&2; exit 64
      fi
      PREV_FINDINGS="$2"; shift 2 ;;
    --output-dir)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --output-dir requires a value\n' >&2; exit 64
      fi
      OUT_DIR="$2"; shift 2 ;;
    --bundle-id)
      if [[ $# -lt 2 || "$2" =~ ^-- ]]; then
        printf '[run_codex_audit] error: --bundle-id requires a value\n' >&2; exit 64
      fi
      BUNDLE_ID="$2"; shift 2 ;;
    --dry-run)       DRY_RUN=true;       shift   ;;
    # Explicitly reject flags from early drafts that are NOT part of §4.2
    --bundle)
      printf '[run_codex_audit] error: --bundle is not a valid flag (use --bundle-id); see spec §4.2\n' >&2
      exit 64
      ;;
    --audit-template)
      printf '[run_codex_audit] error: --audit-template is not a valid flag; see spec §4.2\n' >&2
      exit 64
      ;;
    *)
      printf '[run_codex_audit] error: unknown flag: %s\n' "$1" >&2
      exit 64
      ;;
  esac
done

# ---------------------------------------------------------------------------
# Input validation (§4.2) — all failures → exit 64 EX_USAGE
# ---------------------------------------------------------------------------

# Required flags
for _flag_name in STAGE AGENT DELIVERABLE ROUND; do
  _flag_val="${!_flag_name}"
  if [[ -z "${_flag_val}" ]]; then
    _flag_cli=$(printf '%s' "${_flag_name}" | tr 'A-Z_' 'a-z-')
    printf '[run_codex_audit] error: --%s is required\n' "${_flag_cli}" >&2
    exit 64
  fi
done

# --stage: integer 1-6
if ! [[ "${STAGE}" =~ ^[1-6]$ ]]; then
  printf '[run_codex_audit] error: --stage must be an integer 1-6 (got: %s)\n' "${STAGE}" >&2
  exit 64
fi

# --agent: closed enum
case "${AGENT}" in
  synthesis_agent|research_architect_agent|report_compiler_agent) ;;
  *)
    printf '[run_codex_audit] error: --agent must be one of synthesis_agent, research_architect_agent, report_compiler_agent (got: %s)\n' "${AGENT}" >&2
    exit 64
    ;;
esac

# --deliverable: must exist and be readable
if [[ ! -f "${DELIVERABLE}" || ! -r "${DELIVERABLE}" ]]; then
  printf '[run_codex_audit] error: --deliverable not found or not readable: %s\n' "${DELIVERABLE}" >&2
  exit 64
fi

# --round: integer >= 1
if ! [[ "${ROUND}" =~ ^[0-9]+$ ]] || [[ "${ROUND}" -lt 1 ]]; then
  printf '[run_codex_audit] error: --round must be an integer >= 1 (got: %s)\n' "${ROUND}" >&2
  exit 64
fi

# --target-rounds: integer >= 1
if ! [[ "${TARGET_ROUNDS}" =~ ^[0-9]+$ ]] || [[ "${TARGET_ROUNDS}" -lt 1 ]]; then
  printf '[run_codex_audit] error: --target-rounds must be an integer >= 1 (got: %s)\n' "${TARGET_ROUNDS}" >&2
  exit 64
fi

# --round <= --target-rounds (§3.7 A3)
if [[ "${ROUND}" -gt "${TARGET_ROUNDS}" ]]; then
  printf '[run_codex_audit] error: --round (%s) must be <= --target-rounds (%s)\n' \
    "${ROUND}" "${TARGET_ROUNDS}" >&2
  exit 64
fi

# --previous-findings required when --round > 1 (audit template Section 4(a) violation)
if [[ "${ROUND}" -gt 1 && -z "${PREV_FINDINGS}" ]]; then
  printf '[run_codex_audit] error: --previous-findings is required when --round > 1\n' >&2
  exit 64
fi

if [[ -n "${PREV_FINDINGS}" && ! -f "${PREV_FINDINGS}" ]]; then
  printf '[run_codex_audit] error: --previous-findings not found: %s\n' "${PREV_FINDINGS}" >&2
  exit 64
fi

# --supporting: each path must exist
declare -a SUPPORTING=()
if [[ -n "${SUPPORTING_CSV}" ]]; then
  IFS=',' read -ra SUPPORTING <<< "${SUPPORTING_CSV}"
  for _sup_path in "${SUPPORTING[@]}"; do
    if [[ ! -f "${_sup_path}" ]]; then
      printf '[run_codex_audit] error: --supporting path not found: %s\n' "${_sup_path}" >&2
      exit 64
    fi
  done
fi

# ---------------------------------------------------------------------------
# F-017 (§3.6): inject --previous-findings into SUPPORTING before snapshot.
# Multi-round audits depend on the previous-findings file as context input.
# If it is NOT included in the bundle manifest, it can mutate between snapshot
# and codex invocation without detection — codex audits against different
# findings than the manifest claims.
#
# Fix: treat --previous-findings as a mandatory supporting file for round > 1.
# Inject it into the SUPPORTING array here (dedup by path so a user who also
# listed it in --supporting does not see duplicate content in the prompt).
# This preserves the §3.6 manifest role enum (primary | supporting | template)
# without adding a fourth role.
#
# audit_snapshot.py reads PREV_FINDINGS as part of the supporting bundle, so
# its bytes are snapshotted alongside other supporting files and its SHA enters
# the manifest — no live cat call after snapshot phase.
# ---------------------------------------------------------------------------
if [[ -n "${PREV_FINDINGS}" ]]; then
  _pf_already_in=0
  for _s in "${SUPPORTING[@]+"${SUPPORTING[@]}"}"; do
    if [[ "${_s}" = "${PREV_FINDINGS}" ]]; then
      _pf_already_in=1
      break
    fi
  done
  if [[ "${_pf_already_in}" -eq 0 ]]; then
    SUPPORTING+=("${PREV_FINDINGS}")
  fi
fi

# Audit template path — constant per §3.4 schema constraint
readonly AUDIT_TEMPLATE_PATH="shared/templates/codex_audit_multifile_template.md"
if [[ ! -f "${AUDIT_TEMPLATE_PATH}" ]]; then
  printf '[run_codex_audit] error: audit template not found: %s\n' "${AUDIT_TEMPLATE_PATH}" >&2
  exit 64
fi

# ---------------------------------------------------------------------------
# F-016 (§3.1): Normalize and validate all path inputs BEFORE the dry-run
# early-exit check.  Previously the _to_repo_relative + _validate_repo_relative
# calls came AFTER Step 0a, so --dry-run reported "inputs valid" even when
# an absolute or .. path would have failed EX_USAGE 64 on a real run.
# These calls are pure validation (no mkdir, no file writes), so reordering
# is safe and preserves the "dry-run is side-effect-free" invariant.
# ---------------------------------------------------------------------------
DELIVERABLE=$(_to_repo_relative "${DELIVERABLE}")
# F-006 (§3.1): validate deliverable and supporting paths satisfy repo_relative_path
# schema constraint (no leading /, no whitespace, no .. segments) AFTER normalization.
# Rejects /tmp/... or ../... paths that fail audit_artifact_entry schema validation.
_validate_repo_relative "${DELIVERABLE}" "--deliverable"
_norm_supporting=()
for _s in "${SUPPORTING[@]+"${SUPPORTING[@]}"}"; do
  _norm_sup=$(_to_repo_relative "${_s}")
  _validate_repo_relative "${_norm_sup}" "--supporting"
  _norm_supporting+=("${_norm_sup}")
done
SUPPORTING=("${_norm_supporting[@]+"${_norm_supporting[@]}"}")
# Normalize PREV_FINDINGS to match the normalized SUPPORTING entries (F-017):
# audit_snapshot.py dedupes PREV_FINDINGS against SUPPORTING by path equality,
# so paths must agree after _to_repo_relative normalization or both will be
# snapshotted as separate entries.
if [[ -n "${PREV_FINDINGS}" ]]; then
  PREV_FINDINGS=$(_to_repo_relative "${PREV_FINDINGS}")
fi
# F-014 (§3.1): validate --output-dir BEFORE mkdir -p to avoid creating a
# directory at an invalid path (absolute, .. traversal) before EX_USAGE 64 rejects it.
# "No side effects on input validation rejection" — mkdir must not fire first.
_validate_repo_relative "${OUT_DIR}" "--output-dir"

# ---------------------------------------------------------------------------
# Step 0a — dry-run early exit. §10 Phase 6.1 verification gate and §1.2
# threat model: writing artifacts at zero codex cost is Pattern C3 attack
# surface. --dry-run is input-validation only; nothing is written.
# (F-016: path validation runs above, before this check, so dry-run correctly
# rejects absolute/.. paths rather than reporting "inputs valid" for them.)
# ---------------------------------------------------------------------------
if [[ "${DRY_RUN}" = true ]]; then
  printf '[run_codex_audit] dry-run: inputs valid; no files written\n'
  exit 0
fi

# ---------------------------------------------------------------------------
# SIGTERM / SIGINT trap — F-059 closure.
# On termination: clean up partial artifacts (*.tmp + empty JSONL placeholder)
# and exit 75 (EX_TEMPFAIL). run_id may not be set yet when the trap fires,
# so we record it in a variable that the trap closure reads.
# ---------------------------------------------------------------------------
_CURRENT_RUN_ID=""
_OUT_DIR_FOR_TRAP=""

_cleanup_on_signal() {
  local rid="${_CURRENT_RUN_ID}"
  local odir="${_OUT_DIR_FOR_TRAP}"
  if [[ -n "${rid}" && -n "${odir}" ]]; then
    rm -f \
      "${odir}/${rid}.jsonl" \
      "${odir}/${rid}.meta.json" \
      "${odir}/${rid}.meta.json.tmp" \
      "${odir}/${rid}.verdict.yaml" \
      "${odir}/${rid}.verdict.yaml.tmp" \
      "${odir}/${rid}.audit_artifact_entry.json" \
      "${odir}/${rid}.audit_artifact_entry.json.tmp" \
      "${odir}/${rid}.stdout" \
      "${odir}/${rid}.stderr" \
      "${odir}/${rid}.manifest.txt" 2>/dev/null || true
  fi
  printf '[run_codex_audit] caught signal; cleaned up partial artifacts; exiting 75\n' >&2
  exit 75
}

trap '_cleanup_on_signal' SIGTERM SIGINT

# F-010 (§3.6): EXIT trap removes partial .tmp artifacts left by any aborted
# _atomic_write call. Preserves final contract files (no .tmp suffix).
# Coexists with SIGTERM/SIGINT trap above — EXIT fires after signal handler exits.
_cleanup_partials_on_exit() {
  if [[ -n "${run_id:-}" && -n "${OUT_DIR:-}" ]]; then
    rm -f "${OUT_DIR}/${run_id}".*.tmp 2>/dev/null || true
  fi
}
trap '_cleanup_partials_on_exit' EXIT

# ---------------------------------------------------------------------------
# Setup: run_id, output dir, codex version, git metadata
# ---------------------------------------------------------------------------
# Note: path normalization + validation (DELIVERABLE, SUPPORTING, OUT_DIR)
# was moved above Step 0a (F-016 fix) — paths are already normalized here.
run_id=$(_make_run_id)
_CURRENT_RUN_ID="${run_id}"

# F-010 (§3.6): normalize mkdir failure to EX_CANTCREAT 73.
# mkdir intentionally stays AFTER dry-run: dry-run must be side-effect-free.
if ! mkdir -p "${OUT_DIR}" 2>/dev/null; then
  printf '[run_codex_audit] error: cannot create output dir: %s\n' "${OUT_DIR}" >&2
  exit 73
fi
_OUT_DIR_FOR_TRAP="${OUT_DIR}"

CODEX_VERSION=$(_codex_version)
GIT_SHA=$(git rev-parse --short HEAD 2>/dev/null || printf 'unknown')
GIT_DIRTY=$(_git_dirty)
HOSTNAME_VAL=$(uname -n)
CWD_VAL=$(pwd)

# Primary deliverable array (always exactly one element)
declare -a PRIMARY=("${DELIVERABLE}")

# ---------------------------------------------------------------------------
# F-018 (§3.6): Reject binary/NUL inputs before snapshot.
# ---------------------------------------------------------------------------
# Step 0b — snapshot bundle (DELEGATED TO scripts/audit_snapshot.py).
#
# Round 5 architectural redesign: the Bash-side snapshot helper had three
# structural failures across rounds 1-5 of codex review:
#
#   F-004 (5 rounds partial): Bash command substitution runs the helper in a
#     subshell, so global SHA assignment didn't propagate to the parent.
#   F-018 (Round 4 fix broke wrapper): grep -q $'\0' is empty pattern → all
#     non-empty files rejected as binary.
#   F-020 (trailing newline drift): $(cat file) strips \n; manifest SHA from
#     in-memory content drifts from sha256sum(file) → Step 3a false-positive.
#
# All three are eliminated by moving byte-exact operations to Python:
#   - Single read per file (no TOCTOU window)
#   - Binary-safe NUL detection (b"\0" in content)
#   - hashlib.sha256(file_bytes) matches sha256sum(file) exactly
#
# scripts/audit_snapshot.py snapshot mode:
#   - Reads all bundle files as bytes (binary-safe)
#   - Rejects NUL-containing files (exit 64)
#   - Computes per-file SHA-256 + bundle manifest SHA from same bytes
#   - Writes <run_id>.manifest.txt and <run_id>.prompt.txt
#   - Emits JSON summary to stdout for the wrapper to consume
#
# Step 3a uses scripts/audit_snapshot.py verify mode against the same manifest;
# their SHAs match exactly (no trailing-newline drift).
# ---------------------------------------------------------------------------

# F-021 (§3.6) closure: dedup --previous-findings against SUPPORTING after
# normalization (which the wrapper does upstream). audit_snapshot.py also
# dedupes internally; doing it here too prevents the manifest from listing
# the same file under both --supporting and --previous-findings paths.
if [[ -n "${PREV_FINDINGS}" ]]; then
  _already_in_supporting=0
  for _s in "${SUPPORTING[@]+"${SUPPORTING[@]}"}"; do
    if [[ "${_s}" = "${PREV_FINDINGS}" ]]; then
      _already_in_supporting=1
      break
    fi
  done
  if [[ "${_already_in_supporting}" -eq 0 ]]; then
    SUPPORTING+=("${PREV_FINDINGS}")
  fi
fi

# Build snapshot CLI args (--primary repeated, --supporting repeated)
_snap_args=()
for _p in "${PRIMARY[@]}"; do
  _snap_args+=("--primary" "${_p}")
done
for _s in "${SUPPORTING[@]+"${SUPPORTING[@]}"}"; do
  _snap_args+=("--supporting" "${_s}")
done

# Run snapshot helper. Capture JSON summary on stdout, errors on stderr.
SNAPSHOT_JSON_FILE="${OUT_DIR}/${run_id}.snapshot.tmp"
SNAPSHOT_STDERR_FILE="${OUT_DIR}/${run_id}.snapshot_stderr.tmp"
set +e
_prev_findings_arg=()
if [[ -n "${PREV_FINDINGS}" ]]; then
  _prev_findings_arg=(--previous-findings "${PREV_FINDINGS}")
fi

python3 scripts/audit_snapshot.py snapshot \
  "${_snap_args[@]}" \
  "${_prev_findings_arg[@]+"${_prev_findings_arg[@]}"}" \
  --audit-template "${AUDIT_TEMPLATE_PATH}" \
  --output-dir "${OUT_DIR}" \
  --run-id "${run_id}" \
  --round "${ROUND}" \
  --target-rounds "${TARGET_ROUNDS}" \
  --git-sha "${GIT_SHA}" \
  --stage "${STAGE}" \
  --agent "${AGENT}" \
  > "${SNAPSHOT_JSON_FILE}" \
  2> "${SNAPSHOT_STDERR_FILE}"
SNAPSHOT_EXIT=$?
set -e

if [[ "${SNAPSHOT_EXIT}" -ne 0 ]]; then
  # Forward Python error to user. exit 64 (NUL detection / bad args) propagates;
  # exit 2 (file not found / OSError) we surface as exit 73 (EX_CANTCREAT).
  cat "${SNAPSHOT_STDERR_FILE}" >&2
  rm -f "${SNAPSHOT_JSON_FILE}" "${SNAPSHOT_STDERR_FILE}"
  case "${SNAPSHOT_EXIT}" in
    64) exit 64 ;;
    2)  exit 73 ;;
    *)  exit "${SNAPSHOT_EXIT}" ;;
  esac
fi

# Parse JSON summary into Bash variables. Use python3 for reliable JSON access
# (jq might not be present; we already require python3 in §4.1 dependency table).
BUNDLE_MANIFEST_SHA=$(python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
print(d['manifest_sha'])
" "${SNAPSHOT_JSON_FILE}")

AUDIT_TEMPLATE_SHA_PRE=$(python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
print(d['audit_template_sha'])
" "${SNAPSHOT_JSON_FILE}")

SHA_DELIVERABLE=$(python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
print(d['primary_files'][0]['sha'])
" "${SNAPSHOT_JSON_FILE}")

SNAPSHOT_PROMPT_PATH="${OUT_DIR}/${run_id}.prompt.txt"
SNAPSHOT_MANIFEST_PATH="${OUT_DIR}/${run_id}.manifest.txt"

# Clean up temp files (manifest.txt and prompt.txt remain — they're contract artifacts)
rm -f "${SNAPSHOT_STDERR_FILE}"
# Keep SNAPSHOT_JSON_FILE for sidecar emission (need to enumerate primary/supporting).

# Initialize mutation state. Step 3a (post-codex SHA recompute) may set these.
# Declaring here ensures BUNDLE_MUTATION_FILES is always an array.
BUNDLE_MUTATION_DETECTED=0
declare -a BUNDLE_MUTATION_FILES=()

# ---------------------------------------------------------------------------
# Step 1 — prompt rendered by audit_snapshot.py (Step 0b above) into
# <run_id>.prompt.txt. The Bash wrapper feeds it to codex stdin via shell
# redirection in Step 2b. No template-rendering logic in Bash anymore — that
# moved to Python alongside the byte-exact snapshot, so the prompt embeds
# exactly the snapshotted bytes (no trailing-newline drift, no second cat).
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Step 0c — REMOVED in Round 5 architecture.
# Bash-side TOCTOU defenses (Steps 0b/0c partial across rounds 1-5) are gone.
# audit_snapshot.py reads each file ONCE and computes both SHA and prompt bytes
# from the same read — there is no second-read window to defend against.
# Step 3a (post-codex) still detects post-snapshot disk mutations.
# ---------------------------------------------------------------------------
PRE_CODEX_MUTATION_DETECTED=0  # no pre-codex check needed; kept for Step 2b gate

# ---------------------------------------------------------------------------
# Step 2a — pre-touch empty JSONL placeholder (F-059 closure).
# This ensures the file exists at its final path even if codex is killed before
# emitting any output. AUDIT_FAILED verdict referencing an empty JSONL is
# handled correctly by §5.6 Path B5 short-circuit without Layer 2 validation.
#
# F-010 (§3.6): guard the pre-touch; a failure here (permissions, disk full)
# means the JSONL path would never be created, breaking the artifact invariant
# E8.  Exit 73 (EX_CANTCREAT) to signal the output directory is unusable.
# ---------------------------------------------------------------------------
if ! : > "${OUT_DIR}/${run_id}.jsonl" 2>/dev/null; then
  printf '[run_codex_audit] error: cannot create jsonl placeholder: %s\n' \
    "${OUT_DIR}/${run_id}.jsonl" >&2
  exit 73
fi

# ---------------------------------------------------------------------------
# Step 2b — invoke codex CLI.
#
# Skipped when PRE_CODEX_MUTATION_DETECTED=1 (Step 0c, F-004): bundle was
# mutated between SHA snapshot and prompt render; no codex invocation needed
# since BUNDLE_MUTATION_DETECTED is already set and Step 4 will emit AUDIT_FAILED.
#
# We use a real pipeline + ${PIPESTATUS[@]}, NOT process substitution
# `> >(tee ...)`, because:
#   1. Process substitution hides tee's exit status (wrapper never knows if
#      tee failed — disk full / EIO would silently corrupt the JSONL artifact).
#   2. Process substitution races on draining: orchestrator can read the JSONL
#      before the tee subshell flushes.
#   3. PIPESTATUS captures both codex exit (pipe[0]) AND tee exit (pipe[1]).
#
# `set +e` is required because pipefail would abort on codex's non-zero exit
# before ${PIPESTATUS[@]} is captured. We re-enable after capture.
#
# This is `codex exec`, not `codex exec resume` — every audit run starts a
# fresh thread; the wrapper never resumes a prior thread.
# ---------------------------------------------------------------------------
STARTED_AT=$(_now_rfc3339_ms)
CODEX_EXIT=0
TEE_EXIT=0

if [[ "${PRE_CODEX_MUTATION_DETECTED}" -eq 0 ]]; then
  set +e
  codex exec \
    -m gpt-5.5 \
    -c 'model_reasoning_effort="xhigh"' \
    --json \
    - \
    2> "${OUT_DIR}/${run_id}.stderr" \
    < "${SNAPSHOT_PROMPT_PATH}" \
    | tee "${OUT_DIR}/${run_id}.stdout" > "${OUT_DIR}/${run_id}.jsonl"
  pipe=("${PIPESTATUS[@]}")
  CODEX_EXIT="${pipe[0]}"
  TEE_EXIT="${pipe[1]}"
  set -e
fi

ENDED_AT=$(_now_rfc3339_ms)

# tee write failure → EX_CANTCREAT (73): JSONL integrity not guaranteed.
# Clean up all partial artifacts so orchestrator never sees a sidecar/verdict/
# proposal pointing at a corrupt JSONL.
if [[ "${TEE_EXIT}" -ne 0 ]]; then
  rm -f \
    "${OUT_DIR}/${run_id}.jsonl" \
    "${OUT_DIR}/${run_id}.stdout" \
    "${OUT_DIR}/${run_id}.stderr" \
    "${OUT_DIR}/${run_id}.manifest.txt" 2>/dev/null || true
  printf '[run_codex_audit] error: tee write failed (exit %s); JSONL artifact may be corrupt\n' \
    "${TEE_EXIT}" >&2
  exit 73
fi

# ---------------------------------------------------------------------------
# Step 3a — detect post-snapshot disk mutation via audit_snapshot.py verify.
# Compares each manifest entry's recorded SHA against current file content.
# Round 5 redesign: byte-exact comparison via Python (hashlib reads disk bytes
# verbatim), so manifest SHA and recompute SHA agree on trailing-newline
# semantics — F-020 false-positive (Bash strips \n, sha256sum doesn't) is gone.
#
# Output: list of mutated paths to stdout (one per line) on exit 1; empty
# stdout on exit 0 (no mutation).
# ---------------------------------------------------------------------------
VERIFY_OUT_FILE="${OUT_DIR}/${run_id}.verify_stdout.tmp"
set +e
python3 scripts/audit_snapshot.py verify \
  --manifest "${SNAPSHOT_MANIFEST_PATH}" \
  > "${VERIFY_OUT_FILE}" \
  2>/dev/null
VERIFY_EXIT=$?
set -e

if [[ "${VERIFY_EXIT}" -eq 1 ]]; then
  # Mutation detected — read mutated paths from stdout.
  while IFS= read -r _mutated_path; do
    if [[ -n "${_mutated_path}" ]]; then
      BUNDLE_MUTATION_DETECTED=1
      BUNDLE_MUTATION_FILES+=("${_mutated_path}")
    fi
  done < "${VERIFY_OUT_FILE}"
elif [[ "${VERIFY_EXIT}" -ne 0 ]]; then
  # F-024 (P2, R6): verify internal error must NOT pass through to PASS/MINOR/MATERIAL.
  # If we cannot run the post-snapshot freshness check, treat the audit as
  # AUDIT_FAILED — orchestrator must not assume "no mutation" from "verify
  # could not run". §4.6 contract: AUDIT_FAILED proposal blocks transition.
  BUNDLE_MUTATION_DETECTED=1
  BUNDLE_MUTATION_FILES+=("(audit_snapshot.py verify failed: exit ${VERIFY_EXIT})")
  printf '[run_codex_audit] error: audit_snapshot verify failed (exit %s); forcing AUDIT_FAILED\n' "${VERIFY_EXIT}" >&2
fi
rm -f "${VERIFY_OUT_FILE}"

# Step 3b: bundle_manifest_sha stays pinned to the PRE-codex value (Step 0b).
# The orchestrator's L3-4 check compares current-state SHAs against the
# manifest written at audit time — updating it post-mutation would silently
# accept a stale audit.

# ---------------------------------------------------------------------------
# Step 3c — write sidecar (atomic). §3.4 / §4.3.
# All timestamps, versions, and bundle context captured here for Layer 3
# anti-fake-audit evidence.
# ---------------------------------------------------------------------------
DURATION_S=$(_duration_seconds "${STARTED_AT}" "${ENDED_AT}")
JSONL_THREAD_ID=$(_extract_jsonl_thread_id "${OUT_DIR}/${run_id}.jsonl")

# Build JSON arrays for primary and supporting deliverables.
# Sources from the SNAPSHOT_JSON_FILE (audit_snapshot.py output) — same shape
# the schema requires: [{path, sha}, ...].
_primary_deliverables_json() {
  python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
print(json.dumps([{'path': f['path'], 'sha': f['sha']} for f in d['primary_files']]))
" "${SNAPSHOT_JSON_FILE}"
}

_supporting_context_json() {
  python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
print(json.dumps([{'path': f['path'], 'sha': f['sha']} for f in d['supporting_files']]))
" "${SNAPSHOT_JSON_FILE}"
}

# stdout_path and stderr_path: repo-relative POSIX paths (no leading /, no ..)
# OUT_DIR may be absolute or relative; we normalise to repo-relative by
# stripping the CWD prefix if it matches, or using as-is if already relative.
_repo_relative_out_path() {
  local full="${OUT_DIR}/${run_id}.${1}"
  # If OUT_DIR starts with /, attempt to strip CWD prefix
  if [[ "${full}" == /* ]]; then
    local cwd_prefix="${CWD_VAL}/"
    full="${full#"${cwd_prefix}"}"
  fi
  # Remove leading ./ if present
  full="${full#./}"
  printf '%s' "${full}"
}

STDOUT_PATH=$(_repo_relative_out_path "stdout")
STDERR_PATH=$(_repo_relative_out_path "stderr")

# Optional bundle_id field in sidecar
_bundle_id_sidecar_field=""
if [[ -n "${BUNDLE_ID}" ]]; then
  _bundle_id_sidecar_field="\"bundle_id\":$(_json_escape "${BUNDLE_ID}"),"
fi

_sidecar_json() {
  cat <<EOF
{
  "run_id": $(_json_escape "${run_id}"),
  "codex_cli_version": $(_json_escape "${CODEX_VERSION}"),
  "runner": {
    "hostname": $(_json_escape "${HOSTNAME_VAL}"),
    "cwd": $(_json_escape "${CWD_VAL}"),
    "git_sha": $(_json_escape "${GIT_SHA}"),
    "git_dirty": ${GIT_DIRTY}
  },
  "timing": {
    "started_at": $(_json_escape "${STARTED_AT}"),
    "ended_at": $(_json_escape "${ENDED_AT}"),
    "duration_seconds": ${DURATION_S}
  },
  "process": {
    "exit_code": ${CODEX_EXIT},
    "stdout_path": $(_json_escape "${STDOUT_PATH}"),
    "stderr_path": $(_json_escape "${STDERR_PATH}")
  },
  "stream": {
    "jsonl_thread_id": $(_json_escape "${JSONL_THREAD_ID}")
  },
  "prompt": {
    "audit_template_path": $(_json_escape "${AUDIT_TEMPLATE_PATH}"),
    "audit_template_sha": $(_json_escape "${AUDIT_TEMPLATE_SHA_PRE}"),
    "bundle": {
      ${_bundle_id_sidecar_field}
      "bundle_manifest_sha": $(_json_escape "${BUNDLE_MANIFEST_SHA}"),
      "primary_deliverables": $(_primary_deliverables_json),
      "supporting_context": $(_supporting_context_json)
    }
  }
}
EOF
}

_sidecar_json | _atomic_write "${OUT_DIR}/${run_id}.meta.json"

# ---------------------------------------------------------------------------
# Step 4 — produce verdict file.
# Three triggers force the AUDIT_FAILED branch:
#   (a) codex exited non-zero
#   (b) parse_audit_verdict.py --probe rejects the JSONL
#   (c) bundle mutation detected in Step 3a
# wrapper_exit_code starts as codex's actual exit; AUDIT_FAILED path may
# raise it to 70 when codex itself exited 0 (cases b and c).
# ---------------------------------------------------------------------------
WRAPPER_EXIT_CODE="${CODEX_EXIT}"

# _truncate_failure_reason <string>
# F-008 (§3.1): failure_reason maxLength is 500 per audit_verdict.schema.json,
# and the schema regex rejects multi-line strings (^[^\n\r]+$). Truncate to 497
# chars with ellipsis and strip embedded newlines/carriage-returns.
_truncate_failure_reason() {
  local s="$1"
  # Strip newlines/CRs — schema regex ^[^\n\r]+$ rejects multi-line values
  s=$(printf '%s' "${s}" | tr -d '\n\r')
  if [[ "${#s}" -gt 500 ]]; then
    printf '%s...' "${s:0:497}"
  else
    printf '%s' "${s}"
  fi
}

# Helper: synthesize a failure reason from codex exit code + stderr tail
_synthesize_failure_reason() {
  local exit_code="$1"
  local stderr_path="$2"
  local tail_msg=""
  if [[ -s "${stderr_path}" ]]; then
    # Take last non-empty line as context
    tail_msg=$(grep -v '^[[:space:]]*$' "${stderr_path}" 2>/dev/null | tail -1 || true)
  fi
  local reason=""
  if [[ -n "${tail_msg}" ]]; then
    reason=$(printf 'codex exit %s: %s' "${exit_code}" "${tail_msg}")
  else
    reason=$(printf 'codex exit %s' "${exit_code}")
  fi
  # F-008: apply truncation and newline-strip before returning
  _truncate_failure_reason "${reason}"
}

# Helper: emit an AUDIT_FAILED verdict YAML.
# Reuses ENDED_AT (already captured post-codex) for generated_at to avoid a
# second python3 fork purely for timestamp generation.
_emit_audit_failed_verdict() {
  local failure_reason="$1"
  cat <<EOF
run_id: $(_yaml_escape_oneline "${run_id}")
verdict_status: AUDIT_FAILED
round: ${ROUND}
target_rounds: ${TARGET_ROUNDS}
finding_counts:
  p1: 0
  p2: 0
  p3: 0
findings: []
failure_reason: $(_yaml_escape_oneline "${failure_reason}")
generated_at: $(_yaml_escape_oneline "${ENDED_AT}")
generated_by: 'scripts/run_codex_audit.sh'
generator_version: '1.0.0'
EOF
}

# Helper: parse finding_counts from verdict YAML emitted by parse_audit_verdict.py
_parse_verdict_counts_from_yaml() {
  local verdict_path="$1"
  python3 -c "
import sys, re

content = open(sys.argv[1]).read()

def extract_int(key, text):
    m = re.search(r'^\s*' + key + r'\s*:\s*(\d+)', text, re.MULTILINE)
    return int(m.group(1)) if m else 0

p1 = extract_int('p1', content)
p2 = extract_int('p2', content)
p3 = extract_int('p3', content)

# Extract verdict_status
sm = re.search(r'^\s*verdict_status\s*:\s*(\S+)', content, re.MULTILINE)
status = sm.group(1).strip(\"'\") if sm else 'AUDIT_FAILED'

print('{} {} {} {}'.format(status, p1, p2, p3))
" "${verdict_path}"
}

AUDIT_FAILED_REASON=""

# F-007 (§3.6): capture probe stderr explicitly so the actual parser rejection
# reason (e.g. "no agent_message in stream", "stream contains error event") is
# preserved in AUDIT_FAILED_REASON rather than a hardcoded fallback string.
_probe_stderr=""
_probe_exit=0
_probe_stderr=$(python3 scripts/parse_audit_verdict.py \
  --probe "${OUT_DIR}/${run_id}.jsonl" 2>&1 >/dev/null) \
  || _probe_exit=$?

if [[ "${CODEX_EXIT}" -eq 0 ]] \
   && [[ "${BUNDLE_MUTATION_DETECTED}" -eq 0 ]] \
   && [[ "${_probe_exit}" -eq 0 ]]; then
  # Clean path: codex exited 0, bundle stable, JSONL probe passed.
  # F-003 (§3.6): capture full parser stdout/stderr/exit BEFORE piping to
  # _atomic_write. If full parse fails after probe passed (cross-validation
  # disagreement, malformed finding entry, etc.), fall through to AUDIT_FAILED
  # rather than writing a partial verdict.yaml.tmp and aborting mid-rename.
  _verdict_yaml_content=""
  # F-010 (§3.6) Round 3: eliminate mktemp dependency — use a deterministic path
  # under OUT_DIR so the file is (a) always writable when OUT_DIR is writable and
  # (b) cleaned up automatically by the EXIT trap (_cleanup_partials_on_exit removes
  # "${OUT_DIR}/${run_id}".*.tmp).  Round 2 used mktemp /tmp/... which could fail
  # with EX_CANTCREAT 73 when /tmp is full or permission-denied, aborting the wrapper
  # before AUDIT_FAILED artifacts are written — violating §4.6 invariant E8.
  _full_parse_stderr_file="${OUT_DIR}/${run_id}.parse_stderr.tmp"
  if _verdict_yaml_content=$(python3 scripts/parse_audit_verdict.py \
        --jsonl "${OUT_DIR}/${run_id}.jsonl" \
        --round "${ROUND}" \
        --target-rounds "${TARGET_ROUNDS}" \
        2>"${_full_parse_stderr_file}"); then
    printf '%s' "${_verdict_yaml_content}" | _atomic_write "${OUT_DIR}/${run_id}.verdict.yaml"
    rm -f "${_full_parse_stderr_file}"
  else
    _full_parse_stderr=$(cat "${_full_parse_stderr_file}" 2>/dev/null || true)
    rm -f "${_full_parse_stderr_file}"
    # F-003: full parse failed after probe passed — fall through to AUDIT_FAILED
    # so proposal entry is still written (invariant E8) and orchestrator sees a
    # complete artifact set instead of a missing verdict. F-008 truncation applied.
    AUDIT_FAILED_REASON=$(_truncate_failure_reason \
      "JSONL parse error: ${_full_parse_stderr:-full parse failed after probe passed}")
    _emit_audit_failed_verdict "${AUDIT_FAILED_REASON}" \
      | _atomic_write "${OUT_DIR}/${run_id}.verdict.yaml"
    if [[ "${WRAPPER_EXIT_CODE}" -eq 0 ]]; then
      WRAPPER_EXIT_CODE=70
    fi
  fi
else
  # AUDIT_FAILED path: determine failure reason
  if [[ "${BUNDLE_MUTATION_DETECTED}" -eq 1 ]]; then
    AUDIT_FAILED_REASON=$(_truncate_failure_reason \
      "bundle file(s) mutated during audit run: ${BUNDLE_MUTATION_FILES[*]}")
  elif [[ "${CODEX_EXIT}" -ne 0 ]]; then
    AUDIT_FAILED_REASON=$(_synthesize_failure_reason \
      "${CODEX_EXIT}" "${OUT_DIR}/${run_id}.stderr")
  else
    # F-007: codex exit 0 but --probe rejected the JSONL — use captured stderr
    # for the actual rejection message rather than a hardcoded fallback string.
    AUDIT_FAILED_REASON=$(_truncate_failure_reason \
      "JSONL parse error: ${_probe_stderr:-no parseable agent_message found in JSONL stream}")
  fi

  _emit_audit_failed_verdict "${AUDIT_FAILED_REASON}" \
    | _atomic_write "${OUT_DIR}/${run_id}.verdict.yaml"

  # When codex exited 0 but wrapper rejects (cases b and c), raise to 70
  # so wrapper's process exit always agrees with the AUDIT_FAILED verdict
  # it just wrote (§4.6 contract: exit 0 ↔ PASS/MINOR/MATERIAL only).
  if [[ "${WRAPPER_EXIT_CODE}" -eq 0 ]]; then
    WRAPPER_EXIT_CODE=70
  fi
fi

# ---------------------------------------------------------------------------
# Step 5 — emit proposal entry (LAST write per invariant E8).
# Verdict block mirrors the verdict.yaml just written.
# verified_at and verified_by are NOT set — orchestrator fills them at merge.
# Proposal entries carrying these fields are rejected at §5.6 Path B4
# as Pattern C3 attack surface.
# ---------------------------------------------------------------------------

# Read back the verdict status and finding counts from the just-written YAML
_verdict_info=$(_parse_verdict_counts_from_yaml "${OUT_DIR}/${run_id}.verdict.yaml")
read -r VERDICT_STATUS P1_COUNT P2_COUNT P3_COUNT <<< "${_verdict_info}"

_optional_bundle_id_entry_field=""
if [[ -n "${BUNDLE_ID}" ]]; then
  _optional_bundle_id_entry_field="\"bundle_id\":$(_json_escape "${BUNDLE_ID}"),"
fi

_optional_failure_reason_field=""
if [[ "${VERDICT_STATUS}" = "AUDIT_FAILED" ]]; then
  _optional_failure_reason_field="\"failure_reason\":$(_json_escape "${AUDIT_FAILED_REASON}"),"
fi

_proposal_entry_json() {
  cat <<EOF
{
  "stage": ${STAGE},
  "agent": $(_json_escape "${AGENT}"),
  "deliverable_path": $(_json_escape "${DELIVERABLE}"),
  "deliverable_sha": $(_json_escape "${SHA_DELIVERABLE}"),
  "run_id": $(_json_escape "${run_id}"),
  ${_optional_bundle_id_entry_field}
  "bundle_manifest_sha": $(_json_escape "${BUNDLE_MANIFEST_SHA}"),
  "artifact_paths": {
    "jsonl": $(_json_escape "$(_repo_relative_out_path "jsonl")"),
    "sidecar": $(_json_escape "$(_repo_relative_out_path "meta.json")"),
    "verdict": $(_json_escape "$(_repo_relative_out_path "verdict.yaml")")
  },
  "verdict": {
    "status": $(_json_escape "${VERDICT_STATUS}"),
    ${_optional_failure_reason_field}
    "round": ${ROUND},
    "target_rounds": ${TARGET_ROUNDS},
    "finding_counts": {
      "p1": ${P1_COUNT},
      "p2": ${P2_COUNT},
      "p3": ${P3_COUNT}
    }
  }
}
EOF
}

_proposal_entry_json | _atomic_write "${OUT_DIR}/${run_id}.audit_artifact_entry.json"

# ---------------------------------------------------------------------------
# Step 6 — exit with wrapper_exit_code (§4.6 contract).
# Orchestrator also reads proposal entry's verdict.status; the two signals
# are independently consumed. A zero exit iff PASS/MINOR/MATERIAL.
# ---------------------------------------------------------------------------
printf '[run_codex_audit] run_id=%s verdict=%s exit=%s\n' \
  "${run_id}" "${VERDICT_STATUS}" "${WRAPPER_EXIT_CODE}" >&2

[[ "${WRAPPER_EXIT_CODE}" -eq 0 ]] && exit 0 || exit "${WRAPPER_EXIT_CODE}"
