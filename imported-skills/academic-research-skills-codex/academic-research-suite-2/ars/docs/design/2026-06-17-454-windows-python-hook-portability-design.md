# #454 — Windows Python hook portability + graceful no-Python degradation

**Status**: design (awaiting user review)
**Issue**: #454 (`ncwuguo`) — `ars_write_scope_guard.py` crashes with exit 49, empty stderr, on Windows alongside RTK
**Branch**: `fix/454-windows-python-hook-portability`
**Date**: 2026-06-17

## 1. Problem

The PreToolUse write-scope guard hook is registered as:

```json
{ "type": "command", "command": "python3 \"${CLAUDE_PLUGIN_ROOT}/scripts/ars_write_scope_guard.py\"" }
```

On the reporter's Windows machine every Bash/Write/Edit tool call makes this hook fail (exitCode 49, empty stderr, log spam). The guard's own Python only ever `return 0`s, so the failure is at the **interpreter-launch layer, before Python runs**: `python3` on Windows is commonly a 0-byte Microsoft Store App Execution Alias stub, not real Python.

### Empirically established (first-party, Windows 11 VM)
- On this Windows class, `python3`/`python`/`py` are 0-byte Store alias stubs under `…\AppData\Local\Microsoft\WindowsApps\`, not real Python. (CONFIRMED on VM.)
- The exact "exit 49 + empty stderr" signature was NOT reproduced (`prlctl exec` runs as SYSTEM, not the interactive user; the alias's real behavior only fires in the user's interactive session). The exact emitter of 49 remains UNCONFIRMED — but the root-cause CLASS (hook hardcodes a `python3` that is a non-functional alias) is established.

### Ground truth (official Claude Code hook docs, verified this session)
- Shell-form hook runs via `sh -c` (macOS/Linux), Git Bash (Windows), or **PowerShell when Git Bash isn't installed**.
- `${CLAUDE_PLUGIN_ROOT}` is substituted by Claude Code itself before the shell — the unexpanded value in the user's log is display text, not the executed command. (So "variable didn't expand" is NOT the bug.)
- Exit codes: `0` = no block (normal permission flow); `2` = blocks the tool; **any other non-zero (1, 49…) = NON-BLOCKING error — the action proceeds**, first stderr line shows as a hook-error notice, full stderr to debug log.
- Hooks for one event run **in parallel**; one hook's failure does NOT short-circuit siblings. (So ARS's failing hook does NOT serially "break" RTK — that earlier claim was wrong; RTK's hook runs regardless. ARS's only real harm is its own log spam.)
- No per-OS conditional command field. Exec form (`args` array) bypasses the shell but does NOT fix a wrong interpreter.

## 2. The deciding fact: ARS core does not require Python

Verified by repo inspection + independent codex/gemini fact-check:
- **Core skill use (research / write / review) requires NO Python.** README prerequisites list only Claude Code + API key; there is a `requirements-dev.txt` but no `requirements.txt`. SKILL.md/agent files are prompt/markdown that Claude reads.
- The guard hook is the **sole auto-running Python at user runtime**, and is an **optional security hardening layer** added in v3.10 (#134), not a core feature.
- **Nuance (codex catch — must stay honest):** ARS is not 100% prompt-only. These *opt-in / advanced* features DO execute real Python when the user invokes them:
  - revision mode: `scripts/ars_anchorize_draft.py`, `scripts/ars_apply_revision_patch.py`
  - pipeline submission verifier: `scripts/verify_submission_package.py`
  - slash commands: `/ars-cache-invalidate`, `/ars-mark-read`, `/ars-unmark-read`
  These are user-triggered (not auto-running hooks), so they fail visibly and the user can choose to install Python. They are **out of scope for this fix** (tracked as follow-up, §6).

### Consequence → Plan A (graceful degradation)
Forcing a Python install on a user whose ARS usage never needed Python (Plan B: fail-closed / exit 2) would turn an optional hardening layer into a global prerequisite, contradicting the setup docs and ARS's established "don't assume the environment has X; degrade if it's missing" principle (cf. #413 symlink→materialized copies for Windows). Both codex and gemini independently endorsed Plan A.

## 3. Design

### 3.1 A launcher that finds real Python (the fix for the bug body)
Add `hooks/run_guard.sh` (POSIX sh, Bash 3.2 compatible, same style/shape as the existing `scripts/announce-ars-loaded.sh`). Responsibilities:

1. **Resolve the plugin root from the launcher's OWN path, not `${CLAUDE_PLUGIN_ROOT}` (codex P1).** CC substitutes `${CLAUDE_PLUGIN_ROOT}` into the hook *command text* before the shell, but that does NOT guarantee the variable is exported into the launcher's environment. So the launcher computes the guard path relative to itself: `SELF_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"; GUARD="$SELF_DIR/../scripts/ars_write_scope_guard.py"`. This must work when `CLAUDE_PLUGIN_ROOT` is unset AND when the plugin path contains spaces (both are test cases, §3.5).
2. Detect a REAL Python interpreter by trying candidates in order. **Each candidate is a command + fixed args, NOT a single quoted string (codex P1):** `py -3` (command `py`, arg `-3`), then `python3`, then `python`. Implement as parallel positional sets, e.g. iterate over `"py -3" "python3" "python"` and split into `cmd`/`rest` via `set -- $candidate` so `py` is invoked with `-3` as a real argument — never as an executable literally named `py -3`.
3. For each candidate, VERIFY it actually executes by running a marker probe — `<cmd> <args> -c "import sys; print('ARS_PY_OK')"` — and requiring **both exit 0 AND the exact marker `ARS_PY_OK` on stdout**. A 0-byte Store stub fails to execute / prints nothing → skipped. Probe stdout/stderr suppressed except the marker check. Each probe wrapped in `timeout` when available (see §3.3 for the no-`timeout` watchdog).
4. First verified interpreter runs the guard **as a supervised subprocess, NOT a bare `exec` (codex/gemini P1 — see §3.2.1):** capture the guard's stdout and exit code; decide what to emit based on whether the guard produced a clean result. Stdin is forwarded to the guard.

### 3.2 No-Python posture (Plan A)
If NO candidate verifies (no real Python on the machine): the launcher emits a valid pass-through hook JSON `{"hookSpecificOutput":{"hookEventName":"PreToolUse"}}` and **exits 0**, and is SILENT on stderr (see "stderr discipline" below).

Rationale (grounded in §1 ground truth + §2 fact):
- A non-zero (non-2) exit blocks nothing anyway (GT) — "fail closed via nonzero" is an illusion that only spams logs.
- Exit 2 (true block) would hard-lock a user out of all inspected writes/Bash for an environment gap — wrong for an optional hardening layer on a Python-free core (§2).
- So pass-through + exit 0: no spam, no block.

**stderr discipline (resolves codex P2 — the earlier "stderr advisory + no spam" was self-contradictory):** PreToolUse is a hot path firing on every inspected tool call. Any stderr the launcher writes on the no-Python / guard-broke paths would, if CC surfaces or logs it, repeat on EVERY call — i.e. exactly the log spam #454 is about. Therefore the launcher writes **nothing to stderr on these degraded paths**; it stays silent and exits 0. The user-facing surface for "guard not active" is the docs note (§3.4), NOT a per-call stderr line. (A future once-per-session SessionStart advisory could surface it without hot-path spam — noted as optional follow-up §6, not built here.)

### 3.2.1 Found-Python-but-guard-broke posture (decision: do NOT block)
Distinct from "no Python" (an environment gap, not ARS's fault): here a real Python WAS found but the guard subprocess does not return a clean result — it crashes (non-zero exit), the guard script is missing, or it emits invalid/empty stdout instead of the expected hook JSON. This is an ARS-side defect (a broken guard), so:

- **The launcher emits valid pass-through JSON + exits 0 — it does NOT block (exit 2).** Maintainer decision: an ARS bug in our own hardening layer must not hard-lock the user out of their writes/Bash. Same degradation philosophy as no-Python: when the optional guard cannot produce a trustworthy decision, fall through to the normal permission flow rather than wedging the session.
- Two sub-cases the launcher must distinguish from a real decision:
  - guard exits 0 with valid hook JSON on stdout (deny OR pass-through) → forward that stdout verbatim, exit 0. (Normal path; note the guard ALWAYS exits 0 and signals deny via `permissionDecision:"deny"` in JSON — see §3.5 test-language fix.)
  - guard exits non-zero, or stdout is empty / not valid JSON / lacks `hookSpecificOutput` → treat as broken: emit the canonical pass-through JSON, exit 0, stay silent on stderr (per §3.2 discipline).
- Note the existing guard already self-degrades cleanly for an unreadable manifest (`ars_write_scope_guard.py:472` emits pass-through + exit 0), so that case never reaches the "broken" branch. The launcher's broken-branch handles the cases the guard itself can't (syntax error, missing file, crash before render).
- Honest cost: a genuinely broken guard is silently inactive (no per-call surface, per §3.2). This is the accepted trade-off of the maintainer's "don't block on our own bug" decision; the docs note (§3.4) plus CI lints (which would catch a guard syntax error pre-ship) are the compensating controls.

### 3.3 Bash 3.2 / cross-platform constraints
- POSIX sh only; no bashisms requiring bash 4+. Mirrors `announce-ars-loaded.sh` (which README notes runs on macOS stock bash with no `brew install bash`).
- **Probe timeout / no-`timeout` watchdog (codex P2).** Each marker probe runs under `timeout <N>s` when a `timeout` binary is present. When `timeout` is ABSENT, the launcher must NOT run the probe unbounded (a broken-but-non-stub interpreter that hangs would then hang EVERY PreToolUse call). Fallback watchdog: run the probe in the background, sleep a short bound, and kill the probe if still alive (`probe & pid=$!; ( sleep <N>; kill "$pid" 2>/dev/null ) & ...; wait "$pid"`), in POSIX-sh-portable form. If even that proves unreliable on a target shell, the launcher caps total candidates tried and bounds its own wall-clock; it must never hang the hot path. Tests cover both with- and without-`timeout` hosts AND a hanging candidate (§3.5).
- The single `.sh` launcher covers macOS, Linux, and Windows-with-Git-Bash. **On Windows WITHOUT Git Bash, this is NOT a clean degradation (codex P1 correction).** CC falls back to PowerShell, which runs the hook command `bash ".../run_guard.sh"`; if `bash` is absent from PATH, PowerShell errors, and per GT every inspected tool call becomes a NON-BLOCKING hook error — i.e. the guard is inactive AND the session is hook-error noisy (a different, milder spam than #454, but still noise). We ACCEPT this degradation for now (guard is optional hardening) but the spec states it honestly rather than calling it clean. Mitigations considered and deferred: a `.ps1` twin, a compiled binary (both rejected as disproportionate, §5); documenting Git Bash as the Windows prerequisite for the guard to be active (§3.4 docs note + §6 follow-up to quiet the PowerShell-no-bash noise).

### 3.4 hooks.json + docs
- `hooks.json` PreToolUse command changes from `python3 "…ars_write_scope_guard.py"` to `bash "${CLAUDE_PLUGIN_ROOT}/hooks/run_guard.sh"` (same shape as the announce hook).
- README / docs/SETUP.md gain a short note: the write-scope guard needs a real Python interpreter to be active; if none is found it cleanly no-ops and core (Python-free) skills are unaffected. Plus the honest list (§2 nuance): revision / submission-verify / those 3 slash commands need real Python.

### 3.5 Tests (close the codex-flagged blind spot)
Existing tests invoke the guard via `[sys.executable, guard_path]` — they never exercise interpreter resolution. Add launch-layer tests for `run_guard.sh` (and register the new test file in `scripts/_ci_pytest_manifest.toml`, see §3.6):

**Terminology fix (gemini/codex):** the guard ALWAYS exits 0 and signals a denial via `"permissionDecision":"deny"` in its stdout JSON (`render_hook_output`), never via a non-zero exit. All tests below assert on the forwarded JSON payload, not on exit codes-as-decision.

- **No real Python on PATH** — temp PATH dir holding only non-executing `python3`/`python`/`py` stubs (0-byte files or scripts printing nothing) so the marker probe fails for every candidate → launcher emits canonical pass-through JSON + exit 0, **silent on stderr** (§3.2). Run with AND without a `timeout` binary on PATH.
- **Real Python present, in-scope write** → launcher forwards the guard's pass-through JSON (no `permissionDecision`).
- **Real Python present, out-of-scope Bucket A write** → launcher forwards the guard's `permissionDecision:"deny"` JSON verbatim.
- **Stub-then-real ordering** (first candidate a stub, a later one real) → skips the stub, uses the real one, decision forwarded.
- **`py -3` arg handling** → assert the launcher invokes `py` with `-3` as an argument (e.g. a fake `py` on PATH that records its argv and only succeeds when given `-3`), not a command literally named `py -3`.
- **`CLAUDE_PLUGIN_ROOT` unset** → launcher still resolves the guard from its own path and works (covers codex P1).
- **Plugin path containing spaces** → launcher resolves and runs correctly (no word-splitting break).
- **Found-Python-but-guard-broke (§3.2.1)** → point the launcher at a guard that (a) exits non-zero, (b) prints nothing, (c) prints invalid JSON → in all three the launcher emits canonical pass-through JSON + exit 0 (does NOT block, does NOT spam). This is the gemini/codex P1 fail-open-on-crash case, resolved per the maintainer's "don't block on our own bug" decision.
- **Hanging candidate** → a fake interpreter that sleeps longer than the probe bound → launcher kills it and moves on within the bound (no hot-path hang), on both with/without-`timeout` hosts.
- **Infra self-protection** → a Bucket A subagent payload writing to `hooks/run_guard.sh` is denied (confirms `hooks/*.sh` glob covers the new file end-to-end through the launcher).
- (POSIX host simulation only; an actual Windows repro is still needed to confirm the Store-alias path, `py.exe -3` under Git Bash, Git Bash path conversion, CRLF, and the no-Git-Bash PowerShell fallback — noted as a known test-environment limit, not blocking ship but tracked §6.)

### 3.6 Seams to update (cross-file, dual-track flagged — all verified against the actual files)
- **CI hook-wiring assertion**: `.github/workflows/spec-consistency.yml` (~line 419, verified) asserts `"ars_write_scope_guard.py" in cmds` directly in hooks.json's PreToolUse command — this WILL break. Update it to assert the PreToolUse command now wires `run_guard.sh`, AND add an assertion that `hooks/run_guard.sh` references/execs `ars_write_scope_guard.py` (so the launcher→guard chain stays pinned and a future edit can't silently sever it).
- **CI pytest manifest (codex — newly surfaced, easy to miss)**: new test files are only run if listed in `scripts/_ci_pytest_manifest.toml` (the manifest runner at workflow line ~68; `check_ci_pytest_manifest.py` only validates listed entries). Add the new launch-layer test file to the manifest alongside the existing guard test entry (~line 149) — otherwise the new tests silently don't run in CI.
- **Infra self-protection**: `INFRA_PROTECTED_GLOBS` in `ars_write_scope_guard.py` (line 66, verified) already includes `hooks/*.sh` and matching is segment-aware (line 181), so `hooks/run_guard.sh` is auto-protected — no list change needed. Add the §3.5 test asserting a subagent write to it is denied (lock it in).
- **`.gitattributes` (codex — note it's a NEW file, not a confirmation)**: the repo currently has NO `.gitattributes`. Add one declaring `*.sh text eol=lf` (and the new launcher specifically) so a Windows CRLF checkout can't break the hot-path hook. Since it's new, confirm it doesn't disturb existing line-ending assumptions for other tracked files (scope the rule to `*.sh` to be safe).
- **Executable bit**: `run_guard.sh` committed with `+x` (matches `announce-ars-loaded.sh`).
- **Version/changelog discipline**: this repo enforces version-consistency lints. A hook-wiring + new-file change of this size should land a CHANGELOG entry and any version bump the repo's release discipline requires; check `check_version_consistency` / changelog lints before PR (per repo convention, not a guess about which version).

## 4. What this does NOT change
- The guard's `evaluate_decision` logic is untouched (it was never the bug).
- No per-OS branching (impossible per GT), no `.ps1` twin, no compiled binary.
- No change to the SessionStart announce hook (it's `bash` too; same no-Git-Bash caveat, but it's a context-injection nicety, not a security control — tracked as follow-up if desired, §6).

## 5. Rejected alternatives
- **exec form + hardcoded `node`/`python`**: collapses to the same bug class (a hardcoded interpreter that may be absent; `node` is NOT guaranteed on PATH for native-binary CC installs — codex verified against setup docs).
- **`.sh` + `.ps1` twin (universal launcher)**: solves no-Git-Bash Windows, but disproportionate maintenance shape for an OPTIONAL hardening layer; under Plan A, no-Git-Bash Windows degrading to "guard inactive" is acceptable.
- **Compiled native binary (Go/Rust)**: truly zero-dependency, but saddles a prompt/Python repo with a permanent cross-platform build+sign toolchain. Both reviewers called it overkill.
- **Plan B (fail-closed exit 2 for Bucket A when no Python)**: rejected per §2 — turns optional hardening into a global Python prerequisite on a Python-free core.
- **Fail-closed (exit 2) when Python IS found but the guard crashes**: considered (gemini argued for it: a present-but-broken security control should hard-block). Rejected by maintainer decision (§3.2.1): an ARS-side bug in our own optional hardening layer must not lock the user out of their writes/Bash. The guard-broke path degrades the same way as no-Python (pass-through + exit 0). Compensating controls: pre-ship CI lints catch a broken guard; the §3.4 docs note sets expectations. This is a deliberate availability-over-strictness call for THIS layer, not a general posture.

## 6. Follow-up (separate issues, not this PR)
- Harden the OTHER hardcoded-`python`/`python3` user-runtime call sites (revision scripts, submission verifier, the 3 slash commands) the same way, or document the Python requirement at those touch points.
- SessionStart announce hook: same no-Git-Bash-Windows caveat (cosmetic, non-security).
- CI Windows runner to actually exercise the Store-alias path (currently no Windows CI).
- Reply to codex repo #31 (`ncyunju`, Windows symlink/skill-registration) — same "ARS assumes a Windows capability" family.
