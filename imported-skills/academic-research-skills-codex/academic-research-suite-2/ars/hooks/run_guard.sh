#!/bin/sh
# version: 1.0.0
#
# ARS write-scope guard LAUNCHER — PreToolUse hook (#454 Windows portability fix).
#
# WHY THIS EXISTS: the guard hook used to be wired as `python3 ".../ars_write_scope_guard.py"`
# directly. On Windows, `python3` is commonly a 0-byte Microsoft Store App Execution Alias
# stub (not real Python); invoking it non-interactively fails BEFORE the guard's Python runs,
# so none of the guard's own fail-safes apply — it just errors and spams the hook log (#454).
#
# This launcher finds a REAL Python (skipping stubs), then runs the guard as a SUPERVISED
# subprocess. Design: docs/design/2026-06-17-454-windows-python-hook-portability-design.md.
#
# POSTURE (Plan A — graceful degradation; the guard is OPTIONAL v3.10 hardening and ARS core
# needs no Python): if no real Python is found, OR the guard subprocess misbehaves, the
# launcher emits a valid PASS-THROUGH hook JSON and exits 0. It NEVER exits non-zero on these
# degraded paths (a non-2 exit blocks nothing anyway and only spams logs; exit 2 would
# hard-lock the user out of all writes/Bash for an environment gap or an ARS-side bug — wrong
# for an optional layer). It stays SILENT on stderr on degraded paths: PreToolUse is a hot
# path, so any per-call stderr IS the spam #454 is about.
#
# Bash 3.2 / POSIX sh compatible (same constraint as scripts/announce-ars-loaded.sh). On
# Windows this runs under Git Bash; with no Git Bash, CC falls back to PowerShell which can't
# run this .sh — the guard is then inactive (accepted degradation, see spec §3.3).

# Canonical pass-through output: no permissionDecision => falls back to the normal permission
# flow (NEVER emit "allow" — that would skip every other permission rule).
PASS_THROUGH='{"hookSpecificOutput":{"hookEventName":"PreToolUse"}}'

emit_passthrough_and_exit() {
    printf '%s\n' "$PASS_THROUGH"
    exit 0
}

# --- Resolve the guard script from THIS launcher's own location (codex P1) ---------------
# CC substitutes ${CLAUDE_PLUGIN_ROOT} into the hook COMMAND text before the shell, but does
# NOT guarantee it as an env var inside this script. So compute the guard path from $0.
# (No production env override: the guard path is ALWAYS derived from the launcher's own
# location. Tests that need a broken/alternate guard run the launcher from a temp plugin
# layout, so there is no production back door — P2-e.)
# shellcheck disable=SC1007  # `CDPATH= cd` is intentional: clear CDPATH for this one cd only
SELF_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd) || emit_passthrough_and_exit
GUARD="$SELF_DIR/../scripts/ars_write_scope_guard.py"

# --- Read the payload from stdin ONCE (we must replay it to the guard subprocess) ---------
# Known trade-off (gemini round-6 P2, accepted): the payload is held in a shell variable and
# replayed with `printf '%s'`. `printf` is a builtin so it is NOT bound by ARG_MAX, and the
# stripped trailing newline is irrelevant to the guard's JSON parse, so for ordinary hook
# payloads this is safe. A multi-megabyte Write payload on a POSIX shell that caps variable
# length is the narrow case this does not cover; buffering to a private temp file would handle
# it but adds another temp-file lifecycle (and symlink surface) to a hot path, so it is left as
# documented degradation rather than fixed speculatively.
PAYLOAD=$(cat)

# --- Marker probe: does this candidate run real Python? ----------------------------------
# A candidate is "real" iff the probe exits 0 AND prints the exact marker on stdout. A 0-byte
# Store stub fails to execute / prints nothing, so it is skipped. We bound each probe so a
# broken-but-hanging interpreter can't wedge the hot path (spec §3.3): prefer `timeout` when
# present, else a portable process-group watchdog.
MARKER=ARS_PY_OK
# Per-candidate (and guard) wall-clock bound, seconds. A small ops knob; validated to be a
# bare integer so it can't smuggle anything into the `timeout`/`sleep` args. Default 3.
PROBE_BOUND=${ARS_PROBE_BOUND:-3}
case "$PROBE_BOUND" in
    ''|*[!0-9]*) PROBE_BOUND=3 ;;
esac

# ARS_GUARD_FORCE_WATCHDOG=1 forces the no-`timeout` watchdog path even on hosts that HAVE
# `timeout`. This is a test/debug switch: it only changes the BOUNDING MECHANISM (timeout
# binary vs process-group watchdog), never the security decision — both paths enforce the
# same wall-clock bound and the same pass-through-on-overrun posture. Honored if set; safe
# to leave unset (the default prefers the `timeout` binary when present).
have_timeout() {
    [ -z "${ARS_GUARD_FORCE_WATCHDOG:-}" ] && command -v timeout >/dev/null 2>&1
}

# Reserved exit status meaning "the bounded command was killed for overrunning its bound".
TIMEOUT_STATUS=124

# Run "$@" with a wall-clock bound; its stdout flows to OUR stdout (capture via $(...)).
# Returns the command's real exit status, or $TIMEOUT_STATUS if it overran the bound.
# Stdin for "$@" is whatever the caller arranges (we redirect it per call site) — the guard
# call site PIPES the payload in, so the bounded command MUST keep that stdin.
run_bounded() {
    if have_timeout; then
        # GNU timeout exits 124 on timeout — normalize to our sentinel for a uniform caller.
        timeout "${PROBE_BOUND}s" "$@"
        _st=$?
        [ "$_st" -eq 124 ] && return "$TIMEOUT_STATUS"
        return "$_st"
    fi
    # No `timeout` binary: a portable background-and-watchdog fallback. Several POSIX subtleties
    # bite here, all of which broke a naive version (#454 dual-track):
    #
    #  1. STDIN: a backgrounded (`&`) command's stdin defaults to /dev/null, which would feed
    #     the GUARD an EMPTY payload (guard reads nothing -> pass-through -> a real `deny` is
    #     LOST and the guard is dead on any timeout-less host). We stash this function's stdin
    #     on fd 3 and redirect the job's stdin from it (`<&3`) so the piped payload arrives.
    #  2. STDOUT: capturing the job's stdout through the `$(...)` pipe directly would WEDGE the
    #     pipe — if the job spawns a grandchild we can't reap (no `setsid` to group-kill), that
    #     orphan keeps the pipe's write end open and `$(...)` blocks until it dies (the whole
    #     point of the bound). So the job writes stdout to a temp file; we `cat` it back after
    #     reaping the direct child. The orphan may linger but can no longer wedge the hot path.
    #  3. KILL: with `setsid` we new-pgid the job and signal the whole group (negative pid) so
    #     TERM-ignoring children die too; without it we can only reach the direct pid, so a
    #     grandchild a hung interpreter spawned can be ORPHANED (it no longer wedges the hot
    #     path per (2), but it lingers). There is no fully portable POSIX reap without process
    #     groups / setsid / job-control, and inventing one would add fragility for a doubly-
    #     degraded case (no `timeout` AND no `setsid` AND a broken interpreter that forks — the
    #     real marker probe and guard never spawn grandchildren). Accepted; prefer `timeout`
    #     (path A) and `setsid` where present (codex round-6 P2).
    #  4. TIMEOUT DETECTION via a DONE-FILE handshake, not the exit code (a TERM'd `sh` wrapper
    #     does not reliably surface 143/137) and not "did the kill succeed" (gemini round-6 P1
    #     refuted that: after `wait` reaps the child its pid is freed, and if the OS recycles it
    #     before the parent disarms the watchdog, a blind `kill` would land on an INNOCENT
    #     unrelated process — succeeding, so it would both false-flag a timeout AND signal the
    #     wrong pid). Instead the parent writes a done-file the instant `wait` returns; the
    #     watchdog kills (and flags) ONLY if that file is still absent when its sleep elapses.
    #     So "child finished in time" and "child overran" are decided by the handshake, never by
    #     racing a pid. mktemp failure must NOT fall back to a predictable /tmp path: a local
    #     attacker could pre-create it as a symlink, our redirect would fail, and the launcher
    #     would treat that as a broken guard and fail OPEN (gemini round-6 P1). If we can't get a
    #     private temp, degrade safely to pass-through instead of writing a guessable path.
    _rb_out=$(mktemp 2>/dev/null) || emit_passthrough_and_exit
    _rb_fired=$(mktemp 2>/dev/null) || { rm -f "$_rb_out" 2>/dev/null; emit_passthrough_and_exit; }
    _rb_done=$(mktemp 2>/dev/null) || { rm -f "$_rb_out" "$_rb_fired" 2>/dev/null; emit_passthrough_and_exit; }
    rm -f "$_rb_fired" 2>/dev/null  # absent = watchdog has not fired
    rm -f "$_rb_done" 2>/dev/null   # absent = parent has not yet signalled completion
    if command -v setsid >/dev/null 2>&1; then
        { setsid "$@" >"$_rb_out" <&3 3<&- & } 3<&0
    else
        { "$@" >"$_rb_out" <&3 3<&- & } 3<&0
    fi
    _cmd_pid=$!
    ( sleep "$PROBE_BOUND"
      # If the parent already signalled completion, the child finished within the bound: do NOT
      # kill (its pid may have been recycled to an innocent process) and do NOT flag a timeout.
      if [ ! -f "$_rb_done" ]; then
          # Real overrun: kill the whole process group (negative pid) when we can, else the bare
          # pid, and record the timeout. Re-check the done-file before the hard KILL too.
          kill -TERM "-$_cmd_pid" 2>/dev/null || kill -TERM "$_cmd_pid" 2>/dev/null
          : >"$_rb_fired"
          sleep 1
          if [ ! -f "$_rb_done" ]; then
              kill -KILL "-$_cmd_pid" 2>/dev/null || kill -KILL "$_cmd_pid" 2>/dev/null
          fi
      fi
    ) &
    _watch_pid=$!
    wait "$_cmd_pid" 2>/dev/null
    _st=$?
    : >"$_rb_done"  # DISARM the watchdog before reaping it — closes the pid-reuse race window
    kill "$_watch_pid" 2>/dev/null
    wait "$_watch_pid" 2>/dev/null
    cat "$_rb_out" 2>/dev/null  # replay captured stdout to OUR stdout (for the $(...) caller)
    if [ -f "$_rb_fired" ]; then
        rm -f "$_rb_out" "$_rb_fired" "$_rb_done" 2>/dev/null
        return "$TIMEOUT_STATUS"
    fi
    rm -f "$_rb_out" "$_rb_fired" "$_rb_done" 2>/dev/null
    return "$_st"
}

# Echo the first candidate ("cmd args") that verifies as REAL Python, or nothing.
# A candidate qualifies ONLY if the probe exits 0 AND prints exactly the marker on stdout
# (P1-a: a stub that prints the marker but exits non-zero must be rejected). Candidates in
# order; `py -3` first (the Windows launcher).
find_real_python() {
    for cand in "py -3" "python3" "python"; do
        # shellcheck disable=SC2086  # intentional word-split: "py -3" -> py with arg -3
        set -- $cand
        cmd=$1
        command -v "$cmd" >/dev/null 2>&1 || continue
        probe_out=$(run_bounded "$@" -c "import sys; sys.stdout.write('$MARKER')" </dev/null 2>/dev/null)
        probe_status=$?
        if [ "$probe_status" -eq 0 ] && [ "$probe_out" = "$MARKER" ]; then
            printf '%s' "$cand"
            return 0
        fi
    done
    return 1
}

REAL_PY=$(find_real_python) || emit_passthrough_and_exit
[ -n "$REAL_PY" ] || emit_passthrough_and_exit

# is_valid_hook_json: true iff $1 parses as a JSON object containing a top-level
# "hookSpecificOutput" key. Uses the REAL Python we already found (no jq dependency, P1-c:
# substring grep false-accepts e.g. `not json "hookSpecificOutput"`). Reads candidate on stdin.
is_valid_hook_json() {
    # shellcheck disable=SC2086  # $REAL_PY is "py -3" or "python3" — intentional split
    set -- $REAL_PY
    printf '%s' "$GUARD_OUT" | "$@" -c '
import sys, json
try:
    d = json.load(sys.stdin)
except Exception:
    sys.exit(1)
sys.exit(0 if isinstance(d, dict) and "hookSpecificOutput" in d else 1)
' >/dev/null 2>&1
}

# --- Supervise the guard subprocess (P1-b: time-bound it too; P1-c: validate JSON) --------
# Run the guard with the found interpreter, replaying the captured payload on its stdin,
# under the SAME wall-clock bound as the probes so a hung guard can't wedge the hot path.
# Decide what to emit:
#   * guard exits 0 AND stdout is a JSON object with hookSpecificOutput -> forward verbatim.
#   * anything else (non-zero, timeout, empty, non-JSON, missing key) -> guard is BROKEN;
#     per the maintainer decision (§3.2.1) degrade to pass-through + exit 0, never block.
# shellcheck disable=SC2086  # $REAL_PY is "py -3" or "python3" — intentional split
set -- $REAL_PY
# Capture the guard's stderr to a temp so we can RELAY it on the success path (P2-h: the guard
# has its own no-silent advisories — absent agent_type / schema drift / unreadable manifest —
# that must surface; the launcher only suppresses stderr on its OWN degraded paths). On the
# broken path we drop it, since broken-guard noise on every hot-path call is the #454 spam.
# No predictable /tmp fallback: a guessable path is a symlink-attack surface, and a redirect
# onto an attacker-owned symlink fails -> we'd read that as a broken guard and fail OPEN
# (gemini round-6 P1). If mktemp can't give us a private file, degrade safely to pass-through.
GUARD_ERR=$(mktemp 2>/dev/null) || emit_passthrough_and_exit
GUARD_OUT=$(printf '%s' "$PAYLOAD" | run_bounded "$@" "$GUARD" 2>"$GUARD_ERR")
GUARD_STATUS=$?

if [ "$GUARD_STATUS" -eq 0 ] && is_valid_hook_json; then
    # Healthy guard decision: relay its stderr advisories, then forward its JSON verbatim.
    [ -s "$GUARD_ERR" ] && cat "$GUARD_ERR" >&2
    rm -f "$GUARD_ERR" 2>/dev/null
    printf '%s\n' "$GUARD_OUT"
    exit 0
fi

# Guard broke / timed out / produced invalid output. Degrade, don't block, don't spam.
rm -f "$GUARD_ERR" 2>/dev/null
emit_passthrough_and_exit
