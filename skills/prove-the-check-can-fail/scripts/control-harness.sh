#!/bin/bash
# CONTROL HARNESS - decide whether a check deserves to be believed.
#
# A check that has never failed has never been tested. This runs your check twice:
# against an input you KNOW is good, and against one you KNOW is bad. Four outcomes:
#
#   good=pass  bad=fail   -> TRUSTWORTHY   (the only one that earns belief)
#   good=pass  bad=pass   -> BLIND         (it cannot see the thing it claims to check)
#   good=fail  bad=fail   -> OVERTIGHT     (it rejects everything; a green is impossible)
#   good=fail  bad=pass   -> INVERTED      (wired backwards)
#
# Usage:
#   control-harness.sh --good <arg> --bad <arg> -- <command...>
#
# The command is run with the fixture appended as its last argument:
#   control-harness.sh --good ok.json --bad broken.json -- python3 validate.py
# runs `python3 validate.py ok.json` then `python3 validate.py broken.json`.
#
# WHY IT RUNS THE COMMAND BARE
# An exit code dies in a pipe. `mycheck | tail -1` returns tail's status, not the check's,
# so a failing check reads as exit 0. Measured twice in one session: a script that correctly
# exited 1 was reported as rc=0 purely because the probe piped it. This harness never pipes
# the command it is judging; it captures output to a file and reads $? directly.
set -o pipefail
GOOD=""; BAD=""
while [ $# -gt 0 ]; do
  case "$1" in
    --good) GOOD="${2:?--good needs an argument}"; shift 2 ;;
    --bad)  BAD="${2:?--bad needs an argument}";   shift 2 ;;
    --)     shift; break ;;
    *) echo "unknown option: $1"; exit 2 ;;
  esac
done
[ -n "$GOOD" ] && [ -n "$BAD" ] || { echo "usage: control-harness.sh --good <arg> --bad <arg> -- <command...>"; exit 2; }
[ $# -gt 0 ] || { echo "no command given after --"; exit 2; }

OUT=$(mktemp -d); trap 'rm -rf "$OUT"' EXIT

# good arm - bare invocation, no pipe
"$@" "$GOOD" >"$OUT/good.log" 2>&1
RC_GOOD=$?
# bad arm
"$@" "$BAD" >"$OUT/bad.log" 2>&1
RC_BAD=$?

printf 'known-good : exit %-3s %s\n' "$RC_GOOD" "$GOOD"
printf 'known-bad  : exit %-3s %s\n' "$RC_BAD" "$BAD"

# A check that produced NO output on either arm is suspect even if the codes look right:
# a silent no-op can exit 0 without having run. Report it rather than hide it.
if [ ! -s "$OUT/good.log" ] && [ ! -s "$OUT/bad.log" ]; then
  echo "WARNING    : the check printed nothing on either arm - verify it actually ran"
fi

if [ "$RC_GOOD" = "0" ] && [ "$RC_BAD" != "0" ]; then
  echo "VERDICT    : TRUSTWORTHY - passes known-good, rejects known-bad"
  exit 0
elif [ "$RC_GOOD" = "0" ] && [ "$RC_BAD" = "0" ]; then
  echo "VERDICT    : BLIND - it passed the known-bad input. A green from this check is not evidence."
  echo "             Fix the CHECK, not the subject. Its last clean run proved nothing."
  exit 1
elif [ "$RC_GOOD" != "0" ] && [ "$RC_BAD" != "0" ]; then
  echo "VERDICT    : OVERTIGHT - it rejected the known-good input too. Nothing can ever pass."
  echo "             A gate no one can pass gets disabled, and then you have no gate at all."
  exit 1
else
  echo "VERDICT    : INVERTED - good fails and bad passes. The logic is wired backwards."
  exit 1
fi
