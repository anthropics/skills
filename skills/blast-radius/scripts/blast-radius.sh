#!/usr/bin/env bash
# blast-radius PreToolUse hook.
#
# Solves the trigger problem: a skill about not trusting a query only helps if it loads,
# and the agent that would blindly run the query is the one that will not think to load
# it. This fires on the command itself, at the moment of the write.
#
# Fails open by design. Any error, missing jq, or unrecognised input exits 0 silently -
# a safety hook that breaks someone's workflow gets deleted, and then it protects nobody.
set -uo pipefail

command -v jq >/dev/null 2>&1 || exit 0
INPUT=$(cat 2>/dev/null) || exit 0
CMD=$(printf '%s' "$INPUT" | jq -r '.tool_input.command // empty' 2>/dev/null) || exit 0
[ -n "$CMD" ] || exit 0

# Do NOT strip string literals: real commands carry the code inside quotes
# (node -e "...deleteMany()"), so stripping them removes the only thing worth scanning.
# That rules out stripping trailing '#' too - a '#' inside a quoted string (a colour
# literal, a URL fragment) would truncate the scan and hide the write after it. Only
# whole-line comments are unambiguous, so only those are dropped.
SCAN=$(printf '%s' "$CMD" | sed -e 's/^[[:space:]]*#.*$//')

# Read-only commands never write, however alarming their arguments look.
# Skip every leading VAR=value assignment, not just the first: `FOO=1 BAR=2 rg ...` is
# still a read of rg. A sed '^' anchor cannot re-match after the first strip, so scan
# the fields instead and take the first one that is not an assignment.
FIRST=$(printf '%s' "$SCAN" | awk '{for (i = 1; i <= NF; i++) if ($i !~ /^[A-Za-z_][A-Za-z0-9_]*=/) { print $i; exit } }')
case "$FIRST" in
  grep|rg|ag|cat|less|more|head|tail|ls|echo|printf|wc|awk|sed|jq|diff|man|which|type) exit 0 ;;
esac

# --- unbounded: no filter at all, so it hits the whole table ---
UNBOUNDED='deleteMany\(\s*\)|deleteMany\(\{\s*\}\)|updateMany\(\s*\{\s*\}|TRUNCATE[[:space:]]|DROP[[:space:]]+TABLE|DELETE[[:space:]]+FROM[[:space:]]+[A-Za-z_.]+[[:space:]]*(;|$)'

# --- bulk or destructive, but filtered ---
BULK='deleteMany|updateMany|createMany|DELETE[[:space:]]+FROM|UPDATE[[:space:]]+[A-Za-z_.]+[[:space:]]+SET|INSERT[[:space:]]+INTO|--method[[:space:]]+DELETE|-X[[:space:]]+DELETE|xargs[[:space:]]+rm|-exec[[:space:]]+rm|find[[:space:]].*-delete|push[[:space:]]+--force|push[[:space:]]+-f([[:space:]]|$)'

# --- a write inside a loop: the shape that quietly touches N rows ---
LOOP='for[[:space:]]*\(|forEach|\.map\(|while[[:space:]]*\('
WRITE='\.update\(|\.delete\(|\.create\(|\.upsert\(|emails\.send|sendMail|\.send\(|fetch\('

hit_unbounded=0; hit_bulk=0; hit_loopwrite=0
printf '%s' "$SCAN" | grep -Eqi "$UNBOUNDED" && hit_unbounded=1
printf '%s' "$SCAN" | grep -Eqi "$BULK"      && hit_bulk=1
if printf '%s' "$SCAN" | grep -Eqi "$LOOP" && printf '%s' "$SCAN" | grep -Eqi "$WRITE"; then hit_loopwrite=1; fi

[ $((hit_unbounded + hit_bulk + hit_loopwrite)) -eq 0 ] && exit 0

# A dry run is the behaviour this hook exists to encourage - do not nag it.
if printf '%s' "$SCAN" | grep -Eqi '\-\-dry|dry.?run|DRY_RUN|--check|--plan|SEND=0|APPLY=0'; then exit 0; fi

CHECKLIST='blast-radius — this looks like a bulk or destructive write.

Before running it:
1. SAY THE SENTENCE this filter implies about the world, then try to falsify it.
   Absence is not departure. Auto-generated rows are not activity. A status field is
   not the artifact. A timestamp cluster is one bulk edit, not independent decay.
2. CLASSIFY EVERY ROW into act / exclude / unknown. Never act on a count.
   UNKNOWN IS NEVER ACT. Resolve each row to something you can name, or leave it alone.
3. CHECK THE ACT BUCKET for rows the rule was never meant to catch - the most senior
   person, a service account, anything mid-flight. If they are in it, the rule is wrong.
4. ASK WHAT EACH ROW TAKES WITH IT - work in flight, things it owns, things owed to it.
5. DRY RUN FIRST and print every affected row. Verify the state actually moved
   afterwards; a call returning success is not proof the thing happened.'

if [ "$hit_unbounded" -eq 1 ]; then
  jq -n --arg r "$CHECKLIST

This one has NO FILTER - it would touch every row in the table. Confirm that is intended." '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      permissionDecision: "ask",
      permissionDecisionReason: $r
    }
  }'
else
  jq -n --arg c "$CHECKLIST" '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      additionalContext: $c
    }
  }'
fi
exit 0
