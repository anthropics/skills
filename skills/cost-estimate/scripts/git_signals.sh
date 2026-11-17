#!/usr/bin/env bash
# git_signals.sh — Collect process signals from git history.
#
# Prints one line of key=value pairs covering: first/last commit dates,
# project duration in days, commit count, unique contributors, and
# gross/net churn + churn ratio.
#
# Usage: bash scripts/git_signals.sh
# Output example:
#   first=2026-01-12 last=2026-04-18 duration_days=96 commits=142 \
#   contributors=3 adds=42310 dels=11025 net=31285 churn_ratio=3.84
set -eu

if ! git rev-parse --git-dir >/dev/null 2>&1; then
  echo "no_git=true"
  exit 0
fi

# `git log --reverse -1` returns the NEWEST commit (the -1 limit applies
# before --reverse), so use --max-parents=0 for the root commit instead.
first=$(git log --format="%ai" "$(git rev-list --max-parents=0 HEAD 2>/dev/null | tail -1)" 2>/dev/null | head -1 | awk '{print $1}')
last=$(git log --format="%ai" -1 2>/dev/null | awk '{print $1}')
commits=$(git rev-list --count HEAD 2>/dev/null || echo 0)
contributors=$(git shortlog -sne HEAD 2>/dev/null | wc -l | awk '{print $1}')

duration_days=$(python3 -c "
from datetime import date
f='$first'; l='$last'
if not f or not l: print(0)
else:
    d=(date.fromisoformat(l)-date.fromisoformat(f)).days
    print(max(d,1))
")

read -r adds dels < <(git log --numstat --pretty=tformat: 2>/dev/null \
  | awk '{a+=$1; d+=$2} END {printf "%d %d\n", a+0, d+0}')

net=$((adds - dels))
churn_ratio=$(python3 -c "print(f'{($adds)/max($dels,1):.2f}')")

echo "first=$first last=$last duration_days=$duration_days commits=$commits contributors=$contributors adds=$adds dels=$dels net=$net churn_ratio=$churn_ratio"
