#!/usr/bin/env python3
"""Estimate Claude-active hours by clustering commits into sessions.

Fallback used when no session logs exist at ~/.claude/projects/. Groups
commits within a 4-hour window into a single session, then estimates
each session's duration as max(span+30min, 0.5h + 18min * commit_count),
clamped to [0.5h, 4h].

Output: `sessions:<N> est_hours:<X.X>` on stdout.
Confidence: medium (±2×). Prefer claude_token_cost.py when logs exist.

Usage: python3 scripts/git_session_clustering.py
"""
import subprocess
import sys

try:
    out = subprocess.check_output(
        ["git", "log", "--format=%at", "--reverse"], text=True
    )
except subprocess.CalledProcessError:
    print("sessions:0 est_hours:0.0")
    sys.exit(0)

times = [int(t) for t in out.split() if t.strip().isdigit()]
if not times:
    print("sessions:0 est_hours:0.0")
    sys.exit(0)

GAP = 4 * 3600
sessions, current = [], [times[0]]
for t in times[1:]:
    if t - current[-1] <= GAP:
        current.append(t)
    else:
        sessions.append(current)
        current = [t]
sessions.append(current)

total_h = 0.0
for s in sessions:
    span_h    = (s[-1] - s[0]) / 3600
    by_span   = max(0.5, min(4.0, span_h + 0.5))       # span + 30min buffer
    by_density = min(4.0, 0.5 + 0.3 * len(s))          # 0.5h base + 18min/commit
    total_h += max(by_span, by_density)

print(f"sessions:{len(sessions)} est_hours:{total_h:.1f}")
