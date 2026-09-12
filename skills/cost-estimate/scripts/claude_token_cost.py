#!/usr/bin/env python3
"""Extract ground-truth Claude token usage + session concurrency stats.

Reads every message.usage block and every timestamp from this project's
Claude Code session transcripts at ~/.claude/projects/<project-hash>/*.jsonl
and emits a single JSON object covering:

  - Token usage (input / cache-write / cache-read / output) and the
    equivalent per-token API cost (counterfactual — Max/Pro plans are flat).
  - Session timing: per-session span sum (capped 6h each, the active-hours
    number the skill uses as Claude throughput), uncapped span sum, and the
    wall-clock UNION of all session intervals (the operator's real time).
  - Peak concurrent sessions and average concurrency — reveal when a user
    is driving multiple Claude Code windows in parallel.

Rates below reflect published Anthropic pricing at the skill's last refresh;
update `RATES` if pricing changes.

Usage: python3 scripts/claude_token_cost.py
"""
import glob
import json
import os
import sys
from datetime import datetime, timedelta

# Per-1M-token rates (USD). Refresh when Anthropic updates pricing.
RATES = {
    "opus":   {"in": 15.00, "cache_write": 18.75, "cache_read": 1.50, "out": 75.00},
    "sonnet": {"in":  3.00, "cache_write":  3.75, "cache_read": 0.30, "out": 15.00},
    "haiku":  {"in":  0.80, "cache_write":  1.00, "cache_read": 0.08, "out":  4.00},
}

proj_hash = os.getcwd().replace("/", "-")
sessions_dir = os.path.expanduser(f"~/.claude/projects/{proj_hash}")

out = {
    "input_tokens": 0,
    "cache_creation_input_tokens": 0,
    "cache_read_input_tokens": 0,
    "output_tokens": 0,
    "cost_usd": 0.0,
    "messages": 0,
    "sessions_dir": sessions_dir,
    "sessions_found": 0,
    "active_hours_capped6": 0.0,
    "active_hours_uncapped": 0.0,
    "operator_hours_union": 0.0,
    "peak_concurrent_sessions": 0,
    "avg_concurrency": 0.0,
}

files = glob.glob(f"{sessions_dir}/*.jsonl")
out["sessions_found"] = len(files)

def parse_ts(s):
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00"))
    except (ValueError, AttributeError):
        return None

ranges = []
for f in files:
    first = last = None
    try:
        with open(f, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                try:
                    d = json.loads(line)
                except json.JSONDecodeError:
                    continue

                t = parse_ts(d.get("timestamp"))
                if t:
                    if first is None or t < first: first = t
                    if last is None or t > last:  last = t

                msg = d.get("message", {})
                u = msg.get("usage")
                if not u:
                    continue
                model = msg.get("model", "")
                tier = "opus" if "opus" in model else ("haiku" if "haiku" in model else "sonnet")
                r = RATES[tier]
                ti  = u.get("input_tokens", 0)
                tcw = u.get("cache_creation_input_tokens", 0)
                tcr = u.get("cache_read_input_tokens", 0)
                to  = u.get("output_tokens", 0)
                cost = (ti*r["in"] + tcw*r["cache_write"] + tcr*r["cache_read"] + to*r["out"]) / 1_000_000
                out["input_tokens"]                += ti
                out["cache_creation_input_tokens"] += tcw
                out["cache_read_input_tokens"]     += tcr
                out["output_tokens"]               += to
                out["cost_usd"]                    += cost
                out["messages"]                    += 1
    except OSError:
        continue
    if first and last and last > first:
        ranges.append((first, last))

# Session timing aggregates
if ranges:
    sum_secs = sum((e - s).total_seconds() for s, e in ranges)
    cap_secs = sum(min((e - s).total_seconds(), 6 * 3600) for s, e in ranges)
    out["active_hours_uncapped"] = round(sum_secs / 3600, 2)
    out["active_hours_capped6"]  = round(cap_secs / 3600, 2)

    # Peak concurrency via sweep line
    events = []
    for s, e in ranges:
        events.append((s, +1))
        events.append((e, -1))
    events.sort()
    peak = cur = 0
    for _, delta in events:
        cur += delta
        peak = max(peak, cur)
    out["peak_concurrent_sessions"] = peak

    # Wall-clock union (operator real time). Discretize to 1-minute bins —
    # cheap and precise enough for session-scale signal.
    minutes_active = set()
    for s, e in ranges:
        t = s.replace(second=0, microsecond=0)
        while t <= e:
            minutes_active.add(t)
            t += timedelta(minutes=1)
    out["operator_hours_union"] = round(len(minutes_active) / 60, 2)
    if out["operator_hours_union"] > 0:
        out["avg_concurrency"] = round(out["active_hours_uncapped"] / out["operator_hours_union"], 2)

out["cost_usd"] = round(out["cost_usd"], 2)
json.dump(out, sys.stdout, indent=2)
print()
