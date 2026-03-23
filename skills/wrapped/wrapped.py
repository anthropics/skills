#!/usr/bin/env python3
"""Claude Code Wrapped — your year in review."""

import json
import os
import sys
import collections
import datetime
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

# ── UTF-8 stdout + ANSI on Windows ──────────────────────────────────────────
if os.name == "nt":
    sys.stdout.reconfigure(encoding="utf-8")
    try:
        import ctypes
        ctypes.windll.kernel32.SetConsoleMode(
            ctypes.windll.kernel32.GetStdHandle(-11), 7
        )
    except Exception:
        pass

# ── ANSI colour palette ──────────────────────────────────────────────────────
class C:
    R       = "\033[0m"
    B       = "\033[1m"
    DIM     = "\033[2m"
    ITALIC  = "\033[3m"
    BLACK   = "\033[30m"
    RED     = "\033[31m"
    GREEN   = "\033[32m"
    YELLOW  = "\033[33m"
    BLUE    = "\033[34m"
    MAGENTA = "\033[35m"
    CYAN    = "\033[36m"
    WHITE   = "\033[37m"
    BRED    = "\033[91m"
    BGREEN  = "\033[92m"
    BYELLOW = "\033[93m"
    BBLUE   = "\033[94m"
    BMAGENTA= "\033[95m"
    BCYAN   = "\033[96m"
    BWHITE  = "\033[97m"

def dim(t):        return f"{C.DIM}{t}{C.R}"
def col(t, c):     return f"{c}{t}{C.R}"
def bc(t, c):      return f"{C.B}{c}{t}{C.R}"

def _vis_len(s):
    import re
    return len(re.sub(r"\033\[[0-9;]*m", "", s))


# ── Interactive detection ─────────────────────────────────────────────────────
def _is_interactive():
    """True only when attached to a real user-facing terminal."""
    if not sys.stdout.isatty():
        return False
    if os.name == "nt":
        try:
            import ctypes
            return ctypes.windll.kernel32.GetConsoleWindow() != 0
        except Exception:
            return False
    return True

INTERACTIVE = _is_interactive()

# ── Keypress ─────────────────────────────────────────────────────────────────
def wait_key():
    if os.name == "nt":
        import msvcrt
        return msvcrt.getch()
    else:
        import tty, termios
        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            return sys.stdin.read(1).encode()
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)


# ── Data loading ─────────────────────────────────────────────────────────────
CLAUDE_DIR = Path.home() / ".claude"
DERIVED_CACHE = CLAUDE_DIR / "wrapped-cache.json"

def load_stats():
    p = CLAUDE_DIR / "stats-cache.json"
    return json.loads(p.read_text()) if p.exists() else {}

def load_history():
    p = CLAUDE_DIR / "history.jsonl"
    if not p.exists():
        return []
    out = []
    for line in p.read_bytes().decode("utf-8", errors="ignore").splitlines():
        try:
            out.append(json.loads(line))
        except Exception:
            pass
    return out

def _stats_cache_mtime():
    """mtime of stats-cache.json — O(1), used as proxy for 'has Claude run since last wrap'."""
    try:
        return (CLAUDE_DIR / "stats-cache.json").stat().st_mtime
    except Exception:
        return 0.0

def _load_derived_cache():
    if not DERIVED_CACHE.exists():
        return None
    try:
        if DERIVED_CACHE.stat().st_mtime >= _stats_cache_mtime():
            return json.loads(DERIVED_CACHE.read_text())
    except Exception:
        pass
    return None

def _save_derived_cache(tool_counts, file_counts, slash_counts, avg_prompt_len):
    try:
        DERIVED_CACHE.write_text(json.dumps({
            "tool_stats":   dict(tool_counts),
            "file_stats":   dict(file_counts),
            "slash_stats":  dict(slash_counts),
            "avg_prompt_len": avg_prompt_len,
        }))
    except Exception:
        pass

def _list_jsonl_files():
    """Fast file listing via os.scandir (avoids pathlib overhead on large trees)."""
    projects = CLAUDE_DIR / "projects"
    if not projects.exists():
        return []
    files = []
    try:
        with os.scandir(projects) as it:
            for proj in it:
                if not proj.is_dir(follow_symlinks=False):
                    continue
                try:
                    with os.scandir(proj.path) as fit:
                        for f in fit:
                            if f.name.endswith(".jsonl") and f.is_file():
                                files.append(Path(f.path))
                except Exception:
                    pass
    except Exception:
        pass
    return files


# ── Stat crunching ───────────────────────────────────────────────────────────

def _process_one_file(path):
    """Parse a single JSONL, return (tool_counter, file_counter). Only parses assistant lines."""
    t, f = collections.Counter(), collections.Counter()
    try:
        for line in path.read_bytes().decode("utf-8", errors="ignore").splitlines():
            if '"tool_use"' not in line:
                continue
            try:
                m = json.loads(line)
            except Exception:
                continue
            if m.get("type") != "assistant":
                continue
            for c in m.get("message", {}).get("content", []) or []:
                if not isinstance(c, dict) or c.get("type") != "tool_use":
                    continue
                name = c["name"]
                t[name] += 1
                if name in ("Edit", "Write", "Read"):
                    fp = c.get("input", {}).get("file_path", "")
                    if fp:
                        f[Path(fp).name] += 1
    except Exception:
        pass
    return t, f

def compute_session_stats():
    """Return (tool_counts, file_counts), reading JSONL files in parallel."""
    all_files = _list_jsonl_files()
    workers = min(16, max(1, len(all_files)))
    with ThreadPoolExecutor(max_workers=workers) as ex:
        results = list(ex.map(_process_one_file, all_files))

    tools = collections.Counter()
    files = collections.Counter()
    for t, f in results:
        tools.update(t)
        files.update(f)
    return tools, files

def slash_stats(history):
    counts = collections.Counter()
    for e in history:
        d = e.get("display", "")
        if d.startswith("/"):
            counts[d.split()[0]] += 1
    return counts

def day_of_week_from_stats(stats):
    """Derive day-of-week from dailyActivity in stats-cache — no file I/O."""
    days = collections.Counter()
    for d in stats.get("dailyActivity", []):
        date_str = d.get("date", "")
        if not date_str:
            continue
        try:
            dt = datetime.datetime.fromisoformat(date_str.replace("Z", "+00:00"))
            days[dt.strftime("%a")] += d.get("messageCount", 1)
        except Exception:
            pass
    return days

def prompt_lengths(history):
    return [len(e.get("display", "")) for e in history if e.get("display")]


# ── Cost calculation ─────────────────────────────────────────────────────────
# USD per million tokens: (input, output, cache_read, cache_write)
MODEL_PRICES = {
    "haiku":   (0.80,  4.00,  0.08,  1.00),
    "sonnet":  (3.00, 15.00,  0.30,  3.75),
    "opus":   (15.00, 75.00,  1.50, 18.75),
    "default": (3.00, 15.00,  0.30,  3.75),
}

def get_model_price(model_name):
    name = model_name.lower()
    if "haiku"  in name: return MODEL_PRICES["haiku"]
    if "sonnet" in name: return MODEL_PRICES["sonnet"]
    if "opus"   in name: return MODEL_PRICES["opus"]
    return MODEL_PRICES["default"]

def calc_cost(model_usage):
    total, breakdown = 0.0, {}
    for model, d in model_usage.items():
        inp = d.get("inputTokens", 0)
        out = d.get("outputTokens", 0)
        cr  = d.get("cacheReadInputTokens", 0)
        cw  = d.get("cacheCreationInputTokens", 0)
        pi, po, pcr, pcw = get_model_price(model)
        cost = (inp * pi + out * po + cr * pcr + cw * pcw) / 1_000_000
        breakdown[model] = cost
        total += cost
    return total, breakdown


# ── Archetype engine ─────────────────────────────────────────────────────────
ARCHETYPES = [
    ("automator",    "🤖", "The Automator",      "If it can be scripted, it will be scripted."),
    ("archaeologist","🏺", "The Archaeologist",  "You study every line before daring to touch one."),
    ("builder",      "🏗️ ", "The Builder",        "You ship code like it's going out of style."),
    ("delegator",    "👑", "The Delegator",      "Why do it yourself when AI can do it for you?"),
    ("explorer",     "🗺️ ", "The Explorer",       "No file is safe from your searches."),
    ("researcher",   "🔍", "The Researcher",     "Stack Overflow who? You go straight to the source."),
    ("browser_pilot","🌐", "The Browser Pilot",  "You automate the web like it owes you money."),
    ("planner",      "📋", "The Planner",        "Organised chaos is still organised."),
    ("night_owl",    "🦉", "The Night Owl",      "You debug best when the world is asleep."),
    ("early_bird",   "🌅", "The Early Bird",     "First commit before most devs open their eyes."),
    ("lunch_coder",  "☀️ ", "The Lunch Coder",    "Why eat when you can ship?"),
    ("marathoner",   "🏃", "The Marathon Runner","You don't stop until it's done. Or 3 AM."),
    ("sprinter",     "⚡", "The Sprinter",       "In, out, shipped. No time for ceremonies."),
    ("novelist",     "📖", "The Novelist",       "Your prompts have full character development."),
    ("minimalist",   "🎯", "The Minimalist",     "Less words, more code."),
    ("refactorer",   "🔄", "The Refactorer",     "You polish code like it's going in a museum."),
    ("all_rounder",  "🌟", "The All-Rounder",    "A perfect blend — the rare well-balanced dev."),
]
ARCHETYPE_MAP = {a[0]: a for a in ARCHETYPES}

def score_archetypes(tool_counts, history, stats):
    scores = collections.defaultdict(float)
    total = sum(tool_counts.values()) or 1

    def pct(keys):
        return sum(tool_counts.get(k, 0) for k in keys) / total

    bash_p    = pct(["Bash"])
    edit_p    = pct(["Edit"])
    read_p    = pct(["Read"])
    grep_p    = pct(["Grep"])
    write_p   = pct(["Write"])
    glob_p    = pct(["Glob"])
    agent_p   = pct(["Agent"])
    web_p     = pct(["WebSearch", "WebFetch"])
    browser_p = pct([k for k in tool_counts if "chrome" in k.lower()])
    task_p    = pct([k for k in tool_counts if "Task" in k])

    if bash_p   > 0.28:              scores["automator"]     += bash_p * 3
    if read_p + grep_p > 0.28:       scores["archaeologist"] += (read_p + grep_p) * 2.5
    if edit_p + write_p > 0.32:      scores["builder"]       += (edit_p + write_p) * 2
    if agent_p  > 0.03:              scores["delegator"]     += agent_p * 8
    if glob_p + grep_p > 0.12:       scores["explorer"]      += (glob_p + grep_p) * 3
    if web_p    > 0.03:              scores["researcher"]    += web_p * 6
    if browser_p > 0.03:             scores["browser_pilot"] += browser_p * 8
    if task_p   > 0.03:              scores["planner"]       += task_p * 6

    hour_counts = stats.get("hourCounts", {})
    if hour_counts:
        peak = int(max(hour_counts, key=lambda h: hour_counts[h]))
        if peak >= 22 or peak <= 4:  scores["night_owl"]   += 2.0
        elif 5 <= peak <= 8:          scores["early_bird"]  += 2.0
        elif 12 <= peak <= 14:        scores["lunch_coder"] += 1.5

    longest_ms = stats.get("longestSession", {}).get("duration", 0)
    if longest_ms > 3_600_000 * 3:   scores["marathoner"] += 1.5
    if longest_ms > 3_600_000 * 6:   scores["marathoner"] += 1.0

    total_sessions  = stats.get("totalSessions", 1)
    total_messages  = stats.get("totalMessages", 0)
    avg_per_session = total_messages / total_sessions if total_sessions else 0
    if avg_per_session < 12 and total_sessions >= 3:
        scores["sprinter"] += 1.5

    lengths = prompt_lengths(history)
    if lengths:
        avg = sum(lengths) / len(lengths)
        if avg > 180:  scores["novelist"]   += 1.5
        if avg < 35:   scores["minimalist"] += 1.5

    if tool_counts.get("Edit", 0) > tool_counts.get("Write", 0) * 4:
        scores["refactorer"] += 1.2

    if not scores:
        scores["all_rounder"] += 1.0

    return sorted(scores.items(), key=lambda x: -x[1])


# ── Render primitives ─────────────────────────────────────────────────────────
W = 62

def bar(value, max_val, width=22, fill="█", empty="░", color=C.BCYAN):
    filled = int((value / max_val) * width) if max_val else 0
    return col(fill * filled, color) + col(empty * (width - filled), C.DIM)

def fmt_n(n):
    if n >= 1_000_000: return f"{n/1_000_000:.1f}M"
    if n >= 1_000:     return f"{n/1_000:.1f}K"
    return str(int(n))

def fmt_ms(ms):
    if ms < 60_000:    return f"{ms/1000:.0f}s"
    if ms < 3_600_000: return f"{ms/60_000:.0f}m"
    return f"{ms/3_600_000:.1f}h"

def fmt_cost(usd):
    if usd < 0.005: return "< $0.01"
    if usd < 10:    return f"${usd:.2f}"
    if usd < 1000:  return f"${usd:,.2f}"
    return f"${usd:,.0f}"

def hline(char="─", color=C.DIM):
    print(col(f"  {char * W}", color))

def stat_row(emoji, label, value, val_color=C.BWHITE):
    label_part = f"  {emoji}  {dim(label + ':')}"
    pad = 40 - _vis_len(label_part)
    print("    " + label_part + " " * max(pad, 1) + bc(value, val_color))

def section_box(title, emoji, color=C.BCYAN):
    label = f"  {emoji}  {title}  "
    pad_l = (W - _vis_len(label)) // 2
    pad_r = W - _vis_len(label) - pad_l
    print()
    print(col(f"  ╔{'═' * W}╗", color))
    print(col("  ║", color) + " " * pad_l + bc(label, color) + " " * pad_r + col("║", color))
    print(col(f"  ╚{'═' * W}╝", color))
    print()

def progress_bar(current, total, color=C.BCYAN):
    """Thin slide progress bar at top of screen."""
    filled = int((current / total) * W) if total else 0
    filled = max(filled, 1)
    bar_str = col("▓" * filled, color) + col("░" * (W - filled), C.DIM)
    pct = f" {current}/{total}"
    print(f"  {bar_str}{dim(pct)}")

def nav_footer(current, total):
    print()
    hline()
    dots = "  "
    for j in range(total):
        dots += (bc("◆", C.BCYAN) if j == current else col("◇", C.DIM))
        if j < total - 1:
            dots += " "
    hint = col("  SPACE / ENTER", C.DIM) + "  " + bc("next", C.BWHITE) + \
           "    " + col("Q", C.DIM) + "  " + bc("quit", C.DIM)
    print(dots + "      " + hint)
    hline()
    print()


# ── Slides ────────────────────────────────────────────────────────────────────

def slide_title(stats, total_messages, total_sessions):
    hc = C.BMAGENTA
    print()
    print(col(f"  ╔{'═' * W}╗", hc))
    print(col(f"  ║{'':^{W}}║", hc))
    for line in [
        bc("  ██████╗██╗      █████╗ ██╗   ██╗██████╗ ███████╗  ", C.BCYAN),
        bc(" ██╔════╝██║     ██╔══██╗██║   ██║██╔══██╗██╔════╝  ", C.BBLUE),
        bc(" ██║     ██║     ███████║██║   ██║██║  ██║█████╗    ", C.BCYAN),
        bc(" ██║     ██║     ██╔══██║██║   ██║██║  ██║██╔══╝    ", C.BBLUE),
        bc(" ╚██████╗███████╗██║  ██║╚██████╔╝██████╔╝███████╗  ", C.BCYAN),
        bc("  ╚═════╝╚══════╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚══════╝ ", C.BBLUE),
    ]:
        pad = W - _vis_len(line)
        print(col("  ║", hc) + line + " " * max(pad, 0) + col("║", hc))
    print(col(f"  ║{'':^{W}}║", hc))
    for lbl, lc in [("✦  C O D E   W R A P P E D  ✦", C.BYELLOW),
                     ("your year in claude code", C.DIM)]:
        pad_l = (W - len(lbl)) // 2
        pad_r = W - len(lbl) - pad_l
        print(col("  ║", hc) + " " * pad_l + col(lbl, lc) + " " * pad_r + col("║", hc))
    print(col(f"  ║{'':^{W}}║", hc))
    print(col(f"  ╚{'═' * W}╝", hc))
    print()

    # Quick peek stats on title slide
    hline("─", C.DIM)
    print()
    cols = [
        (bc(fmt_n(total_messages), C.BWHITE),  dim("messages")),
        (bc(str(total_sessions),   C.BGREEN),  dim("sessions")),
    ]
    first_ts = stats.get("firstSessionDate", "")
    if first_ts:
        try:
            first_dt = datetime.datetime.fromisoformat(first_ts.replace("Z", "+00:00"))
            cols.append((bc(first_dt.strftime("%b %Y"), C.BYELLOW), dim("since")))
        except Exception:
            pass

    col_w = W // len(cols)
    top_row = ""
    bot_row = ""
    for val, lbl in cols:
        val_pad = col_w - _vis_len(val)
        lbl_pad = col_w - _vis_len(lbl)
        top_row += "  " + val + " " * max(val_pad - 2, 0)
        bot_row += "  " + lbl + " " * max(lbl_pad - 2, 0)
    print(top_row)
    print(bot_row)
    print()
    hline("─", C.DIM)
    print()
    hint = "Press  SPACE  or  ENTER  to begin  ›"
    pad  = (W - len(hint)) // 2 + 2
    print(" " * pad + col(hint, C.DIM))
    print()


def slide_glance(stats, total_tool_calls, total_tokens):
    section_box("YOUR YEAR AT A GLANCE", "📊")

    total_sessions = stats.get("totalSessions", 0)
    total_messages = stats.get("totalMessages", 0)
    first_ts = stats.get("firstSessionDate", "")
    first_str = "Unknown"
    if first_ts:
        try:
            first_dt  = datetime.datetime.fromisoformat(first_ts.replace("Z", "+00:00"))
            first_str = first_dt.strftime("%B %d, %Y")
        except Exception:
            first_str = first_ts[:10]

    avg_msgs = f"{total_messages / total_sessions:.1f}" if total_sessions else "—"

    stat_row("💬", "Total messages",     fmt_n(total_messages),   C.BWHITE)
    stat_row("🔁", "Sessions",           str(total_sessions),     C.BGREEN)
    stat_row("🛠 ", "Tool calls",         fmt_n(total_tool_calls), C.BCYAN)
    stat_row("📨", "Avg msgs / session", avg_msgs,                C.BYELLOW)
    stat_row("🧠", "Tokens processed",   fmt_n(total_tokens),     C.BMAGENTA)
    stat_row("📅", "First session",      first_str,               C.DIM)


def slide_tools(tools):
    section_box("TOOLS YOU LOVED", "🔧")

    TOOL_COLOR = {
        "Bash":  C.BGREEN,  "Edit":   C.BCYAN,    "Read":  C.BBLUE,
        "Write": C.BYELLOW, "Grep":   C.BMAGENTA,  "Glob":  C.BRED,
        "Agent": C.BWHITE,
    }
    top  = tools.most_common(8)
    maxc = top[0][1]
    tot  = sum(tools.values())

    def clean(name):
        if name.startswith("mcp__"):
            parts = name.split("__")
            return f"mcp:{parts[-1]}"[:18]
        return name[:18]

    for name, count in top:
        clr   = TOOL_COLOR.get(name, C.WHITE)
        pct   = count / tot * 100
        chart = bar(count, maxc, 22, color=clr)
        label = bc(f"{clean(name):<18}", clr)
        print(f"    {label} │{chart}│ {bc(f'{fmt_n(count):>5}', C.BWHITE)}  {dim(f'{pct:.0f}%')}")


def slide_hours(stats):
    section_box("WHEN YOU CODE", "⏰")

    hour_counts = stats.get("hourCounts", {})
    max_h = max(int(v) for v in hour_counts.values())
    peak  = int(max(hour_counts, key=lambda h: hour_counts[h]))

    hour_data = sorted(
        [(int(h), int(v)) for h, v in hour_counts.items() if int(v) > 0],
        key=lambda x: -x[1]
    )[:8]
    hour_data.sort(key=lambda x: x[0])

    for h, cnt in hour_data:
        h12      = h % 12 or 12
        am_pm    = "AM" if h < 12 else "PM"
        is_peak  = (h == peak)
        clr      = C.BYELLOW if is_peak else C.BCYAN
        label    = f"{h12:2d} {am_pm}"
        lbl_fmt  = bc(label, C.BYELLOW) if is_peak else dim(label)
        chart    = bar(cnt, max_h, 28, color=clr)
        mark     = f"  {bc('◀ peak', C.BYELLOW)}" if is_peak else ""
        print(f"    {lbl_fmt} │{chart}│ {bc(fmt_n(cnt), C.BWHITE)}{mark}")

    h12   = peak % 12 or 12
    am_pm = "AM" if peak < 12 else "PM"
    print(f"\n    {dim('Peak coding hour:')}  {bc(f'{h12}:00 {am_pm}', C.BYELLOW)} ✦")


def slide_days(dow):
    section_box("YOUR CODING DAYS", "📆")

    order   = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
    day_clr = {
        "Mon": C.BBLUE, "Tue": C.BCYAN,    "Wed": C.BGREEN,
        "Thu": C.BYELLOW,"Fri": C.BMAGENTA, "Sat": C.BRED, "Sun": C.BWHITE,
    }
    max_d = max(dow.values()) if dow.values() else 1
    for day in order:
        cnt   = dow.get(day, 0)
        clr   = day_clr[day]
        chart = bar(cnt, max_d, 24, color=clr)
        print(f"    {bc(day, clr)} │{chart}│ {bc(fmt_n(cnt), C.BWHITE)}")


def slide_legendary(stats):
    section_box("YOUR LEGENDARY SESSION", "🏆", C.BYELLOW)

    longest  = stats.get("longestSession", {})
    dur      = fmt_ms(longest.get("duration", 0))
    msgs     = longest.get("messageCount", 0)
    ts       = longest.get("timestamp", "")
    date_str = "Unknown"
    if ts:
        try:
            dt       = datetime.datetime.fromisoformat(ts.replace("Z", "+00:00"))
            date_str = dt.strftime("%B %d, %Y at %I:%M %p")
        except Exception:
            date_str = ts[:10]

    stat_row("⏱ ", "Duration",          dur,         C.BYELLOW)
    stat_row("💬", "Messages exchanged", fmt_n(msgs), C.BWHITE)
    stat_row("📅", "Date",               date_str,    C.DIM)

    hrs = longest.get("duration", 0) / 3_600_000
    if hrs > 3:
        quote = '"I should go to bed."  \u2014 You, probably, at some point'
        print(f"\n    {dim(quote)}")


def slide_models(model_usage):
    section_box("YOUR AI FLEET", "🤖")

    model_toks = {
        m: (d.get("inputTokens", 0) + d.get("outputTokens", 0)
            + d.get("cacheReadInputTokens", 0) + d.get("cacheCreationInputTokens", 0))
        for m, d in model_usage.items()
    }
    total_mt  = sum(model_toks.values()) or 1
    sorted_mt = sorted(model_toks.items(), key=lambda x: -x[1])
    max_mt    = sorted_mt[0][1] if sorted_mt else 1
    COLORS    = [C.BCYAN, C.BMAGENTA, C.BYELLOW, C.BGREEN, C.BRED]

    def clean(name):
        return name.replace("claude-", "").replace("-202", " '2")[:26]

    for i, (model, toks) in enumerate(sorted_mt):
        clr   = COLORS[i % len(COLORS)]
        pct   = toks / total_mt * 100
        chart = bar(toks, max_mt, 22, color=clr)
        label = bc(f"{clean(model):<26}", clr)
        print(f"    {label} │{chart}│ {bc(f'{pct:.0f}%', C.BWHITE)}")


def slide_costs(model_usage, stats):
    section_box("YOUR CLAUDE BILL", "💰", C.BGREEN)

    total_cost, breakdown = calc_cost(model_usage)

    # Derive days active
    first_ts    = stats.get("firstSessionDate", "")
    days_active = 1
    if first_ts:
        try:
            first_dt    = datetime.datetime.fromisoformat(first_ts.replace("Z", "+00:00"))
            now         = datetime.datetime.now(datetime.timezone.utc)
            days_active = max((now - first_dt).days, 1)
        except Exception:
            pass

    daily   = total_cost / days_active
    weekly  = daily * 7
    monthly = daily * 30

    # Per-model cost bars
    COLORS          = [C.BCYAN, C.BMAGENTA, C.BYELLOW, C.BGREEN, C.BRED]
    sorted_breakdown = sorted(breakdown.items(), key=lambda x: -x[1])
    max_cost         = sorted_breakdown[0][1] if sorted_breakdown else 1

    def clean(name):
        return name.replace("claude-", "").replace("-202", " '2")[:26]

    for i, (model, cost) in enumerate(sorted_breakdown):
        clr   = COLORS[i % len(COLORS)]
        chart = bar(cost, max_cost, 22, color=clr)
        label = bc(f"{clean(model):<26}", clr)
        print(f"    {label} │{chart}│ {bc(fmt_cost(cost), C.BWHITE)}")

    print()
    hline("─", C.BGREEN)
    print()
    stat_row("💵", "Total spent",  fmt_cost(total_cost), C.BYELLOW)
    stat_row("📅", "Per day",      fmt_cost(daily),      C.BGREEN)
    stat_row("📆", "Per week",     fmt_cost(weekly),     C.BCYAN)
    stat_row("🗓 ", "Per month",   fmt_cost(monthly),    C.BMAGENTA)
    print()
    print(f"    {dim('* Estimates based on public Anthropic pricing')}")


def slide_files(files):
    section_box("FILES YOU COULDN'T QUIT", "📁")

    top_files = files.most_common(7)
    max_f     = top_files[0][1]
    medals    = ["🥇", "🥈", "🥉", "  4.", "  5.", "  6.", "  7."]
    for i, (fname, cnt) in enumerate(top_files):
        chart = bar(cnt, max_f, 20, color=C.BCYAN)
        print(f"    {medals[i]}  {bc(f'{fname:<26}', C.BCYAN)} │{chart}│ {bc(str(cnt), C.BWHITE)}")


def slide_commands(slashes):
    section_box("YOUR GO-TO COMMANDS", "⌨️ ")

    top    = slashes.most_common(6)
    max_c  = top[0][1]
    for cmd, cnt in top:
        chart = bar(cnt, max_c, 20, color=C.BGREEN)
        print(f"    {bc(f'{cmd:<28}', C.BGREEN)} │{chart}│ {bc(str(cnt), C.BWHITE)}")


def slide_archetype(archetypes):
    ac = C.BYELLOW
    print()
    print(col(f"  ╔{'═' * W}╗", ac))
    print(col(f"  ║{'':^{W}}║", ac))
    title = "✦  YOUR DEVELOPER ARCHETYPE  ✦"
    pad_l = (W - len(title)) // 2
    pad_r = W - len(title) - pad_l
    print(col("  ║", ac) + " " * pad_l + bc(title, ac) + " " * pad_r + col("║", ac))
    print(col(f"  ║{'':^{W}}║", ac))
    print(col(f"  ╚{'═' * W}╝", ac))
    print()

    shown = 0
    for arch_id, _ in archetypes[:5]:
        if shown >= 3:
            break
        arch = ARCHETYPE_MAP.get(arch_id)
        if not arch:
            continue
        _, emoji, name, tagline = arch
        print(f"  {emoji}  {bc(name, C.BYELLOW)}")
        print(f"      {dim(tagline)}")
        print()
        shown += 1

    if not shown:
        _, emoji, name, tagline = ARCHETYPE_MAP["all_rounder"]
        print(f"  {emoji}  {bc(name, C.BYELLOW)}")
        print(f"      {dim(tagline)}")
        print()


# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    sys.stdout.write("\nLoading your Claude Code history...\r")
    sys.stdout.flush()

    # Fast: single JSON files
    stats   = load_stats()
    history = load_history()

    # Fast: derived from stats-cache.json (no file I/O)
    dow = day_of_week_from_stats(stats)

    # Parallelised + cached: reads project JSONL files only when needed
    cached = _load_derived_cache()
    if cached:
        tools   = collections.Counter(cached["tool_stats"])
        files   = collections.Counter(cached["file_stats"])
        slashes = collections.Counter(cached["slash_stats"])
    else:
        tools, files = compute_session_stats()
        slashes      = slash_stats(history)
        avg_len      = sum(prompt_lengths(history)) / max(len(history), 1)
        _save_derived_cache(tools, files, slashes, avg_len)

    archetypes = score_archetypes(tools, history, stats)

    model_usage      = stats.get("modelUsage", {})
    daily_activity   = stats.get("dailyActivity", [])
    total_tool_calls = sum(d.get("toolCallCount", 0) for d in daily_activity) or sum(tools.values())
    total_tokens     = sum(
        v.get("inputTokens", 0) + v.get("outputTokens", 0)
        + v.get("cacheReadInputTokens", 0) + v.get("cacheCreationInputTokens", 0)
        for v in model_usage.values()
    )
    total_messages = stats.get("totalMessages", 0)
    total_sessions = stats.get("totalSessions", 0)

    # ── Build slide list ──────────────────────────────────────────────────────
    slides = []
    slides.append(("title",     lambda: slide_title(stats, total_messages, total_sessions)))
    slides.append(("glance",    lambda: slide_glance(stats, total_tool_calls, total_tokens)))
    if tools:
        slides.append(("tools", lambda: slide_tools(tools)))
    if stats.get("hourCounts"):
        slides.append(("hours", lambda: slide_hours(stats)))
    if dow:
        slides.append(("days",  lambda: slide_days(dow)))
    if stats.get("longestSession"):
        slides.append(("legendary", lambda: slide_legendary(stats)))
    if model_usage:
        slides.append(("models", lambda: slide_models(model_usage)))
        slides.append(("costs",  lambda: slide_costs(model_usage, stats)))
    if files:
        slides.append(("files",    lambda: slide_files(files)))
    if slashes:
        slides.append(("commands", lambda: slide_commands(slashes)))
    slides.append(("archetype", lambda: slide_archetype(archetypes)))

    total = len(slides)

    if INTERACTIVE:
        # ── Interactive slideshow ─────────────────────────────────────────────
        i = 0
        while i < total:
            os.system("cls" if os.name == "nt" else "clear")
            if i > 0:
                progress_bar(i, total - 1)
            _, fn = slides[i]
            fn()
            is_last = (i == total - 1)
            if is_last:
                print()
                hline()
                pad_l = (W - len("Generated by  claude code /wrapped")) // 2
                print(" " * (pad_l + 2) + dim("Generated by ") + bc("claude code /wrapped", C.BCYAN))
                hline()
                print()
                print(f"  {dim('Press any key to exit...')}")
                print()
                wait_key()
                os.system("cls" if os.name == "nt" else "clear")
                break
            nav_footer(i, total)
            key = wait_key()
            if key in (b'q', b'Q', b'\x03', b'\x1b'):
                os.system("cls" if os.name == "nt" else "clear")
                break
            i += 1
    else:
        # ── Non-interactive: print all slides sequentially ────────────────────
        for i, (_, fn) in enumerate(slides):
            if i > 0:
                progress_bar(i, total - 1)
                print()
            fn()
        print()
        hline()
        pad_l = (W - len("Generated by  claude code /wrapped")) // 2
        print(" " * (pad_l + 2) + dim("Generated by ") + bc("claude code /wrapped", C.BCYAN))
        hline()
        print()


if __name__ == "__main__":
    main()
