#!/usr/bin/env python3
"""anti_todo_card.py — The 3x5 index card system from Andreessen's personal productivity guide.

Implements the technique Marc Andreessen described in "The Pmarca Guide to Personal
Productivity" (2007):

  FRONT of the card: the day's structured to-do list — NO MORE THAN 3 to 5 things you must
                     get done today. The cap is the discipline. If everything is a priority,
                     nothing is.

  BACK of the card:  the "Anti-Todo List" — throughout the day, every time you finish
                     something (even something that wasn't on the front), you write it down
                     AND cross it off. It is a running log of what you actually got done.
                     The point is the dopamine: at the end of the day you have visible proof
                     of progress, instead of staring at an untouched to-do list and feeling
                     like you failed. The card gets thrown away at end of day. Fresh card tomorrow.

This tool is the digital version: state is one JSON file per day. The 3-5 cap on the front
is ENFORCED — a 6th must-do is rejected. The back grows freely.

NO LLM CALLS. Stdlib only. State stored at --file (default: ~/.andreessen-cards/<date>.json).

Usage:
    python anti_todo_card.py --new --must-do "Ship PMF dashboard" "Call 5 churned users" "Write board update"
    python anti_todo_card.py --did "Fixed the retention query"
    python anti_todo_card.py --did "Unblocked the data pipeline"
    python anti_todo_card.py --show
    python anti_todo_card.py --summary
    python anti_todo_card.py --sample
"""

import argparse
import datetime
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

MAX_MUST_DO = 5
MIN_RECOMMENDED = 3


def _default_dir() -> Path:
    return Path(os.environ.get("ANDREESSEN_CARD_DIR", str(Path.home() / ".andreessen-cards")))


def _card_path(file_arg: Optional[str], date: str) -> Path:
    if file_arg:
        return Path(file_arg)
    return _default_dir() / f"{date}.json"


def _load(path: Path) -> Optional[Dict[str, Any]]:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def _save(path: Path, card: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(card, indent=2), encoding="utf-8")


def _new_card(date: str, must_do: List[str]) -> Dict[str, Any]:
    if len(must_do) > MAX_MUST_DO:
        raise ValueError(
            f"{len(must_do)} must-do items given, but the cap is {MAX_MUST_DO}. "
            "That cap IS the discipline — if everything is a priority, nothing is. "
            "Cut it down to the 3-5 that actually must happen today."
        )
    return {
        "date": date,
        "front_must_do": [{"item": m, "done": False} for m in must_do],
        "back_anti_todo": [],
    }


def render_card(card: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"3x5 CARD — {card['date']}")
    out.append("=" * 50)
    out.append("FRONT — Today's must-dos (3-5 max):")
    if not card["front_must_do"]:
        out.append("  (none set — run --new --must-do ...)")
    for i, m in enumerate(card["front_must_do"], 1):
        mark = "[x]" if m["done"] else "[ ]"
        out.append(f"  {mark} {i}. {m['item']}")
    if 0 < len(card["front_must_do"]) < MIN_RECOMMENDED:
        out.append(f"  (note: {len(card['front_must_do'])} item(s) — fine, but you have room for up to {MAX_MUST_DO})")
    out.append("")
    out.append("BACK — Anti-Todo List (what you actually got done):")
    if not card["back_anti_todo"]:
        out.append("  (empty — log wins with --did \"...\" as you finish them)")
    for entry in card["back_anti_todo"]:
        out.append(f"  [x] {entry['item']}  ({entry['at']})")
    return "\n".join(out)


def summary(card: Dict[str, Any]) -> Dict[str, Any]:
    must = card["front_must_do"]
    done = [m for m in must if m["done"]]
    carry = [m["item"] for m in must if not m["done"]]
    return {
        "date": card["date"],
        "must_do_total": len(must),
        "must_do_done": len(done),
        "must_do_carryover": carry,
        "anti_todo_count": len(card["back_anti_todo"]),
        "anti_todo": [e["item"] for e in card["back_anti_todo"]],
    }


def render_summary(s: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"END-OF-DAY SUMMARY — {s['date']}")
    out.append("=" * 50)
    out.append(f"  Must-dos completed: {s['must_do_done']}/{s['must_do_total']}")
    out.append(f"  Things actually accomplished (anti-todo): {s['anti_todo_count']}")
    if s["anti_todo"]:
        out.append("  You got done today:")
        for item in s["anti_todo"]:
            out.append(f"    [x] {item}")
    if s["must_do_carryover"]:
        out.append("  Carrying over to tomorrow's card:")
        for item in s["must_do_carryover"]:
            out.append(f"    -> {item}")
    out.append("")
    out.append("  Throw this card away. Fresh card tomorrow.")
    return "\n".join(out)


def _match_and_mark_done(card: Dict[str, Any], text: str) -> bool:
    """If a logged accomplishment matches a front must-do, mark it done too."""
    tl = text.lower()
    for m in card["front_must_do"]:
        if not m["done"] and (m["item"].lower() in tl or tl in m["item"].lower()):
            m["done"] = True
            return True
    return False


def main(argv: List[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--new", action="store_true", help="Start a fresh card for today")
    p.add_argument("--must-do", nargs="*", default=None, help="Front-of-card must-dos (3-5 max)")
    p.add_argument("--did", help="Log an accomplishment to the Anti-Todo List (back of card)")
    p.add_argument("--done", help="Mark a front must-do as done by substring match")
    p.add_argument("--show", action="store_true", help="Show the current card")
    p.add_argument("--summary", action="store_true", help="End-of-day summary")
    p.add_argument("--date", default=None, help="Override date (YYYY-MM-DD); default today")
    p.add_argument("--file", default=None, help="Explicit card JSON path (overrides date-based default)")
    p.add_argument("--sample", action="store_true", help="Run a self-contained in-memory demo")
    p.add_argument("--output-format", choices=["human", "json"], default="human")
    args = p.parse_args(argv)

    if args.sample:
        card = _new_card("2026-05-24", ["Ship PMF dashboard", "Call 5 churned users", "Write board update"])
        for win in ["Fixed the retention query", "Ship PMF dashboard", "Unblocked data pipeline"]:
            if not _match_and_mark_done(card, win):
                pass
            card["back_anti_todo"].append({"item": win, "at": "demo"})
        if args.output_format == "json":
            print(json.dumps({"card": card, "summary": summary(card)}, indent=2))
        else:
            print(render_card(card))
            print()
            print(render_summary(summary(card)))
        return 0

    date = args.date or datetime.date.today().isoformat()
    path = _card_path(args.file, date)
    card = _load(path)

    if args.new:
        must = args.must_do or []
        try:
            card = _new_card(date, must)
        except ValueError as e:
            print(f"error: {e}", file=sys.stderr)
            return 2
        _save(path, card)
        print(render_card(card) if args.output_format == "human" else json.dumps(card, indent=2))
        return 0

    if card is None:
        print(f"error: no card found at {path}. Start one with --new --must-do ...", file=sys.stderr)
        return 2

    changed = False
    if args.did:
        now = datetime.datetime.now().strftime("%H:%M")
        card["back_anti_todo"].append({"item": args.did, "at": now})
        _match_and_mark_done(card, args.did)
        changed = True
    if args.done:
        if _match_and_mark_done(card, args.done):
            changed = True
        else:
            print(f"error: no front must-do matched '{args.done}'", file=sys.stderr)
            return 2
    if changed:
        _save(path, card)

    if args.summary:
        s = summary(card)
        print(json.dumps(s, indent=2) if args.output_format == "json" else render_summary(s))
    else:
        print(json.dumps(card, indent=2) if args.output_format == "json" else render_card(card))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
