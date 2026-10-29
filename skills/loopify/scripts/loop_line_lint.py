#!/usr/bin/env python3
"""
The loop-line lint — the eight rules a loopify line must pass, as code.

The same rules are written in prose in skills/loopify/SKILL.md ("Loop-line rules"); this file
is the executable form, used by tests/test_manifests.py against the shipped example and usable
on any line you are about to paste:

    python3 evals/loop_line_lint.py "/loop 20m Run one cycle of /abs/path/.loop/job.md — read it first, obey its stop rule (30 ticks or the PR merges), log the tick."

Exit 0 = passes; 1 = at least one rule failed (each failure printed). Notes are advisory.
No third-party deps; standard library only. Every threshold below is sourced in SKILL.md.
"""
import re
import sys

MAX_CHARS = 220
INTERVAL_RE = re.compile(r"^(\d+)([smhd])$")
# The five phrasings the shipped /loop skill treats as daily cadence (Claude Code 2.1.252,
# "Offer cloud first" block). With daily phrasing and no parsed interval, "This session only"
# makes /loop refuse to schedule locally — the user ends with nothing scheduled.
DAILY_PHRASES = ("every morning", "daily", "every day", "each night", "every weekday")
ABS_PATH_RE = re.compile(r"Run one cycle of (\S+?\.md)(?=[\s,.;:—–-]|$)")


def interval_minutes(token):
    m = INTERVAL_RE.match(token)
    if not m:
        return None
    n, unit = int(m.group(1)), m.group(2)
    return {"s": max(1, -(-n // 60)), "m": n, "h": n * 60, "d": n * 1440}[unit]


def lint_loop_line(line, expected_mode=None):
    """Return (ok, failures, notes). `expected_mode` is 'fixed' | 'self-paced' | None (rule 8)."""
    failures, notes = [], []
    raw = line.strip()
    if not raw.startswith("/loop "):
        failures.append("line must start with `/loop `")
        return False, failures, notes
    rest = raw[len("/loop "):].strip()
    tokens = rest.split()
    first = tokens[0] if tokens else ""
    mode = "fixed" if INTERVAL_RE.match(first) else "self-paced"
    prompt = rest[len(first):].strip() if mode == "fixed" else rest

    # 1. starts with the interval token (fixed) or the verb (self-paced)
    if not prompt.startswith("Run "):
        failures.append("rule 1: the prompt must start with the verb `Run` "
                        "(after the interval token in fixed mode)")

    # 2. `Run one cycle of <ABSOLUTE PATH>` — absolute, never ~/ or relative, never bare
    m = ABS_PATH_RE.search(prompt)
    if not m:
        failures.append("rule 2: must say `Run one cycle of <path>.md`")
    else:
        path = m.group(1)
        if path.startswith("~"):
            failures.append(f"rule 2: `{path}` is a ~ path — the tick reads files by absolute path; expand it")
        elif not path.startswith("/"):
            failures.append(f"rule 2: `{path}` is relative — use the absolute path")

    # 3. carries the stop rule (a tick-cap number) and the words "log the tick"
    if "stop rule" not in prompt:
        failures.append("rule 3: must say `obey its stop rule (...)`")
    if not re.search(r"\b\d+\s+ticks?\b", prompt):
        failures.append("rule 3: the stop rule must name the tick cap (e.g. `30 ticks`)")
    if "log the tick" not in prompt:
        failures.append("rule 3: must end with the words `log the tick`")

    # 4. ≤ 220 characters
    if len(raw) > MAX_CHARS:
        failures.append(f"rule 4: {len(raw)} characters, over the {MAX_CHARS} cap")

    # 5. no daily phrasing anywhere (the slug in the path counts); no bare $
    low = raw.lower()
    for phrase in DAILY_PHRASES:
        if phrase in low or phrase.replace(" ", "-") in low:
            failures.append(f"rule 5: contains daily phrasing `{phrase}` — /loop may refuse to schedule it locally")
    if re.search(r"(?<!\\)\$", raw):
        failures.append("rule 5: contains a bare `$` — escape or reword")

    # 6. never a one-shot slash command as the prompt
    if prompt.startswith("/"):
        failures.append("rule 6: the prompt is a slash command — a one-shot command re-run every tick "
                        "does its one-shot work every tick")

    # 7. ≥ 60 min → the handoff must add the cloud-question caveat
    if mode == "fixed":
        mins = interval_minutes(first)
        if mins is not None and mins >= 60:
            notes.append("rule 7: interval ≥ 60 min — the handoff must add: you may be asked whether "
                         "to make this a cloud schedule; answer `This session only` (a cloud routine "
                         "has no local files, so the brief's path does not exist there)")

    # 8. the line's mode matches the brief's Standing decision 1
    if expected_mode and expected_mode != mode:
        failures.append(f"rule 8: line is {mode} but the brief's Standing decision 1 says {expected_mode}")

    return not failures, failures, notes


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    ok, failures, notes = lint_loop_line(argv[1], argv[2] if len(argv) > 2 else None)
    for f in failures:
        print(f"FAIL: {f}")
    for n in notes:
        print(f"NOTE: {n}")
    print(f"{'PASS' if ok else 'FAIL'}: loop-line lint ({len(argv[1].strip())} chars)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
