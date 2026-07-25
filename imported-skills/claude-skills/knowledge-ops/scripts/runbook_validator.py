#!/usr/bin/env python3
"""runbook_validator.py

Validate a runbook by checking each step against six required attributes:

  1. Named owner       (not "the team", not "ops")
  2. Expected duration (concrete number + unit)
  3. Observable success signal
  4. Observable failure signal
  5. Rollback path     (or explicit "cannot roll back — escalate to X")
  6. Escalation contact

Output is a per-step traffic-light + overall validity score 0-100 + a list
of MUST-FIX issues.

Verdict thresholds:
  >= 80   SAFE-TO-USE
  60-79   USE-WITH-CAUTION
  < 60    NOT-SAFE

Input formats:
  --input runbook.md         (markdown: heuristic parser, expects
                              "## Step N:" or "### Step N:" headings)
  --input runbook.json       (JSON: explicit step list — preferred)

JSON schema:
{
  "runbook_name": "Incident Comms Cascade",
  "steps": [
    {
      "title": "Acknowledge alert in PagerDuty",
      "owner": "On-call IC (named rotation)",
      "duration_minutes": 2,
      "success_signal": "PagerDuty incident transitions to acknowledged",
      "failure_signal": "Incident remains in triggered state after 2 min",
      "rollback": "n/a (acknowledgement is non-mutating)",
      "escalation": "Engineering Manager on-call"
    }
  ]
}

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path


VAGUE_OWNER_TOKENS = {
    "the team", "team", "ops", "the ops team", "engineering",
    "support", "everyone", "whoever", "someone", "tbd", "n/a",
    "the on-call", "on call", "rotation",  # rotation alone is vague
}

# Vague success signal phrases that get flagged. Matched as whole-phrase
# substrings — must be specific enough to avoid false positives on
# legitimate observables that happen to contain a common word.
VAGUE_SUCCESS_TOKENS = [
    "service is up", "it works", "things look good", "looks fine",
    "no errors", "should work", "appears to be",
    "verify the service", "check that it works", "looks good",
]

# Phrases that count as observable.
OBSERVABLE_HINTS = [
    "http 2", "http 3", "http 4", "http 5",  # status codes
    "status code", "exit code 0", "/healthz", "/health", "200 ok",
    "log line", "metric", "dashboard shows", "alert clears",
    "incident transitions", "ticket moves to", "slack reaction",
    "email received", "record updated", "field set to",
]

DURATION_PATTERN = re.compile(
    r"\b\d+(?:\.\d+)?\s*(seconds?|secs?|minutes?|mins?|hours?|hrs?|days?)\b",
    re.IGNORECASE,
)

# Rollback acceptable phrasing: either a real rollback OR explicit
# acknowledgement that rollback is impossible plus escalation.
NO_ROLLBACK_ACCEPTABLE = [
    "cannot be rolled back",
    "cannot roll back",
    "non-mutating",
    "read-only",
    "no rollback needed",
    "irreversible — escalate",
    "irreversible - escalate",
]


@dataclass
class StepFinding:
    step_index: int
    title: str
    owner_ok: bool = False
    duration_ok: bool = False
    success_ok: bool = False
    failure_ok: bool = False
    rollback_ok: bool = False
    escalation_ok: bool = False
    issues: list = field(default_factory=list)

    @property
    def passes(self) -> int:
        return sum([
            self.owner_ok, self.duration_ok, self.success_ok,
            self.failure_ok, self.rollback_ok, self.escalation_ok,
        ])

    @property
    def traffic_light(self) -> str:
        if self.passes == 6:
            return "GREEN"
        if self.passes >= 4:
            return "AMBER"
        return "RED"


def _check_owner(owner: str) -> tuple[bool, str]:
    if not owner or not owner.strip():
        return False, "missing owner"
    norm = owner.strip().lower()
    for token in VAGUE_OWNER_TOKENS:
        # Vague if owner is ONLY that token (allow named rotations like
        # "SRE on-call (alex)" by checking for parenthetical name OR @).
        if norm == token or norm.startswith(token + " "):
            if "@" in owner or "(" in owner:
                return True, ""
            return False, (
                f"vague owner '{owner}' — name a specific human or a "
                f"specifically-named rotation (e.g., 'SRE on-call "
                f"rotation (PagerDuty: sre-primary)')"
            )
    return True, ""


def _check_duration(duration_str: str, duration_minutes) -> tuple[bool, str]:
    if duration_minutes is not None:
        try:
            val = float(duration_minutes)
            if val > 0:
                return True, ""
            return False, "duration_minutes is zero or negative"
        except (TypeError, ValueError):
            pass
    if duration_str and DURATION_PATTERN.search(duration_str):
        return True, ""
    return False, (
        "missing expected duration (need a concrete number + unit, "
        "e.g., '2 minutes', '30 seconds')"
    )


def _check_observable(signal: str, kind: str) -> tuple[bool, str]:
    if not signal or not signal.strip():
        return False, f"missing observable {kind} signal"
    norm = signal.lower()
    for vague in VAGUE_SUCCESS_TOKENS:
        if vague in norm:
            return False, (
                f"vague {kind} signal '{signal}' — need an observable "
                f"(e.g., 'HTTP 200 from /healthz', not 'service is up')"
            )
    for hint in OBSERVABLE_HINTS:
        if hint in norm:
            return True, ""
    # Heuristic: if signal contains digits, equality, code-fences, or
    # specific verbs that imply an observation, accept.
    if any(ch in signal for ch in ("=", ":", "`", "200", "404", "500")):
        return True, ""
    if re.search(r"\b(returns?|equals?|shows?|transitions?|moves?|"
                 r"closes?|emits?|logs?|created|deleted|received|"
                 r"updated|set\s+to|reaches?|reports?)\b", norm):
        return True, ""
    return False, (
        f"{kind} signal '{signal}' is not clearly observable — rewrite "
        f"as a concrete check (status code, log line, dashboard panel, "
        f"ticket state)"
    )


def _check_rollback(rollback: str) -> tuple[bool, str]:
    if not rollback or not rollback.strip():
        return False, "missing rollback path"
    norm = rollback.lower()
    for ok in NO_ROLLBACK_ACCEPTABLE:
        if ok in norm:
            return True, ""
    # If there's substantive text (> 12 chars) describing a step, accept.
    if len(rollback.strip()) >= 12:
        return True, ""
    return False, (
        f"rollback path too thin ('{rollback}') — either describe the "
        f"rollback procedure OR write 'cannot be rolled back — "
        f"escalate to <name>'"
    )


def _check_escalation(escalation: str) -> tuple[bool, str]:
    if not escalation or not escalation.strip():
        return False, "missing escalation contact"
    norm = escalation.strip().lower()
    for token in VAGUE_OWNER_TOKENS:
        if norm == token or norm.startswith(token + " "):
            if "@" not in escalation and "(" not in escalation:
                return False, (
                    f"vague escalation contact '{escalation}' — name a "
                    f"specific human, role+email, or named on-call rotation"
                )
    return True, ""


def validate_step(step: dict, idx: int) -> StepFinding:
    finding = StepFinding(
        step_index=idx,
        title=step.get("title", f"(step {idx} — no title)"),
    )

    owner_ok, owner_err = _check_owner(step.get("owner", ""))
    finding.owner_ok = owner_ok
    if not owner_ok:
        finding.issues.append(f"OWNER: {owner_err}")

    duration_ok, duration_err = _check_duration(
        step.get("duration_str", ""),
        step.get("duration_minutes"),
    )
    finding.duration_ok = duration_ok
    if not duration_ok:
        finding.issues.append(f"DURATION: {duration_err}")

    succ_ok, succ_err = _check_observable(
        step.get("success_signal", ""), "success")
    finding.success_ok = succ_ok
    if not succ_ok:
        finding.issues.append(f"SUCCESS: {succ_err}")

    fail_ok, fail_err = _check_observable(
        step.get("failure_signal", ""), "failure")
    finding.failure_ok = fail_ok
    if not fail_ok:
        finding.issues.append(f"FAILURE: {fail_err}")

    rb_ok, rb_err = _check_rollback(step.get("rollback", ""))
    finding.rollback_ok = rb_ok
    if not rb_ok:
        finding.issues.append(f"ROLLBACK: {rb_err}")

    esc_ok, esc_err = _check_escalation(step.get("escalation", ""))
    finding.escalation_ok = esc_ok
    if not esc_ok:
        finding.issues.append(f"ESCALATION: {esc_err}")

    return finding


def _parse_markdown(text: str) -> dict:
    """Heuristic parser. Expects steps as '## Step N: title' or
    '### Step N: title' followed by bullet attributes."""
    lines = text.splitlines()
    name_match = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    runbook_name = name_match.group(1).strip() if name_match else "(unnamed)"
    steps = []
    current = None
    step_re = re.compile(
        r"^#{2,3}\s+Step\s+(\d+)\s*:?\s*(.*)$", re.IGNORECASE)
    attr_re = re.compile(
        r"^\s*[-*]\s+\*?\*?(Owner|Duration|Success|Failure|"
        r"Rollback|Escalation)\*?\*?\s*:?\s*(.+)$",
        re.IGNORECASE,
    )
    for line in lines:
        m = step_re.match(line)
        if m:
            if current:
                steps.append(current)
            current = {"title": m.group(2).strip() or f"step {m.group(1)}"}
            continue
        if current:
            am = attr_re.match(line)
            if am:
                key = am.group(1).lower()
                val = am.group(2).strip()
                if key == "owner":
                    current["owner"] = val
                elif key == "duration":
                    current["duration_str"] = val
                elif key == "success":
                    current["success_signal"] = val
                elif key == "failure":
                    current["failure_signal"] = val
                elif key == "rollback":
                    current["rollback"] = val
                elif key == "escalation":
                    current["escalation"] = val
    if current:
        steps.append(current)
    return {"runbook_name": runbook_name, "steps": steps}


def _sample_runbook() -> dict:
    """Deliberately broken incident-comms runbook to demonstrate
    failure detection."""
    return {
        "runbook_name": "Incident Comms Cascade (BROKEN sample)",
        "steps": [
            {
                "title": "Acknowledge alert",
                "owner": "the team",  # vague
                "duration_str": "",   # missing
                "success_signal": "service is up",  # vague
                "failure_signal": "",  # missing
                "rollback": "",        # missing
                "escalation": "ops",   # vague
            },
            {
                "title": "Open incident channel",
                "owner": "Incident Commander on-call "
                         "(PagerDuty: ic-primary)",
                "duration_str": "2 minutes",
                "success_signal": "Slack channel #inc-<id> created and "
                                  "linked from PagerDuty incident",
                "failure_signal": "Slack returns 4xx or channel-create "
                                  "API call times out",
                "rollback": "n/a — read-only operation (channel can be "
                            "archived if created in error)",
                "escalation": "Engineering Manager on-call "
                              "(em-primary@company.com)",
            },
            {
                "title": "Notify execs via paging tree",
                "owner": "Communications Lead "
                         "(comms-lead@company.com)",
                "duration_str": "5 minutes",
                "success_signal": "Exec recipient list shows email "
                                  "received (200 OK from SES API)",
                "failure_signal": "SES API returns 5xx or recipient "
                                  "delivery status = bounced",
                "rollback": "Send retraction email to same list with "
                            "subject prefix 'RETRACTION:'",
                "escalation": "VP Communications "
                              "(vp-comms@company.com)",
            },
        ],
    }


def generate_report(runbook: dict, findings: list) -> str:
    total = len(findings)
    if total == 0:
        return "ERROR: runbook contains no steps."
    score = round(sum(f.passes for f in findings) /
                  (6 * total) * 100, 1)
    if score >= 80:
        verdict = "SAFE-TO-USE"
    elif score >= 60:
        verdict = "USE-WITH-CAUTION"
    else:
        verdict = "NOT-SAFE"

    lines = [
        f"# Runbook validation: {runbook.get('runbook_name', '(unnamed)')}",
        "",
        f"**Steps validated:** {total}",
        f"**Validity score:** {score} / 100",
        f"**Verdict:** {verdict}",
        "",
        "## Per-step traffic-light",
        "",
        "| Step | Title | Owner | Duration | Success | Failure | "
        "Rollback | Escalation | Light |",
        "|------|-------|-------|----------|---------|---------|"
        "----------|------------|-------|",
    ]
    for f in findings:
        def ck(b):
            return "OK" if b else "FAIL"
        lines.append(
            f"| {f.step_index} | {f.title[:40]} | {ck(f.owner_ok)} | "
            f"{ck(f.duration_ok)} | {ck(f.success_ok)} | "
            f"{ck(f.failure_ok)} | {ck(f.rollback_ok)} | "
            f"{ck(f.escalation_ok)} | {f.traffic_light} |"
        )

    lines.append("")
    lines.append("## MUST-FIX issues")
    lines.append("")
    any_issues = False
    for f in findings:
        if f.issues:
            any_issues = True
            lines.append(f"### Step {f.step_index}: {f.title}")
            for issue in f.issues:
                lines.append(f"- {issue}")
            lines.append("")
    if not any_issues:
        lines.append("_(none — all steps pass all six checks)_")
    return "\n".join(lines) + "\n"


def generate_json_report(runbook: dict, findings: list) -> dict:
    total = len(findings) or 1
    score = round(sum(f.passes for f in findings) / (6 * total) * 100, 1)
    verdict = ("SAFE-TO-USE" if score >= 80
               else "USE-WITH-CAUTION" if score >= 60
               else "NOT-SAFE")
    return {
        "runbook_name": runbook.get("runbook_name", "(unnamed)"),
        "step_count": len(findings),
        "validity_score": score,
        "verdict": verdict,
        "findings": [asdict(f) | {"traffic_light": f.traffic_light,
                                  "passes": f.passes} for f in findings],
    }


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Validate a runbook against six step-completeness "
                    "rules. Output traffic-light + score + MUST-FIX list."
    )
    p.add_argument("--input", "-i", type=str,
                   help="Path to runbook .md or .json file.")
    p.add_argument("--output", "-o", choices=["markdown", "json"],
                   default="markdown",
                   help="Output format (default: markdown).")
    p.add_argument("--sample", action="store_true",
                   help="Run against a deliberately-broken sample runbook.")
    args = p.parse_args(argv)

    if args.sample:
        runbook = _sample_runbook()
    elif args.input:
        path = Path(args.input)
        if not path.exists():
            print(f"ERROR: input file not found: {args.input}",
                  file=sys.stderr)
            return 2
        text = path.read_text()
        if path.suffix.lower() == ".json":
            runbook = json.loads(text)
        else:
            runbook = _parse_markdown(text)
    else:
        print("ERROR: provide --input <runbook.md|json> or --sample",
              file=sys.stderr)
        return 2

    steps = runbook.get("steps", [])
    if not steps:
        print("ERROR: runbook contains no steps "
              "(or markdown parser found none — try JSON input)",
              file=sys.stderr)
        return 1

    findings = [validate_step(s, i + 1) for i, s in enumerate(steps)]
    if args.output == "json":
        print(json.dumps(generate_json_report(runbook, findings),
                         indent=2))
    else:
        print(generate_report(runbook, findings))
    return 0


if __name__ == "__main__":
    sys.exit(main())
