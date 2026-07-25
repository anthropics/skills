#!/usr/bin/env python3
"""A/B test prompts against structured test cases.

Supports:
- --input JSON payload or stdin JSON payload
- --prompt-a/--prompt-b or file variants
- --cases-file for test suite JSON
- optional --runner-cmd with {prompt} and {input} placeholders

If runner command is omitted, script performs static prompt quality scoring only.
"""

import argparse
import json
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from statistics import mean
from typing import Any, Dict, List, Optional


class CLIError(Exception):
    """Raised for expected CLI errors."""


@dataclass
class CaseScore:
    case_id: str
    prompt_variant: str
    score: float
    matched_expected: int
    missed_expected: int
    forbidden_hits: int
    regex_matches: int
    output_length: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="A/B test prompts against test cases.")
    parser.add_argument("--input", help="JSON input file for full payload.")
    parser.add_argument("--prompt-a", help="Prompt A text.")
    parser.add_argument("--prompt-b", help="Prompt B text.")
    parser.add_argument("--prompt-a-file", help="Path to prompt A file.")
    parser.add_argument("--prompt-b-file", help="Path to prompt B file.")
    parser.add_argument("--cases-file", help="Path to JSON test cases array.")
    parser.add_argument(
        "--runner-cmd",
        help="External command template, e.g. 'llm --prompt {prompt} --input {input}'.",
    )
    parser.add_argument("--format", choices=["text", "json"], default="text", help="Output format.")
    return parser.parse_args()


def read_text_file(path: Optional[str]) -> Optional[str]:
    if not path:
        return None
    try:
        return Path(path).read_text(encoding="utf-8")
    except Exception as exc:
        raise CLIError(f"Failed reading file {path}: {exc}") from exc


def load_payload(args: argparse.Namespace) -> Dict[str, Any]:
    if args.input:
        try:
            return json.loads(Path(args.input).read_text(encoding="utf-8"))
        except Exception as exc:
            raise CLIError(f"Failed reading --input payload: {exc}") from exc

    if not sys.stdin.isatty():
        raw = sys.stdin.read().strip()
        if raw:
            try:
                return json.loads(raw)
            except json.JSONDecodeError as exc:
                raise CLIError(f"Invalid JSON from stdin: {exc}") from exc

    payload: Dict[str, Any] = {}

    prompt_a = args.prompt_a or read_text_file(args.prompt_a_file)
    prompt_b = args.prompt_b or read_text_file(args.prompt_b_file)
    if prompt_a:
        payload["prompt_a"] = prompt_a
    if prompt_b:
        payload["prompt_b"] = prompt_b

    if args.cases_file:
        try:
            payload["cases"] = json.loads(Path(args.cases_file).read_text(encoding="utf-8"))
        except Exception as exc:
            raise CLIError(f"Failed reading --cases-file: {exc}") from exc

    if args.runner_cmd:
        payload["runner_cmd"] = args.runner_cmd

    return payload


def run_runner(runner_cmd: str, prompt: str, case_input: str) -> str:
    cmd = runner_cmd.format(prompt=prompt, input=case_input)
    parts = shlex.split(cmd)
    try:
        proc = subprocess.run(parts, text=True, capture_output=True, check=True)
    except subprocess.CalledProcessError as exc:
        raise CLIError(f"Runner command failed: {exc.stderr.strip()}") from exc
    return proc.stdout.strip()


def static_output(prompt: str, case_input: str) -> str:
    rendered = prompt.replace("{{input}}", case_input)
    return rendered


def score_output(case: Dict[str, Any], output: str, prompt_variant: str) -> CaseScore:
    case_id = str(case.get("id", "case"))
    expected = [str(x) for x in case.get("expected_contains", []) if str(x)]
    forbidden = [str(x) for x in case.get("forbidden_contains", []) if str(x)]
    regexes = [str(x) for x in case.get("expected_regex", []) if str(x)]

    matched_expected = sum(1 for item in expected if item.lower() in output.lower())
    missed_expected = len(expected) - matched_expected
    forbidden_hits = sum(1 for item in forbidden if item.lower() in output.lower())
    regex_matches = 0
    for pattern in regexes:
        try:
            if re.search(pattern, output, flags=re.MULTILINE):
                regex_matches += 1
        except re.error:
            pass

    score = 100.0
    score -= missed_expected * 15
    score -= forbidden_hits * 25
    score += regex_matches * 8

    # Heuristic penalty for unbounded verbosity
    if len(output) > 4000:
        score -= 10
    if len(output.strip()) < 10:
        score -= 10

    score = max(0.0, min(100.0, score))

    return CaseScore(
        case_id=case_id,
        prompt_variant=prompt_variant,
        score=score,
        matched_expected=matched_expected,
        missed_expected=missed_expected,
        forbidden_hits=forbidden_hits,
        regex_matches=regex_matches,
        output_length=len(output),
    )


def aggregate(scores: List[CaseScore]) -> Dict[str, Any]:
    if not scores:
        return {"average": 0.0, "min": 0.0, "max": 0.0, "cases": 0}
    vals = [s.score for s in scores]
    return {
        "average": round(mean(vals), 2),
        "min": round(min(vals), 2),
        "max": round(max(vals), 2),
        "cases": len(vals),
    }


def main() -> int:
    args = parse_args()
    payload = load_payload(args)

    prompt_a = str(payload.get("prompt_a", "")).strip()
    prompt_b = str(payload.get("prompt_b", "")).strip()
    cases = payload.get("cases", [])
    runner_cmd = payload.get("runner_cmd")

    if not prompt_a or not prompt_b:
        raise CLIError("Both prompt_a and prompt_b are required (flags or JSON payload).")
    if not isinstance(cases, list) or not cases:
        raise CLIError("cases must be a non-empty array.")

    scores_a: List[CaseScore] = []
    scores_b: List[CaseScore] = []

    for case in cases:
        if not isinstance(case, dict):
            continue
        case_input = str(case.get("input", "")).strip()

        output_a = run_runner(runner_cmd, prompt_a, case_input) if runner_cmd else static_output(prompt_a, case_input)
        output_b = run_runner(runner_cmd, prompt_b, case_input) if runner_cmd else static_output(prompt_b, case_input)

        scores_a.append(score_output(case, output_a, "A"))
        scores_b.append(score_output(case, output_b, "B"))

    agg_a = aggregate(scores_a)
    agg_b = aggregate(scores_b)
    winner = "A" if agg_a["average"] >= agg_b["average"] else "B"

    result = {
        "summary": {
            "winner": winner,
            "prompt_a": agg_a,
            "prompt_b": agg_b,
            "mode": "runner" if runner_cmd else "static",
        },
        "case_scores": {
            "prompt_a": [asdict(item) for item in scores_a],
            "prompt_b": [asdict(item) for item in scores_b],
        },
    }

    if args.format == "json":
        print(json.dumps(result, indent=2))
    else:
        print("Prompt A/B test result")
        print(f"- mode: {result['summary']['mode']}")
        print(f"- winner: {winner}")
        print(f"- prompt A avg: {agg_a['average']}")
        print(f"- prompt B avg: {agg_b['average']}")
        print("Case details:")
        for item in scores_a + scores_b:
            print(
                f"- case={item.case_id} variant={item.prompt_variant} score={item.score} "
                f"expected+={item.matched_expected} forbidden={item.forbidden_hits} regex={item.regex_matches}"
            )

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CLIError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
