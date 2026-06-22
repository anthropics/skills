#!/usr/bin/env python3
"""Eval runner for PITH compression tests (myskills standalone)."""
import json
import re
import sys
from pathlib import Path

EVALS = Path(__file__).parent / "evals.json"

sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))
from compress import compress, DEFAULT_RATIO


def extract_ratio(prompt: str) -> float:
    m = re.search(r'ratio\s+(\d+\.\d+)', prompt)
    return float(m.group(1)) if m else DEFAULT_RATIO


def needs_json(prompt: str) -> bool:
    return "json" in prompt.lower() and "metadata" in prompt.lower()


def extract_payload(prompt: str) -> str:
    if "\n\n" in prompt:
        return prompt.split("\n\n", 1)[1].strip()
    if ": " in prompt:
        return prompt.split(": ", 1)[1].strip()
    return prompt.strip()


def check_assertion(assertion: str, output: str) -> tuple[bool, str]:
    a = assertion.strip()

    if ' AND ' in a:
        for part in a.split(' AND '):
            passed, reason = check_assertion(part.strip(), output)
            if not passed:
                return False, reason
        return True, "all AND conditions met"

    if ' OR ' in a:
        for part in a.split(' OR '):
            passed, _ = check_assertion(part.strip(), output)
            if passed:
                return True, "OR condition met"
        return False, f"none of OR conditions met: {a}"

    m = re.match(r"output does NOT contain '(.+)'", a)
    if m:
        needle = m.group(1)
        return (needle not in output, f"found forbidden: '{needle}'") if needle in output else (True, "")

    m = re.match(r"output does NOT contain (.+)", a)
    if m:
        needle = m.group(1).strip().strip("'\"")
        return (False, f"found forbidden: '{needle}'") if needle in output else (True, "")

    m = re.match(r"output contains '(.+)'", a)
    if m:
        needle = m.group(1)
        return (True, "") if needle in output else (False, f"missing: '{needle}'")

    m = re.match(r"output contains (.+)", a)
    if m:
        needle = m.group(1).strip()
        if (needle.startswith("'") and needle.endswith("'")) or \
           (needle.startswith('"') and needle.endswith('"')):
            needle = needle[1:-1]
        return (True, "") if needle in output else (False, f"missing: '{needle}'")

    m = re.match(r"output mentions (.+)", a)
    if m:
        needle = m.group(1).strip().strip("'\"").lower()
        return (True, "") if needle in output.lower() else (False, f"missing mention: '{needle}'")

    return False, f"unknown assertion format: '{a}'"


def run_tc(tc: dict) -> dict:
    tid = tc["id"]
    category = tc["category"]
    prompt = tc["prompt"]

    payload = extract_payload(prompt)
    ratio = extract_ratio(prompt)
    json_mode = needs_json(prompt)

    try:
        compressed_text, meta = compress(payload, target_ratio=ratio)
    except Exception as e:
        return {"id": tid, "status": "ERROR", "reason": str(e)}

    if json_mode:
        import json as _json
        output = _json.dumps({"compressed": compressed_text, "meta": meta}, indent=2)
    else:
        benford_icon = "✓" if meta.get("benford_ok", True) else "⚠"
        action = meta.get("action", "compressed")
        saved = meta.get("saved_pct", 0)
        b_mad = meta.get("compressed_benford_mad", meta.get("benford_mad", 0))
        header = f"[PITH | {benford_icon} | -{saved:.0f}% tokens | benford:{b_mad:.1f}% | {action}]"
        output = f"{header}\n{compressed_text}"

    failures = []
    for assertion in tc["assertions"]:
        passed, reason = check_assertion(assertion, output)
        if not passed:
            failures.append(f"  FAIL [{assertion}] >> {reason}")

    return {
        "id": tid,
        "category": category,
        "status": "PASS" if not failures else "FAIL",
        "failures": failures,
        "output_snippet": output[:300].replace("\n", " ") if output else "",
    }


def main():
    tests = json.loads(EVALS.read_text(encoding="utf-8"))
    results = [run_tc(tc) for tc in tests]

    passed = sum(1 for r in results if r["status"] == "PASS")
    failed = sum(1 for r in results if r["status"] in ("FAIL", "ERROR"))
    total = len(results)

    print(f"\n{'='*60}")
    print(f"PITH EVAL RESULTS: {passed}/{total} passed, {failed} failed")
    print(f"{'='*60}")

    for r in results:
        icon = {"PASS": "OK", "FAIL": "XX", "ERROR": "!!"}.get(r["status"], "??")
        print(f"\n[{icon}] {r['id']} ({r.get('category', '')}) - {r['status']}")
        for f in r.get("failures", []):
            print(f)
        if r["status"] in ("FAIL", "ERROR") and r.get("output_snippet"):
            print(f"  Output: {r['output_snippet']}")

    print(f"\n{'='*60}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
