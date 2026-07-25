#!/usr/bin/env python3
"""async_action_classifier.py — Classify NotebookLM action as wait-or-notify.

Stdlib-only. Given an action name, returns whether the skill should wait
synchronously OR fire-and-notify the user. The 2-minute dividing line:

  - Under 2 minutes  → WAIT (with appropriate timeout)
  - Over 2 minutes   → FIRE_AND_NOTIFY (browser session would time out)

Returns: action timing classification + estimated duration + recommended
timeout + fire-and-notify message template (if applicable).

NO LLM CALLS. Pure lookup table.

Usage:
    python async_action_classifier.py --action audio_overview
    python async_action_classifier.py --action add_source_url
    python async_action_classifier.py --output json
    python async_action_classifier.py --sample
"""

import argparse
import json
import sys
from typing import Any, Dict, List


ACTION_TIMING = {
    # Read/Extract
    "chat_send": {
        "category": "read_extract",
        "verdict": "WAIT",
        "estimated_duration_seconds": (3, 10),
        "timeout_seconds": 30,
        "polling_interval_seconds": 3,
    },
    # Add Source sub-types
    "add_source_url": {
        "category": "add_source",
        "verdict": "WAIT",
        "estimated_duration_seconds": (5, 15),
        "timeout_seconds": 60,
        "polling_interval_seconds": 5,
    },
    "add_source_text": {
        "category": "add_source",
        "verdict": "WAIT",
        "estimated_duration_seconds": (5, 15),
        "timeout_seconds": 60,
        "polling_interval_seconds": 5,
    },
    "add_source_file": {
        "category": "add_source",
        "verdict": "WAIT",
        "estimated_duration_seconds": (10, 30),
        "timeout_seconds": 90,
        "polling_interval_seconds": 5,
    },
    "add_source_google_doc": {
        "category": "add_source",
        "verdict": "WAIT",
        "estimated_duration_seconds": (10, 30),
        "timeout_seconds": 90,
        "polling_interval_seconds": 5,
    },
    "add_source_synthesized": {
        "category": "add_source",
        "verdict": "WAIT",
        "estimated_duration_seconds": (5, 15),
        "timeout_seconds": 60,
        "polling_interval_seconds": 5,
    },
    # Create New
    "create_new_notebook": {
        "category": "create_new",
        "verdict": "WAIT",
        "estimated_duration_seconds": (15, 30),
        "timeout_seconds": 60,
        "polling_interval_seconds": 5,
    },
    # Studio outputs — fast
    "study_guide": {
        "category": "studio",
        "verdict": "WAIT",
        "estimated_duration_seconds": (30, 60),
        "timeout_seconds": 120,
        "polling_interval_seconds": 10,
    },
    "briefing_doc": {
        "category": "studio",
        "verdict": "WAIT",
        "estimated_duration_seconds": (30, 60),
        "timeout_seconds": 120,
        "polling_interval_seconds": 10,
    },
    "timeline": {
        "category": "studio",
        "verdict": "WAIT",
        "estimated_duration_seconds": (30, 60),
        "timeout_seconds": 120,
        "polling_interval_seconds": 10,
    },
    "faq": {
        "category": "studio",
        "verdict": "WAIT",
        "estimated_duration_seconds": (30, 60),
        "timeout_seconds": 120,
        "polling_interval_seconds": 10,
    },
    "table_of_contents": {
        "category": "studio",
        "verdict": "WAIT",
        "estimated_duration_seconds": (20, 40),
        "timeout_seconds": 90,
        "polling_interval_seconds": 5,
    },
    "flashcards": {
        "category": "studio",
        "verdict": "WAIT",
        "estimated_duration_seconds": (30, 60),
        "timeout_seconds": 120,
        "polling_interval_seconds": 10,
    },
    "quiz": {
        "category": "studio",
        "verdict": "WAIT",
        "estimated_duration_seconds": (30, 60),
        "timeout_seconds": 120,
        "polling_interval_seconds": 10,
    },
    # Studio outputs — slow (fire-and-notify)
    "video_overview": {
        "category": "studio",
        "verdict": "FIRE_AND_NOTIFY",
        "estimated_duration_seconds": (300, 900),
        "estimated_duration_human": "5-15 minutes",
        "notify_message": (
            "Video Overview generation triggered. Estimated 5-15 minutes. "
            "NotebookLM will notify you in-app and via email when ready. "
            "NOT waiting in this session — returning control to you now."
        ),
    },
    "audio_overview": {
        "category": "studio",
        "verdict": "FIRE_AND_NOTIFY",
        "estimated_duration_seconds": (300, 600),
        "estimated_duration_human": "5-10 minutes",
        "notify_message": (
            "Audio Overview generation triggered. Estimated 5-10 minutes. "
            "NotebookLM will notify you in-app and via email when ready. "
            "NOT waiting in this session — returning control to you now."
        ),
    },
    "infographic": {
        "category": "studio",
        "verdict": "FIRE_AND_NOTIFY",
        "estimated_duration_seconds": (120, 300),
        "estimated_duration_human": "2-5 minutes",
        "notify_message": (
            "Infographic generation triggered. Estimated 2-5 minutes. "
            "NotebookLM will notify you when ready. "
            "NOT waiting in this session — returning control."
        ),
    },
    "slides": {
        "category": "studio",
        "verdict": "FIRE_AND_NOTIFY",
        "estimated_duration_seconds": (120, 300),
        "estimated_duration_human": "2-5 minutes",
        "notify_message": (
            "Slides generation triggered. Estimated 2-5 minutes. "
            "NotebookLM will notify you when ready. "
            "NOT waiting in this session — returning control."
        ),
    },
    "mind_map": {
        "category": "studio",
        "verdict": "FIRE_AND_NOTIFY",
        "estimated_duration_seconds": (120, 300),
        "estimated_duration_human": "2-5 minutes",
        "notify_message": (
            "Mind Map generation triggered. Estimated 2-5 minutes. "
            "NotebookLM will notify you when ready. "
            "NOT waiting in this session — returning control."
        ),
    },
}


def classify(action: str) -> Dict[str, Any]:
    if action not in ACTION_TIMING:
        # Try fuzzy match for synonyms
        action_lower = action.lower().replace(" ", "_").replace("-", "_")
        for known_action in ACTION_TIMING:
            if action_lower in known_action or known_action in action_lower:
                return {"action": known_action, "matched_from": action, **ACTION_TIMING[known_action]}
        raise ValueError(f"Unknown action '{action}'. Known: {sorted(ACTION_TIMING.keys())}")
    return {"action": action, **ACTION_TIMING[action]}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Action:    {result['action']}")
    if result.get('matched_from'):
        out.append(f"  (matched from: {result['matched_from']})")
    out.append(f"Category:  {result['category']}")
    out.append(f"Verdict:   {result['verdict']}")
    out.append("")
    dur = result['estimated_duration_seconds']
    if isinstance(dur, (list, tuple)) and len(dur) == 2:
        out.append(f"Estimated duration: {dur[0]}-{dur[1]} seconds")
    out.append(f"Human duration:     {result.get('estimated_duration_human', f'{dur}s')}")
    out.append("")
    if result['verdict'] == "WAIT":
        out.append(f"Timeout:           {result['timeout_seconds']}s")
        out.append(f"Polling interval:  {result['polling_interval_seconds']}s")
        out.append("")
        out.append("Wait discipline:")
        out.append("  1. Click trigger (after screenshot)")
        out.append("  2. Start wait loop with timeout")
        out.append(f"  3. Poll every {result['polling_interval_seconds']}s for completion signal")
        out.append("  4. Screenshot at each poll for audit")
        out.append("  5. On timeout: screenshot, note delay, ask user")
    else:  # FIRE_AND_NOTIFY
        out.append("Fire-and-notify message (paste into skill output):")
        out.append("")
        out.append(f"  {result['notify_message']}")
        out.append("")
        out.append("Discipline:")
        out.append("  1. Click trigger (in customization menu, not main button)")
        out.append("  2. Verify generation started via screenshot WITHIN 5 seconds")
        out.append("  3. Tell user the notify message above")
        out.append("  4. END TASK — do not loop waiting for completion")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--action", help="Action name (e.g., audio_overview, chat_send, add_source_url)")
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = classify("audio_overview")
    elif args.action:
        try:
            result = classify(args.action)
        except ValueError as e:
            print(f"error: {e}", file=sys.stderr); return 2
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
