#!/usr/bin/env python3
"""action_router.py — Q1-Q4 answers → action plan + UI flow + required parameters.

Stdlib-only. Routes notebooklm intake answers to one of 4 action flows:

  1. read_extract — chat-based extraction
  2. add_source   — push content via Add Source dialog (5 sub-types)
  3. studio       — generate Studio output (9 types) with mandatory custom prompt
  4. create_new   — new notebook with title + initial sources

Returns the action plan: required parameters, UI flow steps, mandatory checks.

NO LLM CALLS. Pure rule-based routing.

Usage:
    python action_router.py --action read_extract --notebook "Q3 prep" --question "what are recent trends?"
    python action_router.py --action add_source --notebook "Q3 prep" --source-type url --source-value "https://..."
    python action_router.py --action studio --notebook "Q3 prep" --studio-type audio_overview --custom-prompt "..."
    python action_router.py --action create_new --title "New project" --initial-sources "url1,url2"
    python action_router.py --sample
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional


VALID_ACTIONS = ["read_extract", "add_source", "studio", "create_new"]
VALID_SOURCE_TYPES = ["url", "text", "file", "google_doc", "synthesized"]
VALID_STUDIO_TYPES = [
    "audio_overview", "study_guide", "briefing_doc", "timeline", "faq",
    "table_of_contents", "infographic", "slides", "mind_map",
]


ACTION_FLOWS = {
    "read_extract": {
        "required_params": ["notebook", "question"],
        "ui_flow": [
            "Step 0: Browser environment check",
            "Navigate to homepage → screenshot",
            "Login wall check (halt if detected)",
            "Notebook discovery (find by name or navigate URL)",
            "Open notebook → screenshot",
            "Locate chat input via find()",
            "Type question (user's natural phrasing)",
            "Submit (Enter or send button)",
            "Wait 3-5s (synchronous; chat is fast)",
            "Screenshot response area",
            "Extract response in clean format (not raw chat dump)",
            "Report to user",
        ],
        "timing": "WAIT (3-10s)",
        "screenshots_required": 4,
    },
    "add_source": {
        "required_params": ["notebook", "source_type", "source_value"],
        "ui_flow_by_source_type": {
            "url": [
                "Open notebook → screenshot",
                "Click 'Add Source' → screenshot",
                "Click 'Link' option",
                "Paste URL",
                "Submit → wait for ingestion spinner",
                "Screenshot to confirm success",
            ],
            "text": [
                "Open notebook → screenshot",
                "Click 'Add Source' → screenshot",
                "Click 'Copied text' option",
                "Paste content",
                "Submit → wait for ingestion spinner",
                "Screenshot to confirm success",
            ],
            "file": [
                "Open notebook → screenshot",
                "Click 'Add Source' → screenshot",
                "Click 'Upload file' option",
                "Use file-upload tool with absolute path (NOT native file picker)",
                "Wait for upload + ingestion",
                "Screenshot to confirm success",
            ],
            "google_doc": [
                "Open notebook → screenshot",
                "Click 'Add Source' → screenshot",
                "Click 'Google Docs' option",
                "Use Drive picker",
                "Confirm doc selection",
                "Wait for ingestion",
                "Screenshot to confirm success",
            ],
            "synthesized": [
                "Pre-process content externally (extract main content, strip nav/ads)",
                "Open notebook → screenshot",
                "Click 'Add Source' → screenshot",
                "Click 'Copied text' option",
                "Paste synthesized content",
                "Submit → wait for ingestion",
                "Screenshot to confirm success",
            ],
        },
        "timing": "WAIT (5-30s with 60s timeout)",
        "screenshots_required": 3,
    },
    "studio": {
        "required_params": ["notebook", "studio_type", "custom_prompt"],
        "ui_flow": [
            "Step 0: Browser environment check",
            "Navigate to notebook → screenshot",
            "Locate Studio panel (right side; may need toggle) → screenshot",
            "Find specific output button via find(text=studio_type)",
            "**Open customization menu** (chevron NEXT to button; NOT main button)",
            "**Write detailed custom prompt** in customization field",
            "Submit Generate",
            "**Verify generation started** via screenshot within 5s",
            "**Fire-and-notify if slow** (Audio Overview, Infographic, Slides, Mind Map = 2-10 min)",
            "Tell user: 'Generation in progress — NotebookLM will notify you when ready'",
            "End task (don't wait for completion on slow ops)",
        ],
        "timing_by_studio_type": {
            "audio_overview": "FIRE_AND_NOTIFY (5-10 min)",
            "study_guide": "WAIT (30-60s, timeout 90s)",
            "briefing_doc": "WAIT (30-60s, timeout 90s)",
            "timeline": "WAIT (30-60s, timeout 90s)",
            "faq": "WAIT (30-60s, timeout 90s)",
            "table_of_contents": "WAIT (20-40s, timeout 60s)",
            "infographic": "FIRE_AND_NOTIFY (2-5 min)",
            "slides": "FIRE_AND_NOTIFY (2-5 min)",
            "mind_map": "FIRE_AND_NOTIFY (2-5 min)",
        },
        "screenshots_required": 5,
        "critical_rule": "ALWAYS open customization menu (chevron) — NEVER click main Studio button (uses default mediocre prompt)",
    },
    "create_new": {
        "required_params": ["title"],
        "optional_params": ["initial_sources"],
        "ui_flow": [
            "Step 0: Browser environment check",
            "Navigate to homepage → screenshot",
            "Click 'New notebook' button (find via text)",
            "Set title from --title argument",
            "If initial_sources provided: add each via Action 2 sub-flow (per source type)",
            "Wait for auto-summary generation (typically <30s)",
            "Screenshot final state",
            "Report new notebook URL to user",
        ],
        "timing": "WAIT (15-30s for init + auto-summary)",
        "screenshots_required": 3,
    },
}


def route(action: str, **params) -> Dict[str, Any]:
    if action not in VALID_ACTIONS:
        raise ValueError(f"Invalid action '{action}'. Pick from: {VALID_ACTIONS}")

    flow_template = ACTION_FLOWS[action].copy()
    flow_template["action"] = action
    flow_template["parameters"] = params

    # Validate required params
    required = flow_template.get("required_params", [])
    missing = [p for p in required if not params.get(p)]
    if missing:
        flow_template["validation_errors"] = [f"Missing required parameter: {p}" for p in missing]

    # Per-action customization
    if action == "add_source":
        source_type = params.get("source_type")
        if source_type and source_type not in VALID_SOURCE_TYPES:
            flow_template["validation_errors"] = flow_template.get("validation_errors", []) + [
                f"Invalid source_type '{source_type}'. Pick from: {VALID_SOURCE_TYPES}"
            ]
        elif source_type:
            flow_template["ui_flow"] = flow_template["ui_flow_by_source_type"][source_type]
            del flow_template["ui_flow_by_source_type"]

    if action == "studio":
        studio_type = params.get("studio_type")
        if studio_type and studio_type not in VALID_STUDIO_TYPES:
            flow_template["validation_errors"] = flow_template.get("validation_errors", []) + [
                f"Invalid studio_type '{studio_type}'. Pick from: {VALID_STUDIO_TYPES}"
            ]
        elif studio_type:
            flow_template["timing"] = flow_template["timing_by_studio_type"][studio_type]
        # Custom prompt is mandatory for studio
        if not params.get("custom_prompt") or len(params.get("custom_prompt", "")) < 30:
            flow_template["validation_errors"] = flow_template.get("validation_errors", []) + [
                "Studio output requires DETAILED custom_prompt (min 30 chars). Default prompts produce mediocre output."
            ]

    return flow_template


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Action: {result['action']}")
    out.append("")
    out.append("Parameters:")
    for k, v in result.get("parameters", {}).items():
        if v:
            display = v if len(str(v)) < 80 else str(v)[:77] + "..."
            out.append(f"  {k}: {display}")
    out.append("")

    if result.get("validation_errors"):
        out.append("⚠️  Validation errors:")
        for err in result["validation_errors"]:
            out.append(f"  - {err}")
        out.append("")

    out.append(f"Timing: {result.get('timing', 'N/A')}")
    out.append(f"Screenshots required: {result.get('screenshots_required', 'N/A')}")
    if result.get("critical_rule"):
        out.append(f"⚠️  Critical rule: {result['critical_rule']}")
    out.append("")
    out.append("UI flow:")
    flow = result.get("ui_flow", [])
    for i, step in enumerate(flow, 1):
        out.append(f"  {i}. {step}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--action", choices=VALID_ACTIONS)
    parser.add_argument("--notebook")
    parser.add_argument("--question")
    parser.add_argument("--source-type", choices=VALID_SOURCE_TYPES)
    parser.add_argument("--source-value")
    parser.add_argument("--studio-type", choices=VALID_STUDIO_TYPES)
    parser.add_argument("--custom-prompt")
    parser.add_argument("--title")
    parser.add_argument("--initial-sources")
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = route(
            "studio",
            notebook="Q3 launch prep",
            studio_type="audio_overview",
            custom_prompt="Two-host conversation for non-technical executive, 8-10 min, focus on business implications not technical depth",
        )
    elif args.action:
        params: Dict[str, Any] = {}
        if args.notebook: params["notebook"] = args.notebook
        if args.question: params["question"] = args.question
        if args.source_type: params["source_type"] = args.source_type
        if args.source_value: params["source_value"] = args.source_value
        if args.studio_type: params["studio_type"] = args.studio_type
        if args.custom_prompt: params["custom_prompt"] = args.custom_prompt
        if args.title: params["title"] = args.title
        if args.initial_sources: params["initial_sources"] = args.initial_sources
        try:
            result = route(args.action, **params)
        except ValueError as e:
            print(f"error: {e}", file=sys.stderr); return 2
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if not result.get("validation_errors") else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
