#!/usr/bin/env python3
"""custom_prompt_template_generator.py — Studio output type + audience → custom prompt starter.

Stdlib-only. Generates a starter custom prompt for NotebookLM Studio outputs
based on output type + audience + length + angle. Default prompts produce
mediocre output; this generator produces a sharper starter the user can refine.

Output types: audio_overview, study_guide, briefing_doc, timeline, faq,
table_of_contents, infographic, slides, mind_map.

NO LLM CALLS. Template-based prompt construction.

Usage:
    python custom_prompt_template_generator.py --output-type audio_overview --audience executive --length 8min
    python custom_prompt_template_generator.py --output-type infographic --audience consumer --angle decision-tree
    python custom_prompt_template_generator.py --sample
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Optional


VALID_OUTPUT_TYPES = [
    "audio_overview", "study_guide", "briefing_doc", "timeline", "faq",
    "table_of_contents", "infographic", "slides", "mind_map",
]

VALID_AUDIENCES = [
    "executive", "technical_lead", "undergraduate", "graduate",
    "consumer", "internal_team", "investor", "general_public",
]

VALID_ANGLES = {
    "audio_overview": ["business_implications", "technical_mechanism", "historical_evolution", "practical_applications"],
    "infographic": ["decision_tree", "process_flow", "comparison", "storytelling"],
    "study_guide": ["definitions_first", "problem_solving", "case_study", "review_focused"],
    "briefing_doc": ["neutral_analytical", "persuasive", "cautionary"],
    "slides": ["narrative", "data_driven", "framework", "case_study"],
    "timeline": ["chronological", "reverse_chronological", "era_grouped"],
    "faq": ["onboarding", "objection_handling", "deep_dive", "troubleshooting"],
    "mind_map": ["hierarchical", "interconnected", "priority_marked"],
    "table_of_contents": ["sequential", "thematic", "audience_guided"],
}


def generate_audio_overview(audience: str, length: str, angle: str) -> str:
    audience_descriptions = {
        "executive": "non-technical executive making a budget or strategic decision",
        "technical_lead": "senior technical lead evaluating an implementation approach",
        "undergraduate": "undergraduate student new to the subject",
        "graduate": "graduate student doing literature review",
        "consumer": "interested general public, no specialized background",
        "internal_team": "internal team member needing context to do their work",
        "investor": "investor evaluating a thesis or opportunity",
        "general_public": "intelligent general public reader",
    }
    angle_focuses = {
        "business_implications": "business implications, ROI, market dynamics — NOT technical depth",
        "technical_mechanism": "how the mechanism works under the hood, with concrete technical detail",
        "historical_evolution": "how the field got to its current state — inflection points, paradigm shifts",
        "practical_applications": "how this gets used in practice, with concrete examples per major point",
    }
    aud = audience_descriptions.get(audience, audience)
    foc = angle_focuses.get(angle, angle)
    return (
        f"Two-host conversation between a researcher and an experienced practitioner. "
        f"Audience: {aud}. Length: {length}. Focus: {foc}. "
        "Include one concrete example per major point. Acknowledge counter-arguments briefly. "
        "End with one specific takeaway, not a generic summary."
    )


def generate_infographic(audience: str, length: str, angle: str) -> str:
    angle_structures = {
        "decision_tree": "Decision-tree style. Action-oriented (each panel ends with a decision/action). Branches lead to next panel.",
        "process_flow": "Linear process flow. Panels are sequential steps. Each panel: step name + one-sentence what-happens + visual cue.",
        "comparison": "Side-by-side comparison. 3-4 alternatives compared on 4-6 dimensions. Color-coded per alternative.",
        "storytelling": "Narrative arc. Panels tell a story: situation → complication → resolution → takeaway.",
    }
    structure = angle_structures.get(angle, angle_structures["decision_tree"])
    panel_count = "4-6 panels max" if length == "compact" else "6-8 panels"
    return (
        f"{structure} {panel_count}. "
        f"Audience: {audience}. Monochrome navy with one accent color (amber highlight on key info). "
        "Each panel: title (4-6 words), 1-2 sentence body, action/decision/next-step line. "
        "No filler panels. Last panel: specific call-to-action with concrete next step (URL/contact/resource)."
    )


def generate_study_guide(audience: str, length: str, angle: str) -> str:
    jargon_rule = (
        "Define every technical term. Assume zero specialized background."
        if audience in ("undergraduate", "general_public", "consumer")
        else "Assume technical fluency in the field. Brief context for novel concepts only."
        if audience in ("graduate", "technical_lead")
        else "Calibrate jargon to audience expertise."
    )
    concept_count = "4-6 core concepts" if length == "compact" else "6-10 core concepts"
    return (
        f"Audience: {audience}. {jargon_rule} "
        f"Structure: {concept_count}, each with 4 elements: "
        "(1) one-paragraph definition, "
        "(2) why this matters in practice (concrete example), "
        "(3) one worked problem or applied scenario, "
        "(4) 3 practice questions Bloom-higher-order (apply / analyze / evaluate; NO recall questions). "
        "Discussion questions tied to a specific learning outcome listed at the start of each section."
    )


def generate_slides(audience: str, length: str, angle: str) -> str:
    slide_count = "8-10 slides" if length == "compact" else "12-15 slides"
    return (
        f"{slide_count} max. Audience: {audience}. 1-2 sentences per slide body — "
        "NO bullet points in slide bodies (prose only). "
        "Per slide: include presenter notes with "
        "(a) one concrete example, "
        "(b) one likely audience objection, "
        "(c) how to address it. "
        "Title slide + content slides + closing call-to-action slide. "
        "Closing slide: specific next step (not generic 'thank you')."
    )


def generate_briefing_doc(audience: str, length: str, angle: str) -> str:
    tone_descriptions = {
        "neutral_analytical": "Neutral analytical tone. Present evidence, let it speak.",
        "persuasive": "Persuasive tone with explicit recommendation backed by evidence.",
        "cautionary": "Cautionary tone, surface risks and trade-offs prominently.",
    }
    tone = tone_descriptions.get(angle, tone_descriptions["neutral_analytical"])
    length_pages = "1 page" if length == "compact" else "2-3 pages" if length == "standard" else "5 pages"
    return (
        f"Audience: {audience}. Length: {length_pages}. {tone} "
        "Structure: "
        "(1) BLUF (bottom line up front, 2 sentences max), "
        "(2) Key findings (3-5 numbered), "
        "(3) Decisions needed from this audience (numbered, with options + recommendation), "
        "(4) Open questions (3 max), "
        "(5) Suggested next step (1 specific action)."
    )


def generate_timeline(audience: str, length: str, angle: str) -> str:
    milestone_count = "5-8 milestones" if length == "compact" else "8-12 milestones"
    direction = "Reverse-chronological (most recent first)" if angle == "reverse_chronological" else "Chronological (earliest first)"
    return (
        f"Milestone-focused (not event-dump). {milestone_count} max. "
        "Per milestone: date, milestone (one phrase), significance (one sentence — why this changed the field). "
        f"Order: {direction}. "
        "Group into 3-4 eras with era-level summary at each boundary. "
        "Exclude minor events that don't shift the trajectory."
    )


def generate_faq(audience: str, length: str, angle: str) -> str:
    question_count = "6-10 questions" if length == "compact" else "10-15 questions"
    return (
        f"Audience: {audience}. {question_count}. "
        "Each answer: 2-3 sentences max. "
        "Question phrasing: how the audience would actually ask it (not how the topic owner would write it). "
        "Group into 3 categories. "
        "Include 2-3 'difficult question' entries (objections / concerns) — handle them directly, not evasively."
    )


def generate_mind_map(audience: str, length: str, angle: str) -> str:
    return (
        f"Audience: {audience}. Central concept clearly named. "
        "3-5 primary branches (the major dimensions). Each branch: 2-4 sub-branches. "
        "Max depth: 3 levels (central → branch → sub-branch). "
        "Use noun phrases for branches (not full sentences). "
        "Mark 2-3 sub-branches as 'critical' (the highest-leverage points). "
        "Skip details that don't connect back to a critical sub-branch."
    )


def generate_table_of_contents(audience: str, length: str, angle: str) -> str:
    section_count = "6-10 sections" if length == "compact" else "10-15 sections"
    return (
        f"{section_count}. Each entry: section number + section title + 1-sentence summary of what the section covers. "
        f"Audience: {audience}. "
        "Group into 2-3 parts with part-level summary at each boundary. "
        "Mark 2-3 sections as 'start here' for newcomers."
    )


GENERATORS = {
    "audio_overview": generate_audio_overview,
    "infographic": generate_infographic,
    "study_guide": generate_study_guide,
    "slides": generate_slides,
    "briefing_doc": generate_briefing_doc,
    "timeline": generate_timeline,
    "faq": generate_faq,
    "mind_map": generate_mind_map,
    "table_of_contents": generate_table_of_contents,
}


def generate(output_type: str, audience: str, length: str, angle: Optional[str] = None) -> Dict[str, Any]:
    if output_type not in VALID_OUTPUT_TYPES:
        raise ValueError(f"Invalid output_type '{output_type}'. Pick from: {VALID_OUTPUT_TYPES}")
    if audience not in VALID_AUDIENCES:
        raise ValueError(f"Invalid audience '{audience}'. Pick from: {VALID_AUDIENCES}")

    valid_angles = VALID_ANGLES.get(output_type, [])
    if angle and angle not in valid_angles:
        raise ValueError(f"Invalid angle '{angle}' for output_type '{output_type}'. Pick from: {valid_angles}")
    if not angle and valid_angles:
        angle = valid_angles[0]  # default to first

    generator_fn = GENERATORS[output_type]
    prompt = generator_fn(audience, length, angle or "")

    return {
        "output_type": output_type,
        "audience": audience,
        "length": length,
        "angle": angle,
        "custom_prompt": prompt,
        "instructions": "Use this as STARTER text in the NotebookLM customization menu (chevron next to Studio output button, NOT main button). Refine the prompt further based on the specific notebook contents and user's intent.",
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Output type:  {result['output_type']}")
    out.append(f"Audience:     {result['audience']}")
    out.append(f"Length:       {result['length']}")
    out.append(f"Angle:        {result['angle'] or '(default)'}")
    out.append("")
    out.append("Custom prompt (paste into NotebookLM customization menu):")
    out.append("")
    out.append(result['custom_prompt'])
    out.append("")
    out.append(f"📝 {result['instructions']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--output-type", choices=VALID_OUTPUT_TYPES)
    parser.add_argument("--audience", choices=VALID_AUDIENCES)
    parser.add_argument("--length", default="standard", choices=["compact", "standard", "deep"])
    parser.add_argument("--angle")
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = generate("audio_overview", "executive", "compact", "business_implications")
    elif args.output_type and args.audience:
        try:
            result = generate(args.output_type, args.audience, args.length, args.angle)
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
