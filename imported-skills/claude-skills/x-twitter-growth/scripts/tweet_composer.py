#!/usr/bin/env python3
"""
Tweet Composer — Generate structured tweets and threads with proven hook patterns.

Provides templates, character counting, thread formatting, and hook generation
for different content types. No API required — pure content scaffolding.

Usage:
    python3 tweet_composer.py --type tweet --topic "AI in healthcare"
    python3 tweet_composer.py --type thread --topic "lessons from scaling" --tweets 8
    python3 tweet_composer.py --type hooks --topic "startup mistakes" --count 10
    python3 tweet_composer.py --validate "your tweet text here"
"""

import argparse
import json
import sys
import textwrap
from dataclasses import dataclass, field, asdict
from typing import Optional

MAX_TWEET_CHARS = 280

HOOK_PATTERNS = {
    "listicle": [
        "{n} {topic} that changed how I {verb}:",
        "The {n} biggest mistakes in {topic}:",
        "{n} {topic} most people don't know about:",
        "I spent {time} studying {topic}. Here are {n} lessons:",
        "{n} signs your {topic} needs work:",
    ],
    "contrarian": [
        "Unpopular opinion: {claim}",
        "Hot take: {claim}",
        "Everyone says {common_belief}. They're wrong.",
        "Stop {common_action}. Here's what to do instead:",
        "The {topic} advice you keep hearing is backwards.",
    ],
    "story": [
        "I {did_thing} and it completely changed my {outcome}.",
        "Last {timeframe}, I made a mistake with {topic}. Here's what happened:",
        "3 years ago I was {before_state}. Now I'm {after_state}. Here's the playbook:",
        "I almost {near_miss}. Then I discovered {topic}.",
        "The best {topic} advice I ever got came from {unexpected_source}.",
    ],
    "observation": [
        "{topic} is underrated. Here's why:",
        "Nobody talks about this part of {topic}:",
        "The gap between {thing_a} and {thing_b} is where the money is.",
        "If you're struggling with {topic}, you're probably {mistake}.",
        "The secret to {topic} isn't what you think.",
    ],
    "framework": [
        "The {name} framework for {topic} (save this):",
        "How to {outcome} in {timeframe} (step by step):",
        "{topic} explained in 60 seconds:",
        "The only {n} things that matter for {topic}:",
        "A simple system for {topic} that actually works:",
    ],
    "question": [
        "What's the most underrated {topic}?",
        "If you could only {do_one_thing} for {topic}, what would it be?",
        "What {topic} advice would you give your younger self?",
        "Real question: why do most people {common_mistake}?",
        "What's one {topic} that completely changed your perspective?",
    ],
}

THREAD_STRUCTURE = """
Thread Outline: {topic}
{'='*50}

Tweet 1 (HOOK — most important):
  Pattern: {hook_pattern}
  Draft: {hook_draft}
  Chars: {hook_chars}/280

Tweet 2 (CONTEXT):
  Purpose: Set up why this matters
  Suggestion: "Here's what most people get wrong about {topic}:"
  OR: "I spent [time] learning this. Here's the breakdown:"

Tweets 3-{n} (BODY — one idea per tweet):
{body_suggestions}

Tweet {n_plus_1} (CLOSE):
  Purpose: Summarize + CTA
  Suggestion: "TL;DR:\\n\\n[3 bullet summary]\\n\\nFollow @handle for more on {topic}"

Reply to Tweet 1 (ENGAGEMENT BAIT):
  Purpose: Resurface the thread
  Suggestion: "What's your experience with {topic}? Drop it below 👇"
"""


@dataclass
class TweetDraft:
    text: str
    char_count: int
    over_limit: bool
    warnings: list = field(default_factory=list)


def validate_tweet(text: str) -> TweetDraft:
    """Validate a tweet and return analysis."""
    char_count = len(text)
    over_limit = char_count > MAX_TWEET_CHARS
    warnings = []

    if over_limit:
        warnings.append(f"Over limit by {char_count - MAX_TWEET_CHARS} characters")

    # Check for links in body
    import re
    if re.search(r'https?://\S+', text):
        warnings.append("Contains URL — consider moving link to reply (hurts reach)")

    # Check for hashtags
    hashtags = re.findall(r'#\w+', text)
    if len(hashtags) > 2:
        warnings.append(f"Too many hashtags ({len(hashtags)}) — max 1-2, ideally 0")
    elif len(hashtags) > 0:
        warnings.append(f"Has {len(hashtags)} hashtag(s) — consider removing for cleaner look")

    # Check for @mentions at start
    if text.startswith('@'):
        warnings.append("Starts with @ — will be treated as reply, not shown in timeline")

    # Readability
    lines = text.strip().split('\n')
    long_lines = [l for l in lines if len(l) > 70]
    if long_lines:
        warnings.append("Long unbroken lines — add line breaks for mobile readability")

    return TweetDraft(text=text, char_count=char_count, over_limit=over_limit, warnings=warnings)


def generate_hooks(topic: str, count: int = 10) -> list:
    """Generate hook variations for a topic."""
    hooks = []
    for pattern_type, patterns in HOOK_PATTERNS.items():
        for p in patterns:
            hook = p.replace("{topic}", topic).replace("{n}", "7").replace(
                "{time}", "6 months").replace("{timeframe}", "month").replace(
                "{claim}", f"{topic} is overrated").replace(
                "{common_belief}", f"{topic} is simple").replace(
                "{common_action}", f"overthinking {topic}").replace(
                "{outcome}", "approach").replace("{verb}", "think").replace(
                "{name}", "3-Step").replace("{did_thing}", f"changed my {topic} strategy").replace(
                "{before_state}", "stuck").replace("{after_state}", "thriving").replace(
                "{near_miss}", f"gave up on {topic}").replace(
                "{unexpected_source}", "a complete beginner").replace(
                "{thing_a}", "theory").replace("{thing_b}", "execution").replace(
                "{mistake}", "overcomplicating it").replace(
                "{common_mistake}", f"ignore {topic}").replace(
                "{do_one_thing}", "change one thing").replace(
                "{common_action}", f"overthinking {topic}")
            hooks.append({"type": pattern_type, "hook": hook, "chars": len(hook)})
            if len(hooks) >= count:
                return hooks
    return hooks[:count]


def generate_thread_outline(topic: str, num_tweets: int = 8) -> str:
    """Generate a thread structure outline."""
    hooks = generate_hooks(topic, 3)
    best_hook = hooks[0]["hook"] if hooks else f"Everything I know about {topic}:"

    body = []
    suggestions = [
        "Key insight or surprising fact",
        "Common mistake people make",
        "The counterintuitive truth",
        "A practical example or case study",
        "The framework or system",
        "Implementation steps",
        "Results or evidence",
        "The nuance most people miss",
    ]

    for i, s in enumerate(suggestions[:num_tweets - 3], 3):
        body.append(f"  Tweet {i}: [{s}]")

    body_text = "\n".join(body)

    return f"""
{'='*60}
  THREAD OUTLINE: {topic}
{'='*60}

  Tweet 1 (HOOK):
    "{best_hook}"
    Chars: {len(best_hook)}/280

  Tweet 2 (CONTEXT):
    "Here's what most people get wrong about {topic}:"

{body_text}

  Tweet {num_tweets - 1} (CLOSE):
    "TL;DR:

    • [Key takeaway 1]
    • [Key takeaway 2]
    • [Key takeaway 3]

    Follow for more on {topic}"

  Reply to Tweet 1 (BOOST):
    "What's your biggest challenge with {topic}? 👇"

{'='*60}
  RULES:
  - Each tweet must stand alone (people read out of order)
  - Max 3-4 lines per tweet (mobile readability)
  - No filler tweets — cut anything that doesn't add value
  - Hook tweet determines 90%% of thread performance
{'='*60}
"""


def main():
    parser = argparse.ArgumentParser(
        description="Generate tweets, threads, and hooks with proven patterns",
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("--type", choices=["tweet", "thread", "hooks", "validate"],
                        default="hooks", help="Content type to generate")
    parser.add_argument("--topic", default="", help="Topic for content generation")
    parser.add_argument("--tweets", type=int, default=8, help="Number of tweets in thread")
    parser.add_argument("--count", type=int, default=10, help="Number of hooks to generate")
    parser.add_argument("--validate", nargs="?", const="", help="Tweet text to validate")
    parser.add_argument("--json", action="store_true", help="Output JSON")

    args = parser.parse_args()

    if args.type == "validate" or args.validate is not None:
        text = args.validate or args.topic
        if not text:
            print("Error: provide tweet text to validate", file=sys.stderr)
            sys.exit(1)
        result = validate_tweet(text)
        if args.json:
            print(json.dumps(asdict(result), indent=2))
        else:
            icon = "🔴" if result.over_limit else "✅"
            print(f"\n  {icon} {result.char_count}/{MAX_TWEET_CHARS} characters")
            if result.warnings:
                for w in result.warnings:
                    print(f"  ⚠️  {w}")
            else:
                print("  No issues found.")
            print()

    elif args.type == "hooks":
        if not args.topic:
            print("Error: --topic required for hook generation", file=sys.stderr)
            sys.exit(1)
        hooks = generate_hooks(args.topic, args.count)
        if args.json:
            print(json.dumps(hooks, indent=2))
        else:
            print(f"\n{'='*60}")
            print(f"  HOOK IDEAS: {args.topic}")
            print(f"{'='*60}\n")
            for i, h in enumerate(hooks, 1):
                print(f"  {i:2d}. [{h['type']:<12}] {h['hook']}")
                print(f"      ({h['chars']} chars)")
            print()

    elif args.type == "thread":
        if not args.topic:
            print("Error: --topic required for thread generation", file=sys.stderr)
            sys.exit(1)
        outline = generate_thread_outline(args.topic, args.tweets)
        print(outline)

    elif args.type == "tweet":
        if not args.topic:
            print("Error: --topic required", file=sys.stderr)
            sys.exit(1)
        hooks = generate_hooks(args.topic, 5)
        print(f"\n  5 tweet drafts for: {args.topic}\n")
        for i, h in enumerate(hooks, 1):
            print(f"  {i}. {h['hook']}")
            print(f"     ({h['chars']} chars)\n")


if __name__ == "__main__":
    main()
