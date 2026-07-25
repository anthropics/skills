#!/usr/bin/env python3
"""AgentHub message board manager.

CRUD operations for the agent message board: list channels, read posts,
create new posts, and reply to threads.

Usage:
    python board_manager.py --list
    python board_manager.py --read dispatch
    python board_manager.py --post --channel results --author agent-1 --message "Task complete"
    python board_manager.py --thread 001-agent-1 --message "Additional details"
    python board_manager.py --demo
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone


BOARD_PATH = ".agenthub/board"


def get_board_path():
    """Get the board directory path."""
    if not os.path.isdir(BOARD_PATH):
        print(f"Error: Board not found at {BOARD_PATH}. Run hub_init.py first.",
              file=sys.stderr)
        sys.exit(1)
    return BOARD_PATH


def load_index():
    """Load the board index."""
    index_path = os.path.join(get_board_path(), "_index.json")
    if not os.path.exists(index_path):
        return {"channels": ["dispatch", "progress", "results"], "counters": {}}
    with open(index_path) as f:
        return json.load(f)


def save_index(index):
    """Save the board index."""
    index_path = os.path.join(get_board_path(), "_index.json")
    with open(index_path, "w") as f:
        json.dump(index, f, indent=2)
        f.write("\n")


def list_channels(output_format="text"):
    """List all board channels with post counts."""
    index = load_index()
    channels = []
    for ch in index.get("channels", []):
        ch_path = os.path.join(get_board_path(), ch)
        count = 0
        if os.path.isdir(ch_path):
            count = len([f for f in os.listdir(ch_path)
                        if f.endswith(".md")])
        channels.append({"channel": ch, "posts": count})

    if output_format == "json":
        print(json.dumps({"channels": channels}, indent=2))
    else:
        print("Board Channels:")
        print()
        for ch in channels:
            print(f"  {ch['channel']:<15} {ch['posts']} posts")


def parse_post_frontmatter(content):
    """Parse YAML frontmatter from a post."""
    metadata = {}
    body = content
    if content.startswith("---"):
        parts = content.split("---", 2)
        if len(parts) >= 3:
            fm = parts[1].strip()
            body = parts[2].strip()
            for line in fm.split("\n"):
                if ":" in line:
                    key, val = line.split(":", 1)
                    metadata[key.strip()] = val.strip()
    return metadata, body


def read_channel(channel, output_format="text"):
    """Read all posts in a channel."""
    ch_path = os.path.join(get_board_path(), channel)
    if not os.path.isdir(ch_path):
        print(f"Error: Channel '{channel}' not found", file=sys.stderr)
        sys.exit(1)

    files = sorted([f for f in os.listdir(ch_path) if f.endswith(".md")])
    posts = []

    for fname in files:
        filepath = os.path.join(ch_path, fname)
        with open(filepath) as f:
            content = f.read()
        metadata, body = parse_post_frontmatter(content)
        posts.append({
            "file": fname,
            "metadata": metadata,
            "body": body,
        })

    if output_format == "json":
        print(json.dumps({"channel": channel, "posts": posts}, indent=2))
    else:
        print(f"Channel: {channel} ({len(posts)} posts)")
        print("=" * 60)
        for post in posts:
            author = post["metadata"].get("author", "unknown")
            timestamp = post["metadata"].get("timestamp", "")
            print(f"\n--- {post['file']} (by {author}, {timestamp}) ---")
            print(post["body"])


def create_post(channel, author, message, parent=None):
    """Create a new post in a channel."""
    ch_path = os.path.join(get_board_path(), channel)
    os.makedirs(ch_path, exist_ok=True)

    # Get next sequence number
    index = load_index()
    counters = index.get("counters", {})
    seq = counters.get(channel, 0) + 1
    counters[channel] = seq
    index["counters"] = counters
    save_index(index)

    # Generate filename
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    safe_author = re.sub(r"[^a-zA-Z0-9_-]", "", author)
    filename = f"{seq:03d}-{safe_author}-{timestamp}.md"

    # Build post content
    lines = [
        "---",
        f"author: {author}",
        f"timestamp: {datetime.now(timezone.utc).isoformat()}",
        f"channel: {channel}",
        f"sequence: {seq}",
    ]
    if parent:
        lines.append(f"parent: {parent}")
    else:
        lines.append("parent: null")
    lines.append("---")
    lines.append("")
    lines.append(message)
    lines.append("")

    filepath = os.path.join(ch_path, filename)
    with open(filepath, "w") as f:
        f.write("\n".join(lines))

    print(f"Posted to {channel}/{filename}")
    return filename


def run_demo():
    """Show demo output."""
    print("=" * 60)
    print("AgentHub Board Manager — Demo Mode")
    print("=" * 60)
    print()

    print("--- Channel List ---")
    print("Board Channels:")
    print()
    print("  dispatch        2 posts")
    print("  progress        4 posts")
    print("  results         3 posts")
    print()

    print("--- Read Channel: results ---")
    print("Channel: results (3 posts)")
    print("=" * 60)
    print()
    print("--- 001-agent-1-20260317T143510Z.md (by agent-1, 2026-03-17T14:35:10Z) ---")
    print("## Result Summary")
    print()
    print("- **Approach**: Added caching layer for database queries")
    print("- **Files changed**: 3")
    print("- **Metric**: 165ms (baseline: 180ms, delta: -15ms)")
    print("- **Confidence**: Medium — 2 edge cases not covered")
    print()
    print("--- 002-agent-2-20260317T143645Z.md (by agent-2, 2026-03-17T14:36:45Z) ---")
    print("## Result Summary")
    print()
    print("- **Approach**: Replaced O(n²) sort with hash map lookup")
    print("- **Files changed**: 2")
    print("- **Metric**: 142ms (baseline: 180ms, delta: -38ms)")
    print("- **Confidence**: High — all tests pass")
    print()
    print("--- 003-agent-3-20260317T143422Z.md (by agent-3, 2026-03-17T14:34:22Z) ---")
    print("## Result Summary")
    print()
    print("- **Approach**: Minor loop optimizations")
    print("- **Files changed**: 1")
    print("- **Metric**: 190ms (baseline: 180ms, delta: +10ms)")
    print("- **Confidence**: Low — no meaningful improvement")


def main():
    parser = argparse.ArgumentParser(
        description="AgentHub message board manager"
    )
    parser.add_argument("--list", action="store_true",
                        help="List all channels with post counts")
    parser.add_argument("--read", type=str, metavar="CHANNEL",
                        help="Read all posts in a channel")
    parser.add_argument("--post", action="store_true",
                        help="Create a new post")
    parser.add_argument("--channel", type=str,
                        help="Channel for --post or --thread")
    parser.add_argument("--author", type=str,
                        help="Author name for --post")
    parser.add_argument("--message", type=str,
                        help="Message content for --post or --thread")
    parser.add_argument("--thread", type=str, metavar="POST_ID",
                        help="Reply to a post (sets parent)")
    parser.add_argument("--format", choices=["text", "json"], default="text",
                        help="Output format (default: text)")
    parser.add_argument("--demo", action="store_true",
                        help="Show demo output")
    args = parser.parse_args()

    if args.demo:
        run_demo()
        return

    if args.list:
        list_channels(args.format)
        return

    if args.read:
        read_channel(args.read, args.format)
        return

    if args.post:
        if not args.channel or not args.author or not args.message:
            print("Error: --post requires --channel, --author, and --message",
                  file=sys.stderr)
            sys.exit(1)
        create_post(args.channel, args.author, args.message)
        return

    if args.thread:
        if not args.message:
            print("Error: --thread requires --message", file=sys.stderr)
            sys.exit(1)
        channel = args.channel or "results"
        author = args.author or "coordinator"
        create_post(channel, author, args.message, parent=args.thread)
        return

    parser.print_help()


if __name__ == "__main__":
    main()
