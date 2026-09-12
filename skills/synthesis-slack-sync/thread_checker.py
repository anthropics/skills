#!/usr/bin/env python3
"""
Thread Checker — Pre-sync checklist generator for synthesis-slack-sync.

Reads the local transcript file and daily action plan, extracts every thread TS
and draft target, and outputs a structured checklist of threads that MUST be
re-read during the next sync.

Usage:
    python3 thread_checker.py <transcript_file> [action_plan_file]

Output:
    A checklist of parent thread TSes grouped by channel, with channel IDs.
    The agent MUST re-read every thread listed using slack_read_thread.
"""

import re
import sys
from pathlib import Path


def extract_threads(transcript_path: str) -> list[dict]:
    """Extract parent thread TSes and metadata from a transcript file."""
    content = Path(transcript_path).read_text()
    lines = content.split('\n')

    threads = []
    seen_ts = set()
    current_channel = None
    current_channel_id = None

    # Channel header with ID: ## #channel-name (CHANNEL_ID)
    channel_header_with_id = re.compile(r'^#{1,3}\s+#([\w-]+)\s*\(([A-Z][A-Z0-9]+)\)')
    # Channel header without ID: ### #channel-name (used in mid-day/evening sync sections)
    channel_header_no_id = re.compile(r'^#{1,3}\s+#([\w-]+)\s*$')

    # TS pattern in parentheses: (TS: 1775064672.791199)
    ts_in_parens = re.compile(r'\(TS:\s*([\d.]+)\)')

    # Reply count patterns
    reply_count_pattern = re.compile(r'(\d+)\s*repl(?:y|ies)')
    thread_label = re.compile(r'\*\*Thread\s*\((\d+)\s*repl')

    # First pass: build channel name → ID map from headers that have IDs
    channel_id_map = {}
    for line in lines:
        m = channel_header_with_id.match(line.strip())
        if m:
            channel_id_map[m.group(1)] = m.group(2)

    for i, line in enumerate(lines):
        # Track channel context — try header with ID first, then without
        ch_match = channel_header_with_id.match(line.strip())
        if ch_match:
            current_channel = ch_match.group(1)
            current_channel_id = ch_match.group(2)
            continue
        ch_match_no_id = channel_header_no_id.match(line.strip())
        if ch_match_no_id:
            current_channel = ch_match_no_id.group(1)
            current_channel_id = channel_id_map.get(current_channel, current_channel_id)
            continue

        # Find TSes — only from lines that look like message headers or thread parents
        # (lines starting with #### or containing "TS:" in a header-like context)
        ts_matches = ts_in_parens.findall(line)
        if not ts_matches:
            continue

        for ts in ts_matches:
            if ts in seen_ts:
                continue

            # Determine if this is a parent message or a reply
            # Parent messages are on lines starting with ####, or top-level entries
            # Reply TSes are typically on lines starting with "- " (list items)
            stripped = line.strip()
            is_parent = stripped.startswith('####') or stripped.startswith('## ')
            is_reply = stripped.startswith('- ') or stripped.startswith('> ')

            # Skip reply TSes — we only want parent messages
            if is_reply:
                continue

            # Get reply count from surrounding context
            reply_count = 0
            context_window = '\n'.join(lines[max(0, i):min(len(lines), i + 5)])
            thread_match = thread_label.search(context_window)
            if thread_match:
                reply_count = int(thread_match.group(1))
            else:
                reply_match = reply_count_pattern.search(context_window)
                if reply_match:
                    reply_count = int(reply_match.group(1))

            # Get context
            context = stripped[:100]

            seen_ts.add(ts)
            threads.append({
                'ts': ts,
                'channel': current_channel or 'unknown',
                'channel_id': current_channel_id or '?',
                'reply_count': reply_count,
                'context': context,
            })

    return threads


def extract_unsent_drafts(action_plan_path: str) -> list[dict]:
    """Extract unsent draft thread TSes from the action plan."""
    content = Path(action_plan_path).read_text()
    drafts = []
    seen_drafts = set()

    # Find draft sections that are NOT struck through
    lines = content.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i]

        # Match draft headers: ### Draft N: ...
        # Skip struck-through: ### ~~Draft N...~~ SENT
        draft_match = re.match(r'^###\s+Draft\s+(\d+):\s*(.*)', line.strip())
        if draft_match and '~~' not in line and 'SENT' not in line:
            draft_num = int(draft_match.group(1))
            draft_title = draft_match.group(2)

            if draft_num in seen_drafts:
                i += 1
                continue
            seen_drafts.add(draft_num)

            # Scan the next ~20 lines for a TS
            block = '\n'.join(lines[i:i + 20])
            ts_match = re.search(r'TS:\s*([\d.]+)', block)
            channel_match = re.search(r'Channel.*?([A-Z][A-Z0-9]{8,})', block)

            drafts.append({
                'number': draft_num,
                'title': draft_title,
                'ts': ts_match.group(1) if ts_match else None,
                'channel_id': channel_match.group(1) if channel_match else None,
            })

        i += 1

    return drafts


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 thread_checker.py <transcript_file> [action_plan_file]")
        sys.exit(1)

    transcript_path = sys.argv[1]
    action_plan_path = sys.argv[2] if len(sys.argv) > 2 else None

    if not Path(transcript_path).exists():
        print(f"ERROR: Transcript file not found: {transcript_path}")
        sys.exit(1)

    threads = extract_threads(transcript_path)

    print("=" * 70)
    print("THREAD CHECKER — Pre-Sync Checklist")
    print("=" * 70)
    print(f"Transcript: {Path(transcript_path).name}")
    print(f"Parent threads found: {len(threads)}")
    print()

    # Group by channel
    by_channel = {}
    for t in threads:
        key = (t['channel'], t['channel_id'])
        if key not in by_channel:
            by_channel[key] = []
        by_channel[key].append(t)

    print("THREADS TO RE-READ:")
    print("-" * 70)
    total = 0
    for (channel, channel_id), channel_threads in sorted(by_channel.items()):
        print(f"\n  #{channel} ({channel_id})")
        for t in channel_threads:
            total += 1
            replies = f" — {t['reply_count']} replies recorded" if t['reply_count'] > 0 else ""
            print(f"    [{total:2d}] message_ts=\"{t['ts']}\"{replies}")
            print(f"         {t['context'][:80]}")

    print(f"\n  TOTAL: {total} threads. Re-read ALL using slack_read_thread.")
    print()

    # Unsent draft verification
    if action_plan_path and Path(action_plan_path).exists():
        drafts = extract_unsent_drafts(action_plan_path)

        if drafts:
            print("=" * 70)
            print("UNSENT DRAFT VERIFICATION")
            print("Before marking any draft as 'not sent', re-read its target thread:")
            print("-" * 70)
            for d in drafts:
                ts_info = f"message_ts=\"{d['ts']}\"" if d['ts'] else "NO TS FOUND — search manually"
                print(f"    Draft {d['number']}: {d['title']}")
                print(f"      → slack_read_thread({ts_info})")
            print()
        else:
            print("No unsent drafts with thread TSes found.")
            print()

    print("=" * 70)
    print("Run slack_read_thread for EVERY thread above. Compare reply counts.")
    print("Append new replies to transcript. Do NOT skip any thread.")
    print("=" * 70)


if __name__ == '__main__':
    main()
