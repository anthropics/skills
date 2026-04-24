"""
YouTube Livestream Comment Downloader
=====================================
Downloads live chat from a YouTube livestream and exports to CSV + Markdown summary.

Usage:
    python download-comments.py <YOUTUBE_URL>
    python download-comments.py https://www.youtube.com/watch?v=VIDEO_ID

Output (saved to ~/Downloads/):
    - livestream_comments.csv       (Timestamp, Author, Message)
    - livestream_summary.md         (Quick stats + sample comments)
"""

import sys
import os
import csv
import json
import subprocess
import tempfile
from datetime import datetime
from collections import Counter

OUTPUT_DIR = os.path.join(os.path.expanduser("~"), "Downloads")


def download_chat(url):
    """Download live chat messages using yt-dlp."""
    print(f"⬇️  Downloading chat from: {url}")

    with tempfile.TemporaryDirectory() as tmpdir:
        out_template = os.path.join(tmpdir, "chat")
        result = subprocess.run(
            [
                sys.executable, "-m", "yt_dlp",
                "--write-subs",
                "--sub-langs", "live_chat",
                "--skip-download",
                "-o", out_template,
                url,
            ],
            capture_output=True, text=True,
        )

        if result.returncode != 0:
            print(f"❌ yt-dlp error: {result.stderr.strip()}")
            return []

        chat_file = None
        for f in os.listdir(tmpdir):
            if "live_chat" in f and f.endswith(".json"):
                chat_file = os.path.join(tmpdir, f)
                break

        if not chat_file:
            print("❌ No live chat file found. Does this stream have chat replay?")
            return []

        messages = []
        with open(chat_file, "r", encoding="utf-8") as f:
            for line in f:
                try:
                    entry = json.loads(line.strip())
                    actions = entry.get("replayChatItemAction", {}).get("actions", [])
                    for action in actions:
                        item = action.get("addChatItemAction", {}).get("item", {})
                        renderer = item.get("liveChatTextMessageRenderer", {})
                        if not renderer:
                            continue

                        author = renderer.get("authorName", {}).get("simpleText", "Unknown")
                        timestamp = renderer.get("timestampText", {}).get("simpleText", "")

                        msg_parts = []
                        for run in renderer.get("message", {}).get("runs", []):
                            if "text" in run:
                                msg_parts.append(run["text"])
                            elif "emoji" in run:
                                alt = run["emoji"].get("shortcuts", [""])[0] or run["emoji"].get("emojiId", "")
                                msg_parts.append(alt)
                        message = "".join(msg_parts)

                        if message:
                            messages.append({
                                "timestamp": timestamp,
                                "author": author,
                                "message": message,
                            })
                except (json.JSONDecodeError, KeyError):
                    continue

    print(f"✅ Downloaded {len(messages)} messages")
    return messages


def export_csv(messages, path):
    """Export messages to CSV."""
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["timestamp", "author", "message"])
        writer.writeheader()
        writer.writerows(messages)
    print(f"📄 CSV saved to: {path}")


def generate_summary(messages, url, path):
    """Generate a Markdown summary with basic stats."""
    unique_authors = set(m["author"] for m in messages)
    author_counts = Counter(m["author"] for m in messages)
    top_authors = author_counts.most_common(10)
    avg_len = sum(len(m["message"]) for m in messages) / max(len(messages), 1)

    with open(path, "w", encoding="utf-8") as f:
        f.write(f"# YouTube Livestream Chat Summary\n\n")
        f.write(f"**Source:** {url}  \n")
        f.write(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M')}  \n\n")
        f.write(f"## 📊 Quick Stats\n\n")
        f.write(f"| Metric | Value |\n")
        f.write(f"|--------|-------|\n")
        f.write(f"| Total messages | {len(messages)} |\n")
        f.write(f"| Unique participants | {len(unique_authors)} |\n")
        f.write(f"| Avg message length | {avg_len:.0f} chars |\n\n")
        f.write(f"## 🏆 Top 10 Most Active Participants\n\n")
        f.write(f"| Author | Messages |\n")
        f.write(f"|--------|----------|\n")
        for author, count in top_authors:
            f.write(f"| {author} | {count} |\n")
        f.write(f"\n## 🔍 Next Steps\n\n")
        f.write(f"Run sentiment analysis, theme extraction, or geographic breakdown\n")
        f.write(f"using the youtube-analysis skill.\n")

    print(f"📝 Summary saved to: {path}")


def main():
    if len(sys.argv) < 2:
        print("Usage: python download-comments.py <YOUTUBE_URL>")
        print('Example: python download-comments.py "https://www.youtube.com/watch?v=VIDEO_ID"')
        sys.exit(1)

    url = sys.argv[1]
    csv_path = os.path.join(OUTPUT_DIR, "livestream_comments.csv")
    summary_path = os.path.join(OUTPUT_DIR, "livestream_summary.md")

    messages = download_chat(url)
    if not messages:
        print("❌ No messages found. Is the URL correct and does the stream have chat?")
        sys.exit(1)

    export_csv(messages, csv_path)
    generate_summary(messages, url, summary_path)

    print(f"\n🎉 Done! {len(messages)} comments ready.")
    print(f"   CSV:     {csv_path}")
    print(f"   Summary: {summary_path}")


if __name__ == "__main__":
    main()
