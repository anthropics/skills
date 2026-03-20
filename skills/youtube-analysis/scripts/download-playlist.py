"""
YouTube Playlist Comment Downloader
====================================
Downloads live chat from every video in a YouTube playlist.
Outputs one CSV per video into ~/Downloads/playlist-analysis/.

Usage:
    python download-playlist.py <PLAYLIST_URL>
    python download-playlist.py "https://www.youtube.com/playlist?list=PLj6YeMhvp2S4gpM0lGDd5hIDveC7IsLwv"

Output (saved to ~/Downloads/playlist-analysis/):
    - 01_<video_title>.csv
    - 02_<video_title>.csv
    - ...
    - playlist_index.csv   (index of all videos with metadata)
"""

import sys
import os
import re
import csv
import json
import subprocess
from datetime import datetime

OUTPUT_DIR = os.path.join(os.path.expanduser("~"), "Downloads", "playlist-analysis")


def sanitize_filename(name, max_len=80):
    """Remove unsafe characters from a filename."""
    name = re.sub(r'[<>:"/\\|?*]', '', name)
    name = re.sub(r'\s+', '_', name.strip())
    return name[:max_len]


def get_playlist_videos(playlist_url):
    """Use yt-dlp to list all videos in a playlist."""
    print(f"📋 Fetching playlist info from: {playlist_url}")
    result = subprocess.run(
        [
            sys.executable, "-m", "yt_dlp",
            "--flat-playlist",
            "--dump-json",
            "--no-warnings",
            playlist_url,
        ],
        capture_output=True, text=True,
    )

    if result.returncode != 0:
        print(f"❌ yt-dlp error: {result.stderr.strip()}")
        return []

    videos = []
    for line in result.stdout.strip().splitlines():
        try:
            entry = json.loads(line)
            videos.append({
                "id": entry.get("id", ""),
                "title": entry.get("title", "Unknown"),
                "url": f"https://www.youtube.com/watch?v={entry.get('id', '')}",
                "upload_date": entry.get("upload_date", ""),
            })
        except json.JSONDecodeError:
            continue

    print(f"✅ Found {len(videos)} videos in playlist")
    return videos


def download_chat_for_video(url):
    """Download live chat for a single video. Returns list of messages."""
    import tempfile

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
            return []

        chat_file = None
        for f in os.listdir(tmpdir):
            if "live_chat" in f and f.endswith(".json"):
                chat_file = os.path.join(tmpdir, f)
                break

        if not chat_file:
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

    return messages


def export_csv(messages, path):
    """Export messages to CSV."""
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["timestamp", "author", "message"])
        writer.writeheader()
        writer.writerows(messages)


def main():
    if len(sys.argv) < 2:
        print("Usage: python download-playlist.py <PLAYLIST_URL>")
        print('Example: python download-playlist.py "https://www.youtube.com/playlist?list=PLxxxxxx"')
        sys.exit(1)

    playlist_url = sys.argv[1]
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    videos = get_playlist_videos(playlist_url)
    if not videos:
        print("❌ No videos found in playlist.")
        sys.exit(1)

    index_rows = []

    for i, video in enumerate(videos, 1):
        safe_title = sanitize_filename(video["title"])
        csv_filename = f"{i:02d}_{safe_title}.csv"
        csv_path = os.path.join(OUTPUT_DIR, csv_filename)

        print(f"\n[{i}/{len(videos)}] ⬇️  {video['title']}")
        messages = download_chat_for_video(video["url"])

        if messages:
            export_csv(messages, csv_path)
            print(f"   ✅ {len(messages)} messages → {csv_filename}")
        else:
            print(f"   ⚠️  No chat found (may not be a livestream)")

        unique_authors = set(m["author"] for m in messages) if messages else set()
        index_rows.append({
            "number": i,
            "title": video["title"],
            "video_id": video["id"],
            "upload_date": video.get("upload_date", ""),
            "comment_count": len(messages),
            "unique_viewers": len(unique_authors),
            "csv_file": csv_filename if messages else "",
        })

    # Write playlist index
    index_path = os.path.join(OUTPUT_DIR, "playlist_index.csv")
    with open(index_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=[
            "number", "title", "video_id", "upload_date",
            "comment_count", "unique_viewers", "csv_file"
        ])
        writer.writeheader()
        writer.writerows(index_rows)

    total_comments = sum(r["comment_count"] for r in index_rows)
    streams_with_chat = sum(1 for r in index_rows if r["comment_count"] > 0)

    print(f"\n🎉 Done!")
    print(f"   Videos processed: {len(videos)}")
    print(f"   Streams with chat: {streams_with_chat}")
    print(f"   Total comments: {total_comments}")
    print(f"   Output folder: {OUTPUT_DIR}")
    print(f"   Index file: {index_path}")
    print(f"\n💡 Tip: Ask Copilot to 'compare sentiment across my playlist streams'")


if __name__ == "__main__":
    main()
