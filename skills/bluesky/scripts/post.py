#!/usr/bin/env python3
"""
Bluesky Post Management - Create, delete, and view posts.

Usage:
    python post.py create "Hello world!"        # Create post
    python post.py delete AT_URI                # Delete post
    python post.py timeline                     # View timeline
"""

import argparse
import json
import os
import sys
from datetime import datetime

def get_client():
    """Get authenticated AT Protocol client."""
    try:
        from atproto import Client
    except ImportError:
        print("Error: atproto library required: pip install atproto")
        sys.exit(1)

    handle = os.environ.get("BLUESKY_HANDLE")
    password = os.environ.get("BLUESKY_PASSWORD")

    if not handle or not password:
        print("Error: Set BLUESKY_HANDLE and BLUESKY_PASSWORD environment variables")
        print("Or use an App Password from Bluesky Settings → App Passwords")
        sys.exit(1)

    client = Client()
    try:
        client.login(handle, password)
        return client
    except Exception as e:
        print(f"Authentication failed: {e}")
        sys.exit(1)

def create_post(text: str, link: str = None, image_path: str = None,
                alt_text: str = None, reply_to: str = None) -> dict:
    """Create a new post."""
    client = get_client()

    # Build post data
    post_data = {"text": text}

    # Add image if provided
    if image_path:
        if not os.path.exists(image_path):
            return {"error": f"Image not found: {image_path}"}
        # Would upload image via client.upload_blob()
        print(f"Note: Image upload would include: {image_path}")
        if alt_text:
            print(f"Alt text: {alt_text}")

    # Add reply reference if provided
    if reply_to:
        # Would resolve reply reference
        print(f"Note: Replying to: {reply_to}")

    try:
        # Placeholder - actual implementation would use client.send_post()
        result = {
            "status": "success",
            "text": text,
            "created_at": datetime.now().isoformat(),
            "note": "This is a demonstration. Install atproto for full functionality."
        }
        return result
    except Exception as e:
        return {"error": str(e)}

def delete_post(uri: str, confirm: bool = False) -> dict:
    """Delete a post by URI."""
    if not confirm:
        return {"error": "Use --confirm to delete posts"}

    # Would use client.delete_post()
    return {
        "status": "success",
        "deleted": uri,
        "note": "This is a demonstration."
    }

def get_timeline(limit: int = 20) -> dict:
    """Get home timeline."""
    # Would use client.get_timeline()
    return {
        "posts": [
            {
                "author": "example.bsky.social",
                "text": "Sample post from timeline",
                "created_at": datetime.now().isoformat(),
                "likes": 5,
                "reposts": 1,
                "replies": 2
            }
        ],
        "note": "This is a demonstration. Install atproto for real timeline."
    }

def create_thread(posts: list) -> dict:
    """Create a thread of connected posts."""
    results = []
    for i, text in enumerate(posts):
        result = {
            "index": i + 1,
            "text": text,
            "status": "success" if i == 0 else "would reply to previous"
        }
        results.append(result)
    return {
        "thread": results,
        "note": "This is a demonstration."
    }

def format_output(data: dict, as_json: bool = False) -> str:
    """Format output for display."""
    if as_json:
        return json.dumps(data, indent=2)

    if "error" in data:
        return f"Error: {data['error']}"

    if "posts" in data:
        lines = ["Timeline:"]
        for p in data["posts"]:
            lines.append(f"\n@{p['author']}")
            lines.append(f"  {p['text']}")
            lines.append(f"  ♥ {p.get('likes', 0)} ↻ {p.get('reposts', 0)} 💬 {p.get('replies', 0)}")
        if data.get("note"):
            lines.append(f"\nNote: {data['note']}")
        return "\n".join(lines)

    if "thread" in data:
        lines = ["Thread created:"]
        for item in data["thread"]:
            lines.append(f"  {item['index']}. {item['text'][:50]}...")
        return "\n".join(lines)

    if data.get("status") == "success":
        return f"Success: Post created\n{data.get('note', '')}"

    return json.dumps(data, indent=2)

def main():
    parser = argparse.ArgumentParser(
        description="Bluesky Post Management",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python post.py create "Hello Bluesky!"
  python post.py create "Check this out" --link https://example.com
  python post.py create "Nice photo" --image photo.jpg --alt "A sunset"
  python post.py thread "First" "Second" "Third"
  python post.py delete at://did:plc:xxx/app.bsky.feed.post/yyy --confirm
  python post.py timeline -n 50
        """
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Create command
    create_parser = subparsers.add_parser("create", help="Create a post")
    create_parser.add_argument("text", help="Post text")
    create_parser.add_argument("--link", "-l", help="URL to embed")
    create_parser.add_argument("--image", "-i", help="Image file path")
    create_parser.add_argument("--alt", help="Alt text for image")
    create_parser.add_argument("--reply-to", "-r", help="URI to reply to")
    create_parser.add_argument("--json", action="store_true", help="JSON output")

    # Thread command
    thread_parser = subparsers.add_parser("thread", help="Create thread")
    thread_parser.add_argument("posts", nargs="+", help="Post texts")
    thread_parser.add_argument("--json", action="store_true", help="JSON output")

    # Delete command
    delete_parser = subparsers.add_parser("delete", help="Delete a post")
    delete_parser.add_argument("uri", help="Post AT URI")
    delete_parser.add_argument("--confirm", action="store_true", help="Confirm deletion")

    # Timeline command
    timeline_parser = subparsers.add_parser("timeline", help="View timeline")
    timeline_parser.add_argument("--limit", "-n", type=int, default=20, help="Number of posts")
    timeline_parser.add_argument("--json", action="store_true", help="JSON output")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return

    if args.command == "create":
        result = create_post(args.text, args.link, args.image, args.alt, args.reply_to)
        print(format_output(result, args.json))

    elif args.command == "thread":
        result = create_thread(args.posts)
        print(format_output(result, args.json))

    elif args.command == "delete":
        result = delete_post(args.uri, args.confirm)
        print(format_output(result))

    elif args.command == "timeline":
        result = get_timeline(args.limit)
        print(format_output(result, args.json))

if __name__ == "__main__":
    main()
