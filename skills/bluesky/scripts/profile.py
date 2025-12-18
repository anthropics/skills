#!/usr/bin/env python3
"""
Bluesky Profile Management - View profiles, followers, following.

Usage:
    python profile.py info alice.bsky.social    # View profile
    python profile.py followers alice.bsky.social
    python profile.py follow alice.bsky.social
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
        print("Warning: atproto library not installed")
        return None

    handle = os.environ.get("BLUESKY_HANDLE")
    password = os.environ.get("BLUESKY_PASSWORD")

    if not handle or not password:
        return None

    client = Client()
    try:
        client.login(handle, password)
        return client
    except:
        return None

def get_profile(handle: str) -> dict:
    """Get profile information."""
    # Placeholder - would use client.get_profile()
    return {
        "handle": handle,
        "display_name": handle.split(".")[0].title(),
        "description": "Sample bio description",
        "followers_count": 100,
        "following_count": 50,
        "posts_count": 200,
        "created_at": "2023-01-01T00:00:00Z",
        "note": "This is a demonstration. Install atproto for real data."
    }

def get_followers(handle: str, limit: int = 50) -> dict:
    """Get followers list."""
    return {
        "handle": handle,
        "followers": [
            {"handle": "follower1.bsky.social", "display_name": "Follower One"},
            {"handle": "follower2.bsky.social", "display_name": "Follower Two"},
        ],
        "total": 2,
        "note": "This is a demonstration."
    }

def get_following(handle: str, limit: int = 50) -> dict:
    """Get following list."""
    return {
        "handle": handle,
        "following": [
            {"handle": "friend1.bsky.social", "display_name": "Friend One"},
            {"handle": "friend2.bsky.social", "display_name": "Friend Two"},
        ],
        "total": 2,
        "note": "This is a demonstration."
    }

def follow_user(handle: str) -> dict:
    """Follow a user."""
    return {
        "status": "success",
        "action": "follow",
        "handle": handle,
        "note": "This is a demonstration."
    }

def unfollow_user(handle: str) -> dict:
    """Unfollow a user."""
    return {
        "status": "success",
        "action": "unfollow",
        "handle": handle,
        "note": "This is a demonstration."
    }

def format_profile(data: dict, as_json: bool = False) -> str:
    """Format profile for display."""
    if as_json:
        return json.dumps(data, indent=2)

    if "error" in data:
        return f"Error: {data['error']}"

    lines = [
        f"@{data['handle']}",
        f"  Name: {data.get('display_name', '')}",
        f"  Bio: {data.get('description', '')}",
        f"  Followers: {data.get('followers_count', 0)}",
        f"  Following: {data.get('following_count', 0)}",
        f"  Posts: {data.get('posts_count', 0)}",
    ]
    if data.get("note"):
        lines.append(f"\nNote: {data['note']}")
    return "\n".join(lines)

def format_list(data: dict, list_key: str, as_json: bool = False) -> str:
    """Format followers/following list."""
    if as_json:
        return json.dumps(data, indent=2)

    items = data.get(list_key, [])
    lines = [f"@{data['handle']} - {list_key.title()} ({data.get('total', len(items))})"]
    for item in items:
        lines.append(f"  @{item['handle']} - {item.get('display_name', '')}")
    if data.get("note"):
        lines.append(f"\nNote: {data['note']}")
    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(
        description="Bluesky Profile Management",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python profile.py info alice.bsky.social
  python profile.py followers alice.bsky.social
  python profile.py following alice.bsky.social -n 100
  python profile.py follow alice.bsky.social
  python profile.py unfollow alice.bsky.social
  python profile.py login
        """
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Info command
    info_parser = subparsers.add_parser("info", help="View profile")
    info_parser.add_argument("handle", help="Bluesky handle")
    info_parser.add_argument("--json", action="store_true", help="JSON output")

    # Followers command
    followers_parser = subparsers.add_parser("followers", help="List followers")
    followers_parser.add_argument("handle", help="Bluesky handle")
    followers_parser.add_argument("--limit", "-n", type=int, default=50)
    followers_parser.add_argument("--json", action="store_true")

    # Following command
    following_parser = subparsers.add_parser("following", help="List following")
    following_parser.add_argument("handle", help="Bluesky handle")
    following_parser.add_argument("--limit", "-n", type=int, default=50)
    following_parser.add_argument("--json", action="store_true")

    # Follow command
    follow_parser = subparsers.add_parser("follow", help="Follow user")
    follow_parser.add_argument("handle", help="Handle to follow")

    # Unfollow command
    unfollow_parser = subparsers.add_parser("unfollow", help="Unfollow user")
    unfollow_parser.add_argument("handle", help="Handle to unfollow")

    # Login command
    login_parser = subparsers.add_parser("login", help="Test authentication")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return

    # Normalize handle
    if hasattr(args, "handle"):
        if args.handle.startswith("@"):
            args.handle = args.handle[1:]
        if not "." in args.handle:
            args.handle = f"{args.handle}.bsky.social"

    if args.command == "info":
        result = get_profile(args.handle)
        print(format_profile(result, args.json))

    elif args.command == "followers":
        result = get_followers(args.handle, args.limit)
        print(format_list(result, "followers", args.json))

    elif args.command == "following":
        result = get_following(args.handle, args.limit)
        print(format_list(result, "following", args.json))

    elif args.command == "follow":
        result = follow_user(args.handle)
        print(f"Followed @{args.handle}" if result.get("status") == "success" else f"Error: {result.get('error')}")

    elif args.command == "unfollow":
        result = unfollow_user(args.handle)
        print(f"Unfollowed @{args.handle}" if result.get("status") == "success" else f"Error: {result.get('error')}")

    elif args.command == "login":
        client = get_client()
        if client:
            print("Authentication successful!")
        else:
            print("Authentication failed or credentials not set.")
            print("Set BLUESKY_HANDLE and BLUESKY_PASSWORD environment variables")

if __name__ == "__main__":
    main()
