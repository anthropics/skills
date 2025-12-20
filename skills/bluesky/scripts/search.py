#!/usr/bin/env python3
"""
Bluesky Search - Search posts, users, and feeds.

Usage:
    python search.py posts "query"              # Search posts
    python search.py users "query"              # Search users
    python search.py feeds "query"              # Search custom feeds
"""

import argparse
import json
import os
import sys
from datetime import datetime

def search_posts(query: str, author: str = None, since: str = None,
                 lang: str = None, limit: int = 20) -> dict:
    """Search posts."""
    results = {
        "query": query,
        "filters": {
            "author": author,
            "since": since,
            "lang": lang
        },
        "posts": [
            {
                "author": "user1.bsky.social",
                "text": f"Sample post about {query}",
                "created_at": datetime.now().isoformat(),
                "uri": "at://did:plc:xxx/app.bsky.feed.post/yyy",
                "likes": 10,
                "reposts": 2,
                "replies": 3
            },
            {
                "author": "user2.bsky.social",
                "text": f"Another post mentioning {query}",
                "created_at": datetime.now().isoformat(),
                "uri": "at://did:plc:aaa/app.bsky.feed.post/bbb",
                "likes": 5,
                "reposts": 1,
                "replies": 0
            }
        ],
        "total": 2,
        "note": "This is a demonstration. Install atproto for real search."
    }
    return results

def search_users(query: str, limit: int = 20) -> dict:
    """Search users by name or bio."""
    return {
        "query": query,
        "users": [
            {
                "handle": "matching-user.bsky.social",
                "display_name": f"User interested in {query}",
                "description": f"Bio mentioning {query}",
                "followers_count": 500
            }
        ],
        "total": 1,
        "note": "This is a demonstration."
    }

def search_feeds(query: str = None, popular: bool = False, limit: int = 20) -> dict:
    """Search custom feeds."""
    return {
        "query": query,
        "feeds": [
            {
                "name": f"{query or 'Popular'} Feed",
                "uri": "at://did:plc:xxx/app.bsky.feed.generator/yyy",
                "creator": "feedcreator.bsky.social",
                "description": f"Custom feed about {query or 'various topics'}",
                "likes": 1000
            }
        ],
        "total": 1,
        "note": "This is a demonstration."
    }

def format_posts(data: dict, as_json: bool = False) -> str:
    """Format post search results."""
    if as_json:
        return json.dumps(data, indent=2)

    lines = [f"Posts matching '{data['query']}' ({data.get('total', 0)} results)"]
    for p in data.get("posts", []):
        lines.append(f"\n@{p['author']}")
        lines.append(f"  {p['text'][:100]}...")
        lines.append(f"  ♥ {p.get('likes', 0)} ↻ {p.get('reposts', 0)} 💬 {p.get('replies', 0)}")
        lines.append(f"  URI: {p['uri']}")
    if data.get("note"):
        lines.append(f"\nNote: {data['note']}")
    return "\n".join(lines)

def format_users(data: dict, as_json: bool = False) -> str:
    """Format user search results."""
    if as_json:
        return json.dumps(data, indent=2)

    lines = [f"Users matching '{data['query']}' ({data.get('total', 0)} results)"]
    for u in data.get("users", []):
        lines.append(f"\n@{u['handle']}")
        lines.append(f"  {u.get('display_name', '')}")
        lines.append(f"  {u.get('description', '')[:80]}")
        lines.append(f"  Followers: {u.get('followers_count', 0)}")
    if data.get("note"):
        lines.append(f"\nNote: {data['note']}")
    return "\n".join(lines)

def format_feeds(data: dict, as_json: bool = False) -> str:
    """Format feed search results."""
    if as_json:
        return json.dumps(data, indent=2)

    lines = [f"Feeds ({data.get('total', 0)} results)"]
    for f in data.get("feeds", []):
        lines.append(f"\n{f['name']}")
        lines.append(f"  By: @{f['creator']}")
        lines.append(f"  {f.get('description', '')[:80]}")
        lines.append(f"  Likes: {f.get('likes', 0)}")
    if data.get("note"):
        lines.append(f"\nNote: {data['note']}")
    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(
        description="Bluesky Search",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python search.py posts "climate change"
  python search.py posts "python" --author alice.bsky.social
  python search.py posts "news" --since 2024-01-01 --lang en
  python search.py users "developer"
  python search.py feeds "photography"
  python search.py feeds --popular
        """
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Posts search
    posts_parser = subparsers.add_parser("posts", help="Search posts")
    posts_parser.add_argument("query", nargs="?", help="Search query")
    posts_parser.add_argument("--author", "-a", help="Filter by author")
    posts_parser.add_argument("--since", help="Posts since date (YYYY-MM-DD)")
    posts_parser.add_argument("--lang", help="Language code (en, ja, etc)")
    posts_parser.add_argument("--limit", "-n", type=int, default=20)
    posts_parser.add_argument("--json", action="store_true")

    # Users search
    users_parser = subparsers.add_parser("users", help="Search users")
    users_parser.add_argument("query", help="Search query")
    users_parser.add_argument("--limit", "-n", type=int, default=20)
    users_parser.add_argument("--json", action="store_true")

    # Feeds search
    feeds_parser = subparsers.add_parser("feeds", help="Search custom feeds")
    feeds_parser.add_argument("query", nargs="?", help="Search query")
    feeds_parser.add_argument("--popular", action="store_true", help="Show popular feeds")
    feeds_parser.add_argument("--limit", "-n", type=int, default=20)
    feeds_parser.add_argument("--json", action="store_true")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return

    if args.command == "posts":
        if not args.query and not args.author:
            print("Error: Provide a query or --author")
            return
        result = search_posts(args.query or "", args.author, args.since, args.lang, args.limit)
        print(format_posts(result, args.json))

    elif args.command == "users":
        result = search_users(args.query, args.limit)
        print(format_users(result, args.json))

    elif args.command == "feeds":
        result = search_feeds(args.query, args.popular, args.limit)
        print(format_feeds(result, args.json))

if __name__ == "__main__":
    main()
