#!/usr/bin/env python3
"""Check GitHub Release download counts for a repo (keychain token on macOS).

Usage:
  python3 check_github_downloads.py <owner/repo> [--token <token>]

Prints per-release asset download counts and a total. Uses the git credential
osxkeychain helper for the token on macOS; falls back to GH_TOKEN env var.
"""
import json
import os
import subprocess
import sys
import urllib.request


def get_token():
    """Try env var first, then git credential helper (macOS keychain)."""
    t = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if t:
        return t
    try:
        r = subprocess.run(
            ["git", "credential-osxkeychain", "get"],
            input="protocol=https\nhost=github.com\n",
            capture_output=True, text=True, timeout=10,
        )
        for line in r.stdout.split("\n"):
            if line.startswith("password="):
                return line.split("=", 1)[1]
    except Exception:
        pass
    return None


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 1
    repo = sys.argv[1].strip("/")
    token = get_token()

    req = urllib.request.Request(
        f"https://api.github.com/repos/{repo}/releases",
        headers={
            "Authorization": f"token {token}",
            "Accept": "application/vnd.github+json",
            "User-Agent": "workbuddy-downloads-check",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            releases = json.loads(resp.read())
    except urllib.error.HTTPError as e:
        print(f"ERROR {e.code}: {e.read().decode()[:300]}")
        return 1

    total = 0
    print(f"=== GitHub Release 下载量: {repo} ===")
    for rel in releases:
        for a in rel.get("assets", []):
            print(f"  {rel['tag_name']:10s} | {a['name']:40s} | {a['download_count']} 次")
            total += a["download_count"]
    print(f"\n  总计: {total} 次下载")
    print(f"  最新版: {releases[0]['tag_name'] if releases else 'N/A'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
