import argparse
import datetime
import json
import os
import sys
import urllib.request
import urllib.error
import urllib.parse

def fetch_items(item_type, repo, status='open', days=None, limit=10, token=None):
    """
    Fetches issues or pull requests from a GitHub repository using urllib.
    """
    if item_type == "issues":
        endpoint = "issues"
    elif item_type == "prs":
        endpoint = "pulls"
    else:
        print(f"Error: Invalid item_type '{item_type}'. Must be 'issues' or 'prs'.", file=sys.stderr)
        sys.exit(1)

    base_url = f"https://api.github.com/repos/{repo}/{endpoint}"
    
    params = {
        "state": status,
        "per_page": 100,
        "sort": "updated",
        "direction": "desc"
    }

    if days and item_type == "issues":
        since_date = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=int(days))
        params["since"] = since_date.strftime('%Y-%m-%dT%H:%M:%SZ')

    query_string = urllib.parse.urlencode(params)
    url = f"{base_url}?{query_string}"

    headers = {
        "Accept": "application/vnd.github.v3+json",
        "User-Agent": "Agent-Skills-CLI"
    }
    if token:
        headers["Authorization"] = f"token {token}"

    req = urllib.request.Request(url, headers=headers)

    try:
        with urllib.request.urlopen(req) as response:
            if response.status != 200:
                print(f"Error: Received status code {response.status}", file=sys.stderr)
                sys.exit(1)
            items = json.loads(response.read().decode())
    except urllib.error.HTTPError as e:
        print(f"HTTP Error: {e.code} {e.reason}", file=sys.stderr)
        try:
            error_body = json.loads(e.read().decode())
            print(f"Message: {error_body.get('message')}", file=sys.stderr)
        except:
            pass
        sys.exit(1)
    except Exception as e:
        print(f"Error fetching {item_type}: {e}", file=sys.stderr)
        sys.exit(1)

    # Post-fetch filtering for PRs or if 'since' not supported
    if days and item_type == "prs":
        since_date = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=int(days))
        filtered_items = []
        for item in items:
            updated_at = datetime.datetime.strptime(item['updated_at'], '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=datetime.timezone.utc)
            if updated_at >= since_date:
                filtered_items.append(item)
            else:
                break
        items = filtered_items

    # Filter out pull requests from issues endpoint result
    if item_type == "issues":
        items = [item for item in items if "pull_request" not in item]
    
    # Apply limit
    items = items[:limit]

    return items

def print_items(items, item_type):
    if not items:
        print(f"No {item_type} found matching the criteria.")
        return

    print(f"Found {len(items)} {item_type}:\n")
    for item in items:
        updated_at = item.get('updated_at', '')[:10]
        print(f"#{item['number']} [{item['state']}] {item['title']}")
        print(f"  Updated: {updated_at} by {item['user']['login']}")
        print(f"  URL: {item['html_url']}")
        body = item.get('body') or ""
        if body:
            truncated_body = body[:500] + "..." if len(body) > 500 else body
            print(f"  Content:\n{truncated_body}")
        print("-" * 40)

def main():
    parser = argparse.ArgumentParser(description="Fetch GitHub issues or pull requests.")
    parser.add_argument("item_type", choices=['issues', 'prs'], help="Type of item to fetch: 'issues' or 'prs'")
    parser.add_argument("repo", help="Repository in 'owner/name' format")
    parser.add_argument("--status", choices=['open', 'closed', 'all'], default='open', help="Item status")
    parser.add_argument("--days", type=int, help="Filter by updated in the last N days")
    parser.add_argument("--limit", type=int, default=10, help="Max number of items to return")
    
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print("Warning: GITHUB_TOKEN environment variable not set. Using unauthenticated request (rate limited).", file=sys.stderr)

    items = fetch_items(args.item_type, args.repo, args.status, args.days, args.limit, token)
    print_items(items, args.item_type)

if __name__ == "__main__":
    main()
