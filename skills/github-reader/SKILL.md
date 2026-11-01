---
name: github-reader
description: Fetch and filter GitHub issues or pull requests from a repository. Use this when you need to analyze issues, check recent code changes, or gather data for reports from GitHub.
---

# GitHub Reader

Fetch and filter GitHub issues or pull requests from a specified repository.

## Usage

Use the provided script to fetch items with various filters. The first argument must be `issues` or `prs` to specify what you want to fetch.

### Fetch Open Issues
To fetch the latest 10 open issues from a repository:
```bash
python3 skills/github-reader/scripts/fetch.py issues owner/repo
```

### Fetch Open Pull Requests
To fetch the latest 10 open pull requests:
```bash
python3 skills/github-reader/scripts/fetch.py prs owner/repo
```

### Filter by Status and Time
To fetch all issues and PRs updated or created in the last 7 days:
```bash
python3 skills/github-reader/scripts/fetch.py issues owner/repo --status all --days 7
python3 skills/github-reader/scripts/fetch.py prs owner/repo --status all --days 7
```

### Options
- `item_type`: `issues` or `prs`.
- `repo`: Repository in `owner/name` format.
- `--status`: `open`, `closed`, or `all` (default: `open`).
- `--days`: Filter by items updated within the last N days.
- `--limit`: Maximum number of items to return (default: 10).

## Environment Variables
- `GITHUB_TOKEN`: (Optional) A GitHub Personal Access Token to avoid rate limiting and access private repositories.
