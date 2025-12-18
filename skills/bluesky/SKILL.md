---
name: bluesky
description: AT Protocol client for Bluesky social network management. Use when (1) posting to Bluesky, (2) managing followers/following, (3) searching posts and profiles, (4) content moderation and cleanup, (5) downloading account backups (CAR files), or (6) building Bluesky automation.
license: MIT
---

# Bluesky AT Protocol Client

Comprehensive toolkit for interacting with Bluesky social network via the AT Protocol. Includes posting, profile management, search, content moderation, and bulk operations.

## Helper Scripts Available

- `scripts/post.py` - Create, delete, and search posts
- `scripts/profile.py` - Profile management and follower operations
- `scripts/search.py` - Search posts, users, and feeds
- `scripts/cleanup.py` - Content moderation and bulk delete
- `scripts/backup.py` - Export account data (CAR files)

**Always run scripts with `--help` first** to see usage.

## Setup

### Authentication
```bash
# Interactive login
python scripts/profile.py login

# Or use environment variables
export BLUESKY_HANDLE=yourhandle.bsky.social
export BLUESKY_PASSWORD=your-app-password

# Or use App Password (recommended)
# 1. Go to Settings → App Passwords in Bluesky
# 2. Create new app password
# 3. Use that instead of main password
```

## Quick Start

### Post to Bluesky
```bash
# Simple post
python scripts/post.py create "Hello from the command line!"

# Post with link
python scripts/post.py create "Check out this article" --link https://example.com

# Post with image
python scripts/post.py create "Beautiful sunset" --image sunset.jpg --alt "Orange sunset over mountains"

# Reply to a post
python scripts/post.py create "Great point!" --reply-to at://did:plc:xxx/app.bsky.feed.post/yyy
```

### Search Posts
```bash
# Search by keyword
python scripts/search.py posts "climate change"

# Search user's posts
python scripts/search.py posts --author alice.bsky.social

# Recent posts with hashtag
python scripts/search.py posts "#coding"
```

### Profile Operations
```bash
# View profile
python scripts/profile.py info alice.bsky.social

# List followers
python scripts/profile.py followers alice.bsky.social

# List following
python scripts/profile.py following alice.bsky.social

# Follow/unfollow
python scripts/profile.py follow alice.bsky.social
python scripts/profile.py unfollow alice.bsky.social
```

## Post Management

### Create Posts
```bash
# Text only
python scripts/post.py create "My post content"

# With mentions
python scripts/post.py create "Hey @alice.bsky.social check this out!"

# With hashtags (auto-linked)
python scripts/post.py create "Learning #Python is fun #coding"

# Thread (multiple connected posts)
python scripts/post.py thread "First post" "Second post" "Third post"
```

### Delete Posts
```bash
# Delete by URI
python scripts/post.py delete at://did:plc:xxx/app.bsky.feed.post/yyy

# Delete recent posts by keyword (careful!)
python scripts/post.py delete --matching "test" --dry-run
python scripts/post.py delete --matching "test" --confirm
```

### View Posts
```bash
# Get your timeline
python scripts/post.py timeline

# Get specific feed
python scripts/post.py feed "at://did:plc:xxx/app.bsky.feed.generator/yyy"

# Get post thread
python scripts/post.py thread-view "at://did:plc:xxx/app.bsky.feed.post/yyy"
```

## Search Capabilities

### Post Search
```bash
python scripts/search.py posts "query"           # Basic search
python scripts/search.py posts "query" -n 50     # More results
python scripts/search.py posts "query" --since 2024-01-01  # Date filter
python scripts/search.py posts "query" --lang en # Language filter
```

### User Search
```bash
python scripts/search.py users "alice"           # Search by name
python scripts/search.py users "python developer" # Search by bio
```

### Feed Discovery
```bash
python scripts/search.py feeds "photography"     # Find custom feeds
python scripts/search.py feeds --popular         # Popular feeds
```

## Content Cleanup

### Find Problematic Content
```bash
# Find posts with low engagement (potential cleanup candidates)
python scripts/cleanup.py audit --min-likes 0 --min-replies 0

# Find old posts
python scripts/cleanup.py audit --before 2023-01-01

# Find posts matching pattern
python scripts/cleanup.py audit --matching "test"
```

### Bulk Delete (with safety)
```bash
# Always dry-run first!
python scripts/cleanup.py delete --before 2023-01-01 --dry-run

# Then execute with confirmation
python scripts/cleanup.py delete --before 2023-01-01 --confirm

# Delete by engagement threshold
python scripts/cleanup.py delete --max-likes 0 --max-replies 0 --dry-run
```

### Export Before Delete
```bash
# Export posts before cleanup
python scripts/cleanup.py export -o my_posts.json
python scripts/cleanup.py delete --before 2023-01-01 --confirm
```

## Account Backup

### Download CAR File
```bash
# Full account backup
python scripts/backup.py download

# Specific collections
python scripts/backup.py download --collection app.bsky.feed.post
python scripts/backup.py download --collection app.bsky.feed.like
```

### Export Data
```bash
# Export posts to JSON
python scripts/backup.py export posts -o posts.json

# Export likes
python scripts/backup.py export likes -o likes.json

# Export everything
python scripts/backup.py export all -o backup/
```

## AT Protocol Concepts

### URI Format
```
at://did:plc:XXXX/app.bsky.feed.post/YYYY
│     │          │                    │
│     │          │                    └─ Record key
│     │          └─ Collection type
│     └─ DID (Decentralized Identifier)
└─ AT Protocol scheme
```

### Collections
| Collection | Content |
|------------|---------|
| `app.bsky.feed.post` | Posts |
| `app.bsky.feed.like` | Likes |
| `app.bsky.feed.repost` | Reposts |
| `app.bsky.graph.follow` | Follows |
| `app.bsky.graph.block` | Blocks |
| `app.bsky.graph.list` | Lists |

### Rate Limits
- **3000 requests per 5 minutes** (global)
- **Batch operations**: 25 profiles per request
- Scripts include automatic rate limiting

## Configuration

### Environment Variables
```bash
# Authentication
export BLUESKY_HANDLE=handle.bsky.social
export BLUESKY_PASSWORD=app-password

# Optional
export BLUESKY_PDS=https://bsky.social  # Default PDS
export BLUESKY_CACHE_DIR=~/.bluesky/cache
```

### Config File
```json
{
  "handle": "yourhandle.bsky.social",
  "pds": "https://bsky.social",
  "cache_enabled": true,
  "rate_limit_delay": 0.05
}
```

## Common Options

```bash
--handle, -u      Bluesky handle (user.bsky.social)
--output, -o      Output file
--json            JSON output format
--dry-run         Preview without executing
--confirm         Require confirmation for destructive ops
--limit, -n       Maximum results
--verbose, -v     Verbose output
```

## Best Practices

1. **Use App Passwords**: Never use main password; create app-specific passwords
2. **Dry Run First**: Always use `--dry-run` before bulk operations
3. **Export Before Delete**: Backup data before any cleanup
4. **Respect Rate Limits**: Scripts handle this, but be patient with bulk ops
5. **Cache Smartly**: Enable caching for repeated profile lookups

## Integration

### Python Usage
```python
from atproto import Client

client = Client()
client.login('handle.bsky.social', 'app-password')

# Create post
client.send_post('Hello from Python!')

# Get profile
profile = client.get_profile('alice.bsky.social')
print(f"{profile.display_name}: {profile.description}")
```

### With Swarm Agent
```bash
# Bluesky tools available in swarm
python agent.py --tools bluesky

> Post about today's weather
[Invokes bluesky post tool]
```

## Troubleshooting

**"Invalid handle"**: Use format `handle.bsky.social` (not @handle)

**"Authentication failed"**: Check app password, not main password

**"Rate limited"**: Wait 5 minutes, or reduce request frequency

**"Post not found"**: Verify AT URI format is correct

**"CAR download failed"**: PDS may be temporarily unavailable

## Resources

- AT Protocol Documentation: https://atproto.com/docs
- Bluesky API: https://docs.bsky.app
- atproto Python SDK: https://github.com/MarshalX/atproto
