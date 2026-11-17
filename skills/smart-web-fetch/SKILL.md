---
name: smart-web-fetch
description: Fetch web content efficiently by checking llms.txt first, then Jina markdown endpoints, then falling back to HTML. Reduces token usage by 80% on sites that support clean markdown delivery. No external dependencies — installs a single Python script. Trigger words: fetch URL, web content, read website, scrape page, download page, get webpage, read this link.
license: MIT
metadata:
  author: sagemindai
  version: "1.0"
---

# smart-web-fetch — Token-Efficient Web Content Fetching

Fetching a webpage with the default WebFetch tool retrieves full HTML — navigation menus, footers, ads, cookie banners, and all. For a documentation page, 90% of the tokens go to chrome, not content. This script fixes that by trying cleaner sources first.

## How It Works

The fetch chain, in order:

1. **Check `llms.txt`** — Many sites publish `/llms.txt` or `/llms-full.txt` with curated content for AI agents. If present, this is the best source: intentionally structured, no noise.
2. **Try Jina markdown** — Jina's reader API serves clean markdown for millions of sites. If available, this returns structured markdown at ~20% of the HTML token cost.
3. **Fall back to HTML** — Standard fetch, with HTML stripped to readable text. Reliable but verbose.

The result: typically 60-80% fewer tokens on documentation sites, blog posts, and product pages.

---

## Installation

Copy the script into your project's scripts directory:

```bash
mkdir -p .claude/scripts
```

Then create `.claude/scripts/smart-fetch.py` with the contents below.

---

## The Script

Save this as `.claude/scripts/smart-fetch.py`:

```python
#!/usr/bin/env python3
"""
smart-fetch.py — Token-efficient web content fetching.
Tries llms.txt, then Jina markdown, then plain HTML.
Usage: python3 .claude/scripts/smart-fetch.py <url> [--raw] [--source]
"""
import sys
import urllib.request
import urllib.parse
import urllib.error
import re
import json

def fetch_url(url, timeout=15):
    req = urllib.request.Request(url, headers={
        'User-Agent': 'Mozilla/5.0 (compatible; agent-fetch/1.0)'
    })
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            charset = 'utf-8'
            ct = r.headers.get('Content-Type', '')
            if 'charset=' in ct:
                charset = ct.split('charset=')[-1].strip()
            return r.read().decode(charset, errors='replace'), r.geturl()
    except urllib.error.HTTPError as e:
        return None, str(e)
    except Exception as e:
        return None, str(e)

def html_to_text(html):
    # Remove scripts, styles, nav, footer
    for tag in ['script', 'style', 'nav', 'footer', 'header', 'aside']:
        html = re.sub(rf'<{tag}[^>]*>.*?</{tag}>', '', html, flags=re.DOTALL|re.IGNORECASE)
    # Remove all remaining tags
    text = re.sub(r'<[^>]+>', ' ', html)
    # Decode common entities
    for ent, ch in [('&amp;','&'),('&lt;','<'),('&gt;','>'),('&nbsp;',' '),('&#39;',"'"),('&quot;','"')]:
        text = text.replace(ent, ch)
    # Collapse whitespace
    text = re.sub(r'\n\s*\n\s*\n', '\n\n', text)
    text = re.sub(r'[ \t]+', ' ', text)
    return text.strip()

def get_base(url):
    p = urllib.parse.urlparse(url)
    return f"{p.scheme}://{p.netloc}"

def try_llms_txt(base):
    for path in ['/llms-full.txt', '/llms.txt']:
        content, _ = fetch_url(base + path)
        if content and len(content) > 100 and not content.strip().startswith('<'):
            return content, 'llms.txt'
    return None, None

def try_jina_markdown(url):
    jina_url = 'https://r.jina.ai/' + url
    content, final_url = fetch_url(jina_url, timeout=20)
    if content and len(content) > 200 and not content.strip().startswith('<!'):
        return content, 'markdown'
    return None, None

def smart_fetch(url, show_source=False):
    base = get_base(url)
    results = []

    # 1. Try llms.txt
    content, source = try_llms_txt(base)
    if content:
        results.append(('llms.txt', content))

    # 2. Try markdown delivery
    content, source = try_jina_markdown(url)
    if content:
        results.append(('markdown', content))

    # 3. HTML fallback
    if not results:
        html, _ = fetch_url(url)
        if html:
            text = html_to_text(html)
            results.append(('html', text))

    if not results:
        print(f"ERROR: Could not fetch {url}", file=sys.stderr)
        sys.exit(1)

    # Use best result (prefer llms.txt > markdown > html)
    best_source, best_content = results[0]

    if show_source:
        print(f"[source: {best_source}]", file=sys.stderr)

    return best_content

if __name__ == '__main__':
    args = sys.argv[1:]
    if not args or args[0] in ('-h', '--help'):
        print(__doc__)
        sys.exit(0)

    url = args[0]
    show_source = '--source' in args

    content = smart_fetch(url, show_source=show_source)
    print(content)
```

Make it executable:

```bash
chmod +x .claude/scripts/smart-fetch.py
```

---

## Usage

```bash
# Fetch a page (auto-selects best source)
python3 .claude/scripts/smart-fetch.py https://docs.example.com/guide

# Show which source was used (llms.txt / markdown / html)
python3 .claude/scripts/smart-fetch.py https://docs.example.com/guide --source

# Pipe into another tool
python3 .claude/scripts/smart-fetch.py https://example.com | head -100
```

---

## Teaching the Agent to Use It

Add this to your project's `CLAUDE.md`:

```markdown
## Web Fetching

When fetching web content, always use the smart-fetch script first:

\`\`\`bash
python3 .claude/scripts/smart-fetch.py <url> --source
\`\`\`

Only use WebFetch as a fallback if smart-fetch fails or if you need
JavaScript-rendered content. The script reduces token usage by 60-80%
on documentation sites and blogs.
```

---

## When Each Source Wins

| Site Type | Likely Source | Why |
|-----------|--------------|-----|
| AI/dev tool docs | llms.txt | Modern tools publish agent-ready content |
| Technical blogs | markdown | Clean article content via markdown delivery |
| Legacy enterprise sites | html | No markdown alternative available |
| SPAs / JS-heavy sites | html (may be sparse) | Server-side content only |

---

## Token Savings by Source

Approximate token counts for a typical 2,000-word documentation page:

- **HTML** (raw): ~8,000 tokens (navigation, scripts, markup included)
- **Markdown delivery**: ~2,000 tokens (clean structured content)
- **llms.txt**: ~1,500 tokens (curated for AI consumption)

On a project that fetches 50 URLs per session, this saves ~300,000 tokens — roughly the difference between fitting in context and not.
