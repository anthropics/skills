# Documentation Scraping for Skill Creation

This reference provides detailed guidance on using Skill_Seekers to automatically populate skill references from online documentation.

## Overview

When creating skills for frameworks, libraries, or tools with online documentation, manually copying and organizing content is time-consuming and error-prone. **Skill_Seekers** automates this process by:

- Scraping documentation websites
- Detecting code languages and syntax
- Categorizing content intelligently
- Extracting patterns from examples
- Supporting llms.txt for 10x faster scraping
- Handling large documentation (10K+ pages)

## When to Use Documentation Scraping

**Good use cases:**
- Framework skills (React, Vue, Django, FastAPI)
- Library documentation (pandas, NumPy, lodash)
- Game engine docs (Godot, Unity)
- API documentation with web-based references
- Tools with comprehensive online guides

**Not recommended for:**
- Company-specific internal knowledge (no public docs)
- Simple skills with minimal reference needs
- Skills focused on scripts/assets rather than documentation

## Quick Start Workflow

### 1. One-Time Setup

Clone and install Skill_Seekers:

```bash
cd ~
git clone https://github.com/yusufkaraaslan/Skill_Seekers.git
cd Skill_Seekers
pip install requests beautifulsoup4
```

### 2. Use Helper Script (Recommended)

From skill-creator directory:

```bash
python3 scripts/scrape_documentation_helper.py
```

The interactive helper will:
1. Check if Skill_Seekers is installed
2. Show available preset configurations
3. Guide you through choosing preset or custom URL
4. Generate the exact commands to run
5. Show how to copy references to your skill

### 3. Manual Scraping (Alternative)

**Using a preset config:**

```bash
cd ~/Skill_Seekers

# Scrape React documentation
python3 cli/doc_scraper.py --config configs/react.json

# Copy to your skill
cp -r output/react/references/* /path/to/your-skill/references/
```

**Custom documentation:**

```bash
cd ~/Skill_Seekers

# Scrape custom URL
python3 cli/doc_scraper.py \
  --url https://docs.yourframework.com/ \
  --name yourframework

# Copy to your skill
cp -r output/yourframework/references/* /path/to/your-skill/references/
```

## Available Preset Configurations

Skill_Seekers includes 15+ production-tested configs:

**Web Frameworks:**
- `react.json` - React documentation
- `vue.json` - Vue.js documentation
- `django.json` - Django web framework
- `fastapi.json` - FastAPI Python framework
- `laravel.json` - Laravel PHP framework
- `astro.json` - Astro web framework

**Game Engines:**
- `godot.json` - Godot game engine

**CSS & Utilities:**
- `tailwind.json` - Tailwind CSS

**DevOps:**
- `kubernetes.json` - Kubernetes
- `ansible.json` - Ansible Core

**And more...**

Each preset includes:
- Pre-tested CSS selectors for content extraction
- URL pattern filters
- Category keyword mappings
- Appropriate rate limiting

## Advanced Features

### llms.txt Support

Skill_Seekers automatically detects llms.txt files (a standard for LLM-optimized documentation):

- Checks for `llms-full.txt`, `llms.txt`, `llms-small.txt`
- 10x faster than HTML scraping (< 5 seconds vs 20-60 seconds)
- Higher quality (pre-formatted for LLMs)
- Falls back to HTML automatically if unavailable

Example sites with llms.txt:
- Hono: https://hono.dev/llms-full.txt

### Page Estimation

Before scraping, estimate page count to validate config:

```bash
cd ~/Skill_Seekers
python3 cli/estimate_pages.py configs/react.json
```

Shows:
- Total pages discovered
- Recommended max_pages setting
- Estimated scraping time
- Discovery rate

### Large Documentation

For documentation with 10K+ pages:

```bash
# Estimate first
python3 cli/estimate_pages.py configs/godot.json

# Split into focused sub-skills
python3 cli/split_config.py configs/godot.json --strategy router

# Scrape sub-skills in parallel
for config in configs/godot-*.json; do
  python3 cli/doc_scraper.py --config $config &
done
wait

# Generate router skill
python3 cli/generate_router.py configs/godot-*.json
```

### AI Enhancement

For higher quality SKILL.md generation:

```bash
# Using Claude Code Max (free, no API key needed)
python3 cli/enhance_skill_local.py output/react/

# Or using Anthropic API
export ANTHROPIC_API_KEY=sk-ant-...
python3 cli/enhance_skill.py output/react/
```

Enhancement transforms basic 75-line templates into comprehensive 500+ line guides with:
- 5-10 practical code examples
- Comprehensive quick reference
- Domain-specific key concepts
- Navigation guidance for different skill levels

## What Gets Created

After scraping, the output directory contains:

```
output/yourframework/
├── SKILL.md                    # Basic skill file
├── references/                 # Organized documentation
│   ├── index.md               # Category overview
│   ├── getting_started.md     # Beginner content
│   ├── api.md                 # API references
│   ├── guides.md              # Tutorials
│   └── ...                    # Other categories
├── scripts/                    # Empty (for your scripts)
└── assets/                     # Empty (for your assets)
```

**Smart categorization** organizes content by:
- URL patterns (3 points for match)
- Page titles (2 points for match)
- Content keywords (1 point for match)
- Threshold of 2+ for category assignment
- Falls back to "other" category

**Copy only references/** to your skill - the scraped data already has the correct structure.

## Creating Custom Configs

For frameworks without presets, create custom config:

```json
{
  "name": "myframework",
  "description": "When to use this skill",
  "base_url": "https://docs.myframework.com/",
  "selectors": {
    "main_content": "article",
    "title": "h1",
    "code_blocks": "pre code"
  },
  "url_patterns": {
    "include": ["/docs", "/guide"],
    "exclude": ["/blog", "/about"]
  },
  "categories": {
    "getting_started": ["intro", "quickstart"],
    "api": ["api", "reference"]
  },
  "rate_limit": 0.5,
  "max_pages": 500
}
```

Save to `configs/myframework.json` and use with:

```bash
python3 cli/doc_scraper.py --config configs/myframework.json
```

## Troubleshooting

### No Content Extracted

Check `selectors.main_content` in config. Common selectors:
- `article`
- `main`
- `div[role="main"]`
- `div.content`

Test selectors with BeautifulSoup:

```python
from bs4 import BeautifulSoup
import requests

url = "https://docs.example.com/page"
soup = BeautifulSoup(requests.get(url).content, 'html.parser')

print(soup.select_one('article'))
print(soup.select_one('main'))
```

### Poor Categorization

Edit `categories` in config with better keywords:

```json
{
  "categories": {
    "getting_started": ["introduction", "getting-started", "quickstart"],
    "api": ["api", "reference", "class", "function"],
    "guides": ["guide", "tutorial", "how-to"]
  }
}
```

### Rate Limiting

If getting blocked, increase `rate_limit` in config:

```json
{
  "rate_limit": 1.0  // Increase from 0.5 to 1.0 seconds
}
```

## Best Practices

1. **Start with estimation** - Run `estimate_pages.py` to validate config before full scrape
2. **Test with limited pages** - Set `"max_pages": 20` in config for initial testing
3. **Use presets when available** - Leverages battle-tested configs
4. **Review generated references** - Verify categorization makes sense for your skill
5. **Consider enhancement** - Significantly improves SKILL.md quality
6. **Check for llms.txt** - Manual check: `https://docs.site.com/llms.txt`

## Integration with Skill Creation Workflow

**Recommended workflow:**

1. **Step 1-2**: Understand skill and plan contents (standard process)
2. **Step 3**: Initialize skill with `init_skill.py`
3. **Step 4a**: Use documentation scraping to populate `references/`
   - Run `scrape_documentation_helper.py` OR
   - Manually scrape with Skill_Seekers
4. **Step 4b**: Add scripts and assets as needed
5. **Step 4c**: Update SKILL.md with instructions
6. **Step 5**: Package skill
7. **Step 6**: Iterate based on testing

## Additional Resources

- **Skill_Seekers Repository**: https://github.com/yusufkaraaslan/Skill_Seekers
- **Skill_Seekers README**: Full documentation and examples
- **llms.txt Standard**: https://llmstxt.org/ (proposed standard)
- **Available Configs**: Browse `configs/` directory in Skill_Seekers

## Support

If Skill_Seekers doesn't work for your documentation:
1. Check if site provides llms.txt
2. Try creating custom config with correct selectors
3. Open issue at https://github.com/yusufkaraaslan/Skill_Seekers/issues
4. Fall back to manual reference creation
