# Source Tier Classification Guide

Detailed criteria for classifying research sources into trust tiers.

## Tier S — 🏛️ Academic & Primary Research

**Highest trust. Primary evidence.**

### Qualifying Domains & Databases
- Google Scholar (scholar.google.com)
- Semantic Scholar (semanticscholar.org)
- OpenAlex (openalex.org)
- CORE (core.ac.uk)
- Crossref (crossref.org)
- PubMed (pubmed.ncbi.nlm.nih.gov)
- arXiv (arxiv.org) — preprints, note peer-review status

### Qualifying Criteria
- Has DOI (Digital Object Identifier)
- Published in peer-reviewed journal
- Official conference proceedings (ACM, IEEE, USENIX, etc.)
- W3C/IETF/ISO specifications and RFCs
- Language/framework official specifications (ECMAScript spec, Python PEPs, Go proposals)

### Usage Rules
- For academic/research questions: minimum 2 Tier S sources required
- Always note: peer-reviewed vs. preprint vs. technical report
- Cite as: `[Author(Year), "Title", Venue]`

---

## Tier A — 🛡️ Trusted Official Sources

**High trust. Verified institutions and major press.**

### Government & Public
- .gov, .mil domains
- International organizations: UN, WHO, OECD, World Bank
- .org domains from established public institutions
- National statistics offices

### Academic Institutions
- .edu domains
- University research labs with named researchers
- Established research institutes (MIT CSAIL, Stanford HAI, etc.)

### Major Press & Wire Services
- Wire: Reuters, AP, AFP
- Broadcast: BBC, NPR, PBS
- Print: NYT, WSJ, The Economist, Financial Times
- Tech: Ars Technica, The Verge (news reporting, not opinion)
- Korean: 연합뉴스, KBS, MBC, SBS, 조선/중앙/동아 (뉴스 기사만)

### Official Documentation
- Product/framework official docs (docs.python.org, react.dev, etc.)
- Company engineering blogs from established orgs (Google AI Blog, Meta Engineering, Netflix Tech Blog)
- Official benchmarks from neutral parties (TechEmpower, Benchmarks Game)

### Usage Rules
- Treat as reliable but verify extraordinary claims
- Company blogs about their OWN products = potential bias → note it

---

## Tier B — ⚠️ Caution Required

**Medium trust. Useful but may contain bias, opinion, or unverified claims.**

### Social Media
- Twitter/X, Reddit, Mastodon, Threads
- Facebook, Instagram, LinkedIn posts
- YouTube (non-official channels)

### Open Forums & Community
- StackOverflow (especially non-accepted answers)
- Quora, HackerNews comments
- Discord, Slack community messages
- DC Inside, Reddit discussions

### Wikis
- Wikipedia — useful for overview, but verify specific claims
- NamuWiki (나무위키) — community-edited, frequently inaccurate
- Fandom wikis

### Personal Content
- Personal blogs (Tistory, Medium, dev.to, Hashnode)
- Personal YouTube channels
- Individual GitHub READMEs (non-official projects)

### Usage Rules
- **Always flag** to user with ⚠️ marker
- **Never cite alone** — must be corroborated by Tier S or A source
- Useful for: developer experience reports, community sentiment, edge cases
- Note: StackOverflow ACCEPTED answers with high votes = borderline Tier A

---

## Tier C — General

**No special trust label. Default category.**

### What Belongs Here
- General corporate websites
- Marketing materials
- Press releases (company-issued)
- SEO-optimized content sites
- News aggregators
- Generic "how-to" sites

### Usage Rules
- No icon marker in output
- Use only when better sources unavailable
- Never use as sole evidence for factual claims

---

## Special Cases

### Company's Own Content About Their Product
- Official docs → Tier A
- Company blog announcing features → Tier A (for feature existence), Tier B (for performance claims)
- Marketing pages → Tier C
- Example: "Bun is 3x faster" on bun.sh → Tier B (biased source for performance claims)

### GitHub
- Official repos (e.g., facebook/react) → Tier A
- Issues/Discussions with reproduction → Tier A (for bug existence)
- Random user repos → Tier B
- GitHub Stars/trending → Tier C (popularity ≠ quality)

### Benchmarks
- Independent, reproducible, methodology disclosed → Tier S
- Official benchmarks by neutral party → Tier A
- Vendor's own benchmarks → Tier B (always note bias)
- Undisclosed methodology → Tier C
