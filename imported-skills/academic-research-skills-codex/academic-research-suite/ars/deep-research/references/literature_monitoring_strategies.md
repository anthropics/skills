# Literature Monitoring Strategies — Reference Guide

## Purpose

Comprehensive reference for setting up post-research literature monitoring across major academic databases and platforms. Used by the `monitoring_agent` to configure monitoring strategies tailored to the user's research field and publication velocity.

---

## 1. Google Scholar Alerts

### Setup

1. Go to [Google Scholar](https://scholar.google.com)
2. Enter your search query (use the same keywords from your systematic search)
3. Click the envelope icon (📧) in the left sidebar, or go to scholar.google.com/scholar_alerts
4. Set email address and frequency

### Best Practices

- Create separate alerts for each major keyword cluster (not one giant query)
- Use quotes for exact phrases: `"quality assurance" "higher education"`
- Use OR for synonyms: `"quality assurance" OR "quality evaluation"`
- Limit to 10-15 active alerts to avoid email overload
- Review alerts monthly and deactivate stale ones

### Limitations

- No Boolean NOT support in alerts
- Cannot filter by date, journal, or document type
- May include non-peer-reviewed sources (theses, reports, patents)
- Coverage varies by discipline (strong in STEM, weaker in humanities)

---

## 2. PubMed Email Alerts

### Setup

1. Go to [PubMed](https://pubmed.ncbi.nlm.nih.gov)
2. Run your search using MeSH terms and filters
3. Click "Save" below the search box
4. Log in to My NCBI account (free)
5. Set email alert frequency: daily, weekly, or monthly

### Best Practices

- Use MeSH terms for precise matching (e.g., `"Quality Assurance, Health Care"[MeSH]`)
- Combine with free-text search for newer terms not yet in MeSH
- Set weekly frequency for active research areas, monthly for stable fields
- Use the "Sort by: Most Recent" option to prioritize new publications
- Save your search strategy for reproducibility

### Advanced Features

- **MyNCBI Collections**: Organize saved articles into folders
- **Filters**: Limit by date, article type, language, species
- **RSS feed**: Available for any saved search (click RSS icon)

### Limitations

- Biomedical focus — limited coverage of social sciences, education, humanities
- Indexing lag: 1-4 weeks for new articles to appear
- No citation tracking built in

---

## 3. RSS Feeds for Major Databases

### What is RSS?

RSS (Really Simple Syndication) allows you to subscribe to content updates from websites without checking each site manually. Use an RSS reader (e.g., Feedly, Inoreader, NewsBlur) to aggregate feeds.

### Recommended Feeds

| Source | Feed URL Pattern | Content |
|--------|-----------------|---------|
| **PubMed** | Saved search → RSS icon | New articles matching your search |
| **arXiv** | `arxiv.org/rss/[category]` (e.g., `cs.AI`, `cs.CL`) | Preprints by category |
| **bioRxiv** | `connect.biorxiv.org/biorxiv_xml.php?subject=[subject]` | Biology preprints |
| **medRxiv** | `connect.medrxiv.org/medrxiv_xml.php?subject=[subject]` | Medical preprints |
| **SSRN** | Subscribe to specific research networks | Social science preprints |
| **Journal TOC** | Most journals offer RSS on their homepage | New issues of specific journals |
| **Retraction Watch** | `retractionwatch.com/feed/` | Retraction news and updates |

### RSS Reader Recommendations

| Reader | Platform | Cost | Best For |
|--------|----------|------|----------|
| **Feedly** | Web, iOS, Android | Free (basic) / $6/mo (Pro) | Organized categorization, AI features |
| **Inoreader** | Web, iOS, Android | Free (basic) / $5/mo (Pro) | Power users, rules/filters |
| **NewsBlur** | Web, iOS, Android | Free (limited) / $36/yr | Open source option |
| **Zotero RSS** | Desktop | Free | Integrates with reference manager |

---

## 4. Retraction Watch Integration

### Retraction Watch Database

- **URL**: [retractiondatabase.org](http://retractiondatabase.org)
- **Coverage**: 40,000+ retracted or corrected papers
- **Searchable by**: author, journal, subject, reason, date

### Monitoring Workflow

1. **Baseline check**: Search all cited authors and paper titles in the Retraction Watch Database
2. **Ongoing monitoring**: Subscribe to Retraction Watch blog RSS feed
3. **Periodic re-check**: Every 3-6 months, re-run the baseline check for cited sources

### Retraction Reasons to Watch For

| Reason | Severity | Action Required |
|--------|----------|-----------------|
| Data fabrication/falsification | Critical | Remove citation; add note explaining removal |
| Plagiarism | High | Replace with original source |
| Duplicate publication | Moderate | Keep the primary publication; remove duplicate |
| Honest error | Moderate | Check whether the error affects cited findings |
| Author dispute | Low | Usually no impact on findings |
| Publisher error | Low | Update citation to corrected version |

---

## 5. Preprint Server Monitoring

### arXiv

- **Coverage**: Physics, mathematics, computer science, statistics, quantitative biology, economics
- **Monitoring**: Subscribe to RSS feeds by category and cross-list
- **Alert service**: [arxiv-sanity](http://arxiv-sanity-lite.com/) for AI-curated recommendations
- **Update frequency**: Daily (new submissions posted ~8 PM ET)

### SSRN

- **Coverage**: Social sciences, humanities, law, economics, management
- **Monitoring**: Subscribe to eJournal alerts by research network
- **Alert service**: Email notifications for new papers in subscribed networks
- **Note**: Now owned by Elsevier; some content behind paywall

### bioRxiv / medRxiv

- **Coverage**: Biology (bioRxiv) and health sciences (medRxiv)
- **Monitoring**: RSS feeds by subject area
- **Alert service**: Email alerts for specific keywords
- **Note**: Preprints are NOT peer-reviewed — flag accordingly in digests

### Key Preprint Monitoring Rules

1. Always label preprint sources clearly: `[PREPRINT — not peer-reviewed]`
2. Check whether a preprint has been published in a peer-reviewed journal (look for "Now published in..." banner)
3. Preprints can change or be withdrawn — re-check before citing
4. Preprint findings may differ from the final published version

---

## 6. Citation Tracking

### Web of Science

1. Find your key cited papers in Web of Science
2. Click "Create Citation Alert" (requires institutional access)
3. Receive email when someone cites that paper
4. Use "Cited Reference Search" for older papers not in the database

### Scopus

1. Find your key cited papers in Scopus
2. Click "Set Citation Alert" on the document page
3. Configure email frequency
4. Also available: author alerts (track all publications by an author)

### Google Scholar

1. Find the paper on Google Scholar
2. Click "Cited by N" to see citing papers
3. Click the "Follow" button (envelope icon) on author profiles
4. Set up alerts for specific papers by quoting the exact title

### Semantic Scholar

- **URL**: [semanticscholar.org](https://www.semanticscholar.org)
- **Alerts**: Click "Alert" on any paper to track citations
- **Advantage**: AI-powered relevance ranking of citing papers
- **Research feed**: Personalized recommendations based on your library

---

## 7. Recommended Monitoring Cadence by Field

### Determining Your Field's Publication Velocity

| Indicator | High Velocity | Moderate | Low |
|-----------|--------------|----------|-----|
| Papers per month (in your niche) | > 50 | 10-50 | < 10 |
| Median time from submission to publication | < 6 months | 6-12 months | > 12 months |
| Preprint prevalence | > 50% of key papers | 10-50% | < 10% |
| Conference vs. journal dominance | Conference-first | Mixed | Journal-only |

### Cadence Recommendations

| Field | Check Frequency | Digest Period | Sunset |
|-------|----------------|---------------|--------|
| **AI/ML, NLP** | Daily (arXiv) + Weekly (journals) | Weekly | 6 months |
| **Biomedical, Clinical** | Weekly (PubMed + preprints) | Biweekly | 12 months |
| **Education Technology** | Biweekly | Monthly | 12 months |
| **Higher Education Policy** | Monthly | Quarterly | 18 months |
| **Social Sciences (general)** | Monthly | Quarterly | 18 months |
| **Law, Philosophy** | Quarterly | Semi-annually | 24 months |
| **History, Classics** | Semi-annually | Annually | 36 months |

### Sunset Policy

- **Sunset date**: The date after which active monitoring stops (topic presumed stable)
- Set based on field velocity and research currency
- After sunset: switch to annual check-ins or opportunistic monitoring
- Exception: extend monitoring if a major development occurs (e.g., retraction of key source, paradigm shift)

---

## 8. Monitoring Maintenance Checklist

Run this checklist every monitoring cycle:

- [ ] Are all alerts still active? (some platforms deactivate after inactivity)
- [ ] Are any alerts returning zero results? (keywords may need updating)
- [ ] Are any alerts returning too many results? (keywords may need narrowing)
- [ ] Has the field's terminology evolved? (add new keywords, retire old ones)
- [ ] Any new major databases or preprint servers for this field?
- [ ] Has any tracked author changed institutions? (update author tracking)
- [ ] Is the sunset date still appropriate?
- [ ] Have you checked the Retraction Watch Database recently?

---

## Quick Reference: Setting Up in 30 Minutes

1. **Google Scholar** (5 min): Create 3-5 keyword alerts matching your original search strategy
2. **PubMed** (5 min): Save your search and set weekly email alerts (if your field is indexed)
3. **RSS** (5 min): Subscribe to RSS feeds for your top 5 cited journals in Feedly or Inoreader
4. **Retraction Watch** (5 min): Run baseline check on all cited authors; subscribe to RSS feed
5. **Citation tracking** (5 min): Set up citation alerts for your 5 most-cited sources in Google Scholar or Scopus
6. **Preprints** (5 min): Subscribe to relevant arXiv/SSRN/bioRxiv categories if applicable to your field

---

## SKILL.md Extracted Content: Literature Monitoring (Optional Post-Pipeline)

After any research mode is complete, users can optionally activate the `monitoring_agent` to set up post-research literature monitoring. This is not part of the main pipeline — it is an auxiliary capability triggered on demand.

See `agents/monitoring_agent.md` for the detailed agent definition.

**Trigger**: "monitor this topic", "set up alerts", "track new publications on this"

**Capabilities**:
- Weekly/monthly monitoring digest generation
- Retraction alerts for cited sources
- Contradictory findings detection
- Key author tracking
- Keyword evolution tracking

**Input**: Completed bibliography + search strategy from any research mode
**Output**: Monitoring configuration + digest template (markdown)

**Limitation**: The monitoring agent produces configurations and templates for the user to act on. It cannot run autonomous background monitoring.
