import logging
import re
import time
import requests
import random
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta

try:
    import feedparser as _feedparser
    _HAS_FEEDPARSER = True
except Exception:
    _feedparser = None
    _HAS_FEEDPARSER = False

logger = logging.getLogger(__name__)

REDDIT_HEADERS = {"User-Agent": "VideoAutomationBot/1.0"}

# Fallback content when all external APIs are unreachable
FALLBACK_CONTENT: dict[str, dict] = {
    "tech": {
        "topics": [
            "AI chips are reshaping personal computing in 2025",
            "Open-source models now rival GPT-4 in benchmarks",
            "Quantum computing breaks 1,000-qubit barrier",
            "Foldable phones hit mainstream pricing below $500",
            "USB-C universal standard finally ships on all devices",
        ],
        "facts": [
            "The average smartphone now has more compute than a 2010 supercomputer",
            "Over 90% of new enterprise software is AI-assisted",
            "Solid-state batteries promise 50% more EV range by 2026",
        ],
    },
    "finance": {
        "topics": [
            "S&P 500 hits new all-time high as inflation cools",
            "High-yield savings accounts still beating market averages",
            "Bitcoin ETFs attract record institutional inflows",
            "Real estate crowdfunding opens doors for retail investors",
            "Index funds outperform 92% of active managers over 10 years",
        ],
        "facts": [
            "Compound interest on $500/month from age 25 yields $1.6M at 65",
            "Only 16% of Americans have a 3-month emergency fund",
            "The average millionaire has 7 streams of income",
        ],
    },
    "motivation": {
        "topics": [
            "Why 5 AM routines are adopted by top CEOs worldwide",
            "The science of habit stacking for productivity",
            "Micro-habits: small changes creating massive results",
            "How stoic philosophy drives modern elite performance",
            "The 1% improvement rule that transforms careers",
        ],
        "facts": [
            "It takes 66 days on average to form a new habit",
            "People who write down goals are 42% more likely to achieve them",
            "A 1% daily improvement leads to 37x improvement in a year",
        ],
    },
    "health": {
        "topics": [
            "Zone 2 cardio: the longevity exercise everyone is missing",
            "Cold plunge therapy backed by new clinical trials",
            "Sleep quality linked directly to Alzheimer's risk",
            "Time-restricted eating shows metabolic benefits",
            "Strength training after 40 reverses biological age",
        ],
        "facts": [
            "7-8 hours of sleep reduces heart disease risk by 34%",
            "Walking 8,000 steps a day cuts all-cause mortality by 51%",
            "Protein intake of 1g per lb of bodyweight preserves muscle mass",
        ],
    },
    "ai": {
        "topics": [
            "Claude and GPT-4o enter multimodal reasoning era",
            "AI agents autonomously complete week-long coding projects",
            "Text-to-video AI creates broadcast-quality content",
            "AI tutors close learning gaps in underserved schools",
            "Autonomous vehicles reach Level 4 in major US cities",
        ],
        "facts": [
            "AI is expected to automate 30% of tasks in 60% of jobs by 2030",
            "LLMs can now write code better than 90% of human developers on benchmarks",
            "AI drug discovery cut time-to-candidate from 5 years to 18 months",
        ],
    },
    "science": {
        "topics": [
            "James Webb discovers galaxies older than current universe models",
            "CRISPR therapy cures first hereditary blindness patients",
            "Dark matter detector records possible first direct signal",
            "Scientists reverse aging by 20 years in mouse study",
            "Nuclear fusion reactor sustains plasma for 30 minutes",
        ],
        "facts": [
            "There are more stars in the universe than grains of sand on Earth",
            "The human brain contains 86 billion neurons with 100 trillion connections",
            "Octopuses have three hearts and blue blood",
        ],
    },
    "history": {
        "topics": [
            "Lost Roman city found perfectly preserved under Italian farmland",
            "Ancient Egyptian papyri reveal unknown surgical techniques",
            "Medieval climate change contributed to Black Death spread",
            "Genetic study reveals true origins of Indo-European languages",
            "Sunken 2,000-year-old Greek computer decoded after 80 years",
        ],
        "facts": [
            "Cleopatra lived closer in time to the Moon landing than to pyramid construction",
            "The Roman Empire lasted for over 1,000 years if you count Byzantium",
            "Oxford University is older than the Aztec Empire",
        ],
    },
    "news": {
        "topics": [
            "G7 leaders agree on new global AI governance framework",
            "Renewable energy surpasses fossil fuels in electricity generation",
            "Global life expectancy rebounds to pre-pandemic levels",
            "Electric vehicle sales cross 20% of all new cars worldwide",
            "Antarctic ice shelf shows signs of recovery after decade of loss",
        ],
        "facts": [
            "Solar power costs have fallen 90% in the last 10 years",
            "Global internet penetration now exceeds 65% of world population",
            "Literacy rates worldwide have risen from 12% in 1820 to 87% today",
        ],
    },
}


class DataCollector:
    def __init__(self, config):
        self.config = config
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": "VideoAutomationBot/1.0"})

    # ── Public interface ─────────────────────────────────────────────────────

    def collect(self, niche) -> dict:
        """Return a dict with trending_topics and raw_facts for a niche."""
        topics: list[str] = []
        facts: list[str] = []

        # RSS feeds
        rss_items = self._collect_rss(niche.rss_feeds)
        topics.extend([item["title"] for item in rss_items[:5]])
        facts.extend([item["summary"] for item in rss_items[:5] if item.get("summary")])

        # Reddit hot posts
        reddit_items = self._collect_reddit(niche.subreddits)
        topics.extend([r["title"] for r in reddit_items[:5]])

        # NewsAPI (if key set)
        if self.config.NEWS_API_KEY:
            news_items = self._collect_news(niche.keywords[0])
            topics.extend([n["title"] for n in news_items[:5]])
            facts.extend([n["description"] for n in news_items[:3] if n.get("description")])

        # Deduplicate
        seen: set[str] = set()
        unique_topics: list[str] = []
        for t in topics:
            if t and t not in seen:
                seen.add(t)
                unique_topics.append(t)

        # Fall back to curated content if nothing was collected
        if not unique_topics:
            logger.info("External APIs unavailable — using curated fallback content for '%s'", niche.name)
            fallback = FALLBACK_CONTENT.get(niche.name, FALLBACK_CONTENT.get("tech", {}))
            unique_topics = fallback.get("topics", [])
            facts = fallback.get("facts", [])

        return {
            "topics": unique_topics[:10],
            "facts": [f for f in facts if f][:8],
            "keywords": niche.keywords,
            "niche_name": niche.display_name,
        }

    # ── Sources ──────────────────────────────────────────────────────────────

    def _collect_rss(self, feed_urls: list[str]) -> list[dict]:
        items: list[dict] = []
        for url in feed_urls:
            try:
                if _HAS_FEEDPARSER:
                    feed = _feedparser.parse(url)
                    for entry in feed.entries[:5]:
                        summary = getattr(entry, "summary", "") or ""
                        summary = re.sub(r"<[^>]+>", " ", summary).strip()[:300]
                        items.append({
                            "title": entry.get("title", "").strip(),
                            "summary": summary,
                            "link": entry.get("link", ""),
                        })
                else:
                    items.extend(self._parse_rss_xml(url))
            except Exception as exc:
                logger.debug("RSS fetch failed %s: %s", url, exc)
        return items

    def _parse_rss_xml(self, url: str) -> list[dict]:
        """Minimal RSS parser using stdlib xml — works on Python 3.11+."""
        items: list[dict] = []
        try:
            resp = self.session.get(url, timeout=10)
            resp.raise_for_status()
            root = ET.fromstring(resp.content)
            ns = {"atom": "http://www.w3.org/2005/Atom"}
            # Support both RSS 2.0 and Atom
            entries = root.findall(".//item") or root.findall(".//atom:entry", ns)
            for entry in entries[:5]:
                title = (
                    (entry.findtext("title") or entry.findtext("atom:title", namespaces=ns) or "").strip()
                )
                summary = (
                    entry.findtext("description")
                    or entry.findtext("atom:summary", namespaces=ns)
                    or ""
                ).strip()
                summary = re.sub(r"<[^>]+>", " ", summary)[:300]
                link = entry.findtext("link") or entry.findtext("atom:link", namespaces=ns) or ""
                if title:
                    items.append({"title": title, "summary": summary, "link": link})
        except Exception as exc:
            logger.debug("XML RSS parse failed %s: %s", url, exc)
        return items

    def _collect_reddit(self, subreddits: list[str]) -> list[dict]:
        items: list[dict] = []
        sub = "+".join(subreddits[:3])
        url = f"https://www.reddit.com/r/{sub}/hot.json?limit=10"
        try:
            resp = self.session.get(url, timeout=10)
            resp.raise_for_status()
            posts = resp.json()["data"]["children"]
            for post in posts:
                d = post["data"]
                if not d.get("stickied") and not d.get("over_18"):
                    items.append({
                        "title": d["title"],
                        "score": d["score"],
                        "url": d.get("url", ""),
                    })
        except Exception as exc:
            logger.debug("Reddit fetch failed: %s", exc)
        return items

    def _collect_news(self, keyword: str) -> list[dict]:
        items: list[dict] = []
        url = "https://newsapi.org/v2/everything"
        params = {
            "q": keyword,
            "sortBy": "popularity",
            "pageSize": 10,
            "language": "en",
            "from": (datetime.now() - timedelta(days=2)).strftime("%Y-%m-%d"),
            "apiKey": self.config.NEWS_API_KEY,
        }
        try:
            resp = self.session.get(url, params=params, timeout=10)
            resp.raise_for_status()
            articles = resp.json().get("articles", [])
            for art in articles:
                if art.get("title") and "[Removed]" not in art["title"]:
                    items.append({
                        "title": art["title"],
                        "description": art.get("description", ""),
                    })
        except Exception as exc:
            logger.debug("NewsAPI failed: %s", exc)
        return items

    def fetch_pexels_images(self, query: str, count: int = 5) -> list[str]:
        """Return list of image URLs from Pexels for a search query."""
        if not self.config.PEXELS_API_KEY:
            return []
        url = "https://api.pexels.com/v1/search"
        headers = {"Authorization": self.config.PEXELS_API_KEY}
        params = {"query": query, "per_page": count, "orientation": "landscape"}
        try:
            resp = requests.get(url, headers=headers, params=params, timeout=10)
            resp.raise_for_status()
            photos = resp.json().get("photos", [])
            return [p["src"]["large"] for p in photos]
        except Exception as exc:
            logger.debug("Pexels fetch failed: %s", exc)
            return []
