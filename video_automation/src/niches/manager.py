from dataclasses import dataclass, field


@dataclass
class Niche:
    name: str
    display_name: str
    keywords: list[str]
    subreddits: list[str]
    rss_feeds: list[str]
    youtube_category_id: str  # YouTube category ID
    tiktok_hashtags: list[str]
    youtube_hashtags: list[str]
    color_scheme: str          # key into VideoCreator.NICHE_COLORS
    platforms: list[str]       # ['youtube', 'tiktok'] or subset
    youtube_duration: int      # seconds
    tiktok_duration: int       # seconds


NICHES: list[Niche] = [
    Niche(
        name="tech",
        display_name="Technology",
        keywords=["technology", "gadgets", "software", "programming", "AI", "smartphone"],
        subreddits=["technology", "gadgets", "programming", "MachineLearning"],
        rss_feeds=[
            "https://feeds.feedburner.com/TechCrunch",
            "https://www.theverge.com/rss/index.xml",
            "https://feeds.arstechnica.com/arstechnica/index",
        ],
        youtube_category_id="28",
        tiktok_hashtags=["#tech", "#technology", "#gadgets", "#coding", "#programming"],
        youtube_hashtags=["technology", "tech", "gadgets", "programming", "software"],
        color_scheme="tech",
        platforms=["youtube", "tiktok"],
        youtube_duration=300,
        tiktok_duration=60,
    ),
    Niche(
        name="finance",
        display_name="Finance & Money",
        keywords=["investing", "stock market", "personal finance", "crypto", "money tips"],
        subreddits=["personalfinance", "investing", "stocks", "CryptoCurrency"],
        rss_feeds=[
            "https://feeds.a.dj.com/rss/RSSMarketsMain.xml",
            "https://finance.yahoo.com/rss/",
        ],
        youtube_category_id="22",
        tiktok_hashtags=["#finance", "#investing", "#money", "#stocks", "#personalfinance"],
        youtube_hashtags=["finance", "investing", "money", "stocks", "personalfinance"],
        color_scheme="finance",
        platforms=["youtube", "tiktok"],
        youtube_duration=360,
        tiktok_duration=60,
    ),
    Niche(
        name="motivation",
        display_name="Motivation & Success",
        keywords=["motivation", "success", "mindset", "productivity", "self improvement"],
        subreddits=["GetMotivated", "selfimprovement", "productivity", "DecidingToBeBetter"],
        rss_feeds=[
            "https://feeds.feedburner.com/JamesClear",
        ],
        youtube_category_id="22",
        tiktok_hashtags=["#motivation", "#success", "#mindset", "#selfimprovement", "#productivity"],
        youtube_hashtags=["motivation", "success", "mindset", "selfimprovement", "productivity"],
        color_scheme="motivation",
        platforms=["youtube", "tiktok"],
        youtube_duration=240,
        tiktok_duration=60,
    ),
    Niche(
        name="health",
        display_name="Health & Fitness",
        keywords=["fitness", "health tips", "nutrition", "workout", "wellness"],
        subreddits=["Fitness", "nutrition", "loseit", "running", "bodyweightfitness"],
        rss_feeds=[
            "https://www.healthline.com/rss/health-news",
        ],
        youtube_category_id="26",
        tiktok_hashtags=["#health", "#fitness", "#workout", "#nutrition", "#wellness"],
        youtube_hashtags=["health", "fitness", "workout", "nutrition", "wellness"],
        color_scheme="health",
        platforms=["youtube", "tiktok"],
        youtube_duration=300,
        tiktok_duration=60,
    ),
    Niche(
        name="ai",
        display_name="Artificial Intelligence",
        keywords=["artificial intelligence", "machine learning", "ChatGPT", "deep learning", "AI tools"],
        subreddits=["artificial", "MachineLearning", "ChatGPT", "OpenAI"],
        rss_feeds=[
            "https://openai.com/blog/rss/",
            "https://feeds.feedburner.com/AITrends",
        ],
        youtube_category_id="28",
        tiktok_hashtags=["#AI", "#artificialintelligence", "#ChatGPT", "#machinelearning", "#tech"],
        youtube_hashtags=["AI", "artificialintelligence", "ChatGPT", "machinelearning", "deeplearning"],
        color_scheme="ai",
        platforms=["youtube", "tiktok"],
        youtube_duration=300,
        tiktok_duration=60,
    ),
    Niche(
        name="science",
        display_name="Science Facts",
        keywords=["science", "space", "physics", "biology", "discoveries"],
        subreddits=["science", "space", "Physics", "biology", "EverythingScience"],
        rss_feeds=[
            "https://www.sciencedaily.com/rss/all.xml",
            "https://feeds.bbci.co.uk/news/science_and_environment/rss.xml",
        ],
        youtube_category_id="28",
        tiktok_hashtags=["#science", "#space", "#facts", "#physics", "#didyouknow"],
        youtube_hashtags=["science", "space", "physics", "facts", "discovery"],
        color_scheme="science",
        platforms=["youtube", "tiktok"],
        youtube_duration=300,
        tiktok_duration=60,
    ),
    Niche(
        name="history",
        display_name="History Facts",
        keywords=["history", "ancient civilizations", "historical events", "world war", "famous people"],
        subreddits=["history", "AskHistorians", "HistoryMemes", "ancienthistory"],
        rss_feeds=[
            "https://feeds.bbci.co.uk/news/rss.xml",
        ],
        youtube_category_id="27",
        tiktok_hashtags=["#history", "#historyfacts", "#didyouknow", "#historytok", "#facts"],
        youtube_hashtags=["history", "historyfacts", "ancienthistory", "worldhistory", "facts"],
        color_scheme="history",
        platforms=["youtube", "tiktok"],
        youtube_duration=360,
        tiktok_duration=60,
    ),
    Niche(
        name="news",
        display_name="World News",
        keywords=["breaking news", "world news", "current events", "politics", "economy"],
        subreddits=["worldnews", "news", "politics", "Economics"],
        rss_feeds=[
            "https://feeds.bbci.co.uk/news/world/rss.xml",
            "https://rss.cnn.com/rss/edition.rss",
        ],
        youtube_category_id="25",
        tiktok_hashtags=["#news", "#worldnews", "#breakingnews", "#currentevents", "#today"],
        youtube_hashtags=["news", "worldnews", "breakingnews", "currentevents", "today"],
        color_scheme="news",
        platforms=["youtube", "tiktok"],
        youtube_duration=240,
        tiktok_duration=60,
    ),
]


class NicheManager:
    def __init__(self, active_names: list[str] | None = None):
        if active_names:
            self._niches = [n for n in NICHES if n.name in active_names]
        else:
            self._niches = list(NICHES)

    def get_all(self) -> list[Niche]:
        return self._niches

    def get(self, name: str) -> Niche | None:
        return next((n for n in self._niches if n.name == name), None)

    def names(self) -> list[str]:
        return [n.name for n in self._niches]

    def for_platform(self, platform: str) -> list[Niche]:
        return [n for n in self._niches if platform in n.platforms]
