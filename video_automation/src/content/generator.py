import json
import logging
import anthropic

logger = logging.getLogger(__name__)

YOUTUBE_SYSTEM = """You are an expert YouTube content creator who produces highly engaging,
educational videos. You create clear, well-structured scripts that keep viewers hooked from
start to finish. Your style is informative yet conversational."""

TIKTOK_SYSTEM = """You are an expert TikTok content creator who makes punchy, fast-paced,
viral short-form videos. Your scripts are hook-driven, energetic, and end with a strong CTA.
Every second counts."""

YOUTUBE_PROMPT = """\
Based on the following trending data for the "{niche}" niche, create a complete YouTube video script.

TRENDING TOPICS:
{topics}

FACTS / DATA:
{facts}

Target duration: ~{duration} seconds of spoken narration.

Return ONLY valid JSON with this structure:
{{
  "title": "Compelling YouTube title (max 60 chars)",
  "description": "SEO-optimised description (150-200 words, include keywords naturally)",
  "tags": ["tag1", "tag2", ... up to 15 tags],
  "narration": "Full word-for-word narration script the TTS will read aloud",
  "slides": [
    {{"title": "Slide heading", "content": "Key point shown on screen (max 2 sentences)"}},
    ...
  ],
  "thumbnail_text": "Short punchy text for thumbnail (max 5 words)"
}}

Rules:
- narration must be natural spoken English (no symbols, no markdown)
- slides array must have 6-10 items matching the narration structure
- title must be click-worthy but NOT clickbait
"""

TIKTOK_PROMPT = """\
Based on the following trending data for the "{niche}" niche, create a TikTok short video script.

TRENDING TOPICS:
{topics}

FACTS / DATA:
{facts}

Target duration: ~{duration} seconds of spoken narration.

Return ONLY valid JSON with this structure:
{{
  "title": "Catchy TikTok caption (max 80 chars with emojis)",
  "description": "TikTok caption with hashtags (max 150 chars)",
  "tags": ["hashtag1", "hashtag2", ... up to 10 hashtags without #],
  "narration": "Hook + main content + CTA script. Fast-paced, conversational.",
  "slides": [
    {{"title": "Hook line", "content": "Opening hook shown on screen"}},
    {{"title": "Main point", "content": "Key content text"}},
    {{"title": "CTA", "content": "Follow for more!"}}
  ],
  "thumbnail_text": "Hook text (max 4 words)"
}}

Rules:
- First slide must be a strong hook question or shocking fact
- narration must start with the hook immediately — no intro padding
- Last slide must have a clear CTA
- Keep sentences short and punchy
"""


class ContentGenerator:
    def __init__(self, config):
        self.client = anthropic.Anthropic(api_key=config.ANTHROPIC_API_KEY)
        self.config = config

    def generate(self, collected_data: dict, niche, platform: str = "youtube") -> dict:
        topics_text = "\n".join(f"• {t}" for t in collected_data["topics"][:6])
        facts_text = "\n".join(f"• {f}" for f in collected_data["facts"][:5])

        if platform == "youtube":
            duration = niche.youtube_duration
            system = YOUTUBE_SYSTEM
            prompt = YOUTUBE_PROMPT.format(
                niche=niche.display_name,
                topics=topics_text,
                facts=facts_text,
                duration=duration,
            )
        else:
            duration = niche.tiktok_duration
            system = TIKTOK_SYSTEM
            prompt = TIKTOK_PROMPT.format(
                niche=niche.display_name,
                topics=topics_text,
                facts=facts_text,
                duration=duration,
            )

        logger.info("Generating %s script for niche=%s", platform, niche.name)

        response = self.client.messages.create(
            model="claude-opus-4-7",
            max_tokens=4096,
            system=system,
            messages=[{"role": "user", "content": prompt}],
        )

        raw = response.content[0].text.strip()

        # Strip code fences if present
        if raw.startswith("```"):
            raw = raw.split("```", 2)[1]
            if raw.startswith("json"):
                raw = raw[4:]
            raw = raw.rsplit("```", 1)[0].strip()

        script = json.loads(raw)

        # Augment with niche hashtags
        platform_tags = niche.youtube_hashtags if platform == "youtube" else [
            h.lstrip("#") for h in niche.tiktok_hashtags
        ]
        existing = set(script.get("tags", []))
        for tag in platform_tags:
            if tag not in existing:
                script["tags"].append(tag)

        script["platform"] = platform
        script["niche"] = niche.name
        return script
