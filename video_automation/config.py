import os
from dotenv import load_dotenv

load_dotenv()


class Config:
    # AI
    ANTHROPIC_API_KEY: str = os.getenv("ANTHROPIC_API_KEY", "")

    # Media
    PEXELS_API_KEY: str = os.getenv("PEXELS_API_KEY", "")

    # News
    NEWS_API_KEY: str = os.getenv("NEWS_API_KEY", "")

    # YouTube
    YOUTUBE_CLIENT_ID: str = os.getenv("YOUTUBE_CLIENT_ID", "")
    YOUTUBE_CLIENT_SECRET: str = os.getenv("YOUTUBE_CLIENT_SECRET", "")
    YOUTUBE_REFRESH_TOKEN: str = os.getenv("YOUTUBE_REFRESH_TOKEN", "")

    # TikTok
    TIKTOK_CLIENT_KEY: str = os.getenv("TIKTOK_CLIENT_KEY", "")
    TIKTOK_CLIENT_SECRET: str = os.getenv("TIKTOK_CLIENT_SECRET", "")
    TIKTOK_ACCESS_TOKEN: str = os.getenv("TIKTOK_ACCESS_TOKEN", "")

    # App
    VIDEOS_PER_DAY: int = int(os.getenv("VIDEOS_PER_DAY", "8"))
    OUTPUT_DIR: str = os.getenv("OUTPUT_DIR", "output")
    UPLOAD_TO_YOUTUBE: bool = os.getenv("UPLOAD_TO_YOUTUBE", "true").lower() == "true"
    UPLOAD_TO_TIKTOK: bool = os.getenv("UPLOAD_TO_TIKTOK", "true").lower() == "true"
    YOUTUBE_VIDEO_DURATION: int = int(os.getenv("YOUTUBE_VIDEO_DURATION", "300"))
    TIKTOK_VIDEO_DURATION: int = int(os.getenv("TIKTOK_VIDEO_DURATION", "60"))
    TTS_LANGUAGE: str = os.getenv("TTS_LANGUAGE", "en")
    LOG_LEVEL: str = os.getenv("LOG_LEVEL", "INFO")

    def validate(self) -> list[str]:
        """Return list of missing critical config keys."""
        missing = []
        if not self.ANTHROPIC_API_KEY:
            missing.append("ANTHROPIC_API_KEY")
        if self.UPLOAD_TO_YOUTUBE and not self.YOUTUBE_REFRESH_TOKEN:
            missing.append("YOUTUBE_REFRESH_TOKEN (run: python main.py setup --platform youtube)")
        if self.UPLOAD_TO_TIKTOK and not self.TIKTOK_ACCESS_TOKEN:
            missing.append("TIKTOK_ACCESS_TOKEN")
        return missing
