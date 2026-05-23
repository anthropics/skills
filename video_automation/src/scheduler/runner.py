import logging
import random
import time
from datetime import datetime

from apscheduler.schedulers.blocking import BlockingScheduler
from apscheduler.triggers.cron import CronTrigger

from config import Config
from src.database.manager import DatabaseManager
from src.niches.manager import NicheManager
from src.content.collector import DataCollector
from src.content.generator import ContentGenerator
from src.video.creator import VideoCreator
from src.upload.youtube import YouTubeUploader
from src.upload.tiktok import TikTokUploader

logger = logging.getLogger(__name__)


class VideoRunner:
    """Orchestrates the end-to-end pipeline for one video."""

    def __init__(self, config: Config):
        self.config = config
        self.db = DatabaseManager()
        self.collector = DataCollector(config)
        self.generator = ContentGenerator(config)
        self.creator = VideoCreator(config)
        self.yt = YouTubeUploader(config) if config.UPLOAD_TO_YOUTUBE else None
        self.tt = TikTokUploader(config) if config.UPLOAD_TO_TIKTOK else None

    def run_niche(self, niche, platform: str):
        """Full pipeline: collect → generate → create → upload."""
        niche_name = niche.name
        logger.info("▶  Starting pipeline: niche=%s platform=%s", niche_name, platform)

        # Collect data
        try:
            data = self.collector.collect(niche)
        except Exception as exc:
            logger.error("Collection failed for %s: %s", niche_name, exc)
            return False

        # Generate script
        try:
            script = self.generator.generate(data, niche, platform)
        except Exception as exc:
            logger.error("Script generation failed for %s: %s", niche_name, exc)
            return False

        # Create video
        try:
            video_path = self.creator.create_video(script, niche_name, platform)
        except Exception as exc:
            logger.error("Video creation failed for %s: %s", niche_name, exc)
            return False

        if not video_path:
            logger.error("Video creation returned None for %s", niche_name)
            return False

        # Save to DB
        video_id = self.db.save_video(
            niche=niche_name,
            platform=platform,
            title=script.get("title", ""),
            description=script.get("description", ""),
            tags=script.get("tags", []),
            file_path=video_path,
            metadata={"thumbnail_text": script.get("thumbnail_text", "")},
        )

        # Upload
        self._upload(video_id, video_path, script, niche, platform)

        logger.info("✓  Pipeline complete: niche=%s platform=%s", niche_name, platform)
        return True

    def _upload(self, video_id: int, video_path: str, script: dict, niche, platform: str):
        uploader = self.yt if platform == "youtube" else self.tt
        if not uploader:
            logger.info("Upload disabled for %s", platform)
            return

        try:
            result = uploader.upload(video_path, script, niche)
            self.db.save_upload(
                video_id=video_id,
                platform=platform,
                platform_id=result.get("platform_id", ""),
                url=result.get("url", ""),
                status="success",
            )
            logger.info("Uploaded to %s: %s", platform, result.get("url", ""))
        except Exception as exc:
            logger.error("Upload to %s failed: %s", platform, exc)
            self.db.save_upload(video_id=video_id, platform=platform, status="error", error=str(exc))


class DailyScheduler:
    """Schedule N videos per day spread evenly across the day."""

    def __init__(self, config: Config):
        self.config = config
        self.runner = VideoRunner(config)
        self.niche_mgr = NicheManager()
        self.db = DatabaseManager()
        self.scheduler = BlockingScheduler(timezone="UTC")

    def start(self):
        logger.info("Scheduler starting — %d videos/day target", self.config.VIDEOS_PER_DAY)
        self._schedule_jobs()

        # Run one batch immediately on startup
        logger.info("Running initial batch on startup …")
        self._run_batch()

        logger.info("Scheduler running. Press Ctrl+C to stop.")
        self.scheduler.start()

    def _schedule_jobs(self):
        """Create N evenly-spaced jobs throughout the day."""
        n = self.config.VIDEOS_PER_DAY
        interval_minutes = (23 * 60) // max(n, 1)

        for i in range(n):
            hour = (i * interval_minutes) // 60
            minute = (i * interval_minutes) % 60
            self.scheduler.add_job(
                self._run_batch,
                CronTrigger(hour=hour, minute=minute),
                id=f"batch_{i}",
                replace_existing=True,
            )
            logger.info("Scheduled batch %d at %02d:%02d UTC", i + 1, hour, minute)

    def _run_batch(self):
        """Pick one niche/platform combo and run the pipeline."""
        today_count = self.db.videos_created_today()
        if today_count >= self.config.VIDEOS_PER_DAY:
            logger.info("Daily quota reached (%d videos). Skipping.", today_count)
            return

        # Alternate platforms and rotate niches
        platform = "youtube" if today_count % 2 == 0 else "tiktok"
        niches = self.niche_mgr.for_platform(platform)
        if not niches:
            niches = self.niche_mgr.get_all()
            platform = "youtube"

        niche = niches[today_count % len(niches)]
        logger.info("Batch job: niche=%s platform=%s (video %d today)", niche.name, platform, today_count + 1)
        self.runner.run_niche(niche, platform)
