import os
import time
import logging
import requests
from pathlib import Path

logger = logging.getLogger(__name__)

TIKTOK_API_BASE = "https://open.tiktokapis.com/v2"


class TikTokUploader:
    """
    Uses TikTok Content Posting API v2.
    Apply for access at: https://developers.tiktok.com/products/content-posting-api/
    """

    def __init__(self, config):
        self.config = config
        self.access_token = config.TIKTOK_ACCESS_TOKEN

    def upload(self, video_path: str, script_data: dict, niche) -> dict:
        """Upload video to TikTok. Returns dict with video_id and url."""
        if not self.access_token:
            raise ValueError("TIKTOK_ACCESS_TOKEN not set in .env")

        caption = self._build_caption(script_data, niche)
        file_size = os.path.getsize(video_path)

        # Step 1: Initialize upload
        logger.info("Initialising TikTok upload …")
        init_resp = self._init_upload(file_size, caption)
        upload_url = init_resp["data"]["upload_url"]
        publish_id = init_resp["data"]["publish_id"]

        # Step 2: Upload video file
        logger.info("Uploading video bytes to TikTok …")
        self._upload_file(upload_url, video_path, file_size)

        # Step 3: Poll for publish status
        logger.info("Waiting for TikTok to process video …")
        result = self._poll_status(publish_id)
        return result

    # ── Internal ──────────────────────────────────────────────────────────────

    def _headers(self) -> dict:
        return {
            "Authorization": f"Bearer {self.access_token}",
            "Content-Type": "application/json; charset=UTF-8",
        }

    def _init_upload(self, file_size: int, caption: str) -> dict:
        url = f"{TIKTOK_API_BASE}/post/publish/video/init/"
        payload = {
            "post_info": {
                "title": caption,
                "privacy_level": "PUBLIC_TO_EVERYONE",
                "disable_duet": False,
                "disable_comment": False,
                "disable_stitch": False,
            },
            "source_info": {
                "source": "FILE_UPLOAD",
                "video_size": file_size,
                "chunk_size": file_size,
                "total_chunk_count": 1,
            },
        }
        resp = requests.post(url, json=payload, headers=self._headers(), timeout=30)
        resp.raise_for_status()
        return resp.json()

    def _upload_file(self, upload_url: str, video_path: str, file_size: int):
        with open(video_path, "rb") as f:
            video_bytes = f.read()
        headers = {
            "Content-Type": "video/mp4",
            "Content-Range": f"bytes 0-{file_size - 1}/{file_size}",
            "Content-Length": str(file_size),
        }
        resp = requests.put(upload_url, data=video_bytes, headers=headers, timeout=300)
        resp.raise_for_status()

    def _poll_status(self, publish_id: str, max_attempts: int = 20) -> dict:
        url = f"{TIKTOK_API_BASE}/post/publish/status/fetch/"
        payload = {"publish_id": publish_id}
        for attempt in range(max_attempts):
            time.sleep(5)
            resp = requests.post(url, json=payload, headers=self._headers(), timeout=30)
            resp.raise_for_status()
            data = resp.json()
            status = data.get("data", {}).get("status", "")
            logger.debug("TikTok publish status [%d]: %s", attempt + 1, status)
            if status == "PUBLISH_COMPLETE":
                video_id = data["data"].get("publicaly_available_post_id", [""])[0]
                url_out = f"https://www.tiktok.com/@me/video/{video_id}" if video_id else "https://www.tiktok.com/"
                logger.info("TikTok upload complete: %s", url_out)
                return {"platform_id": video_id, "url": url_out}
            if status in ("FAILED", "PUBLISH_FAILED"):
                raise RuntimeError(f"TikTok publish failed: {data}")
        raise TimeoutError("TikTok publish timed out after polling")

    @staticmethod
    def _build_caption(script_data: dict, niche) -> str:
        title = script_data.get("title", "")
        hashtags = " ".join(
            h if h.startswith("#") else f"#{h}"
            for h in niche.tiktok_hashtags[:5]
        )
        caption = f"{title} {hashtags}"
        return caption[:2200]  # TikTok caption limit

    # ── Setup ─────────────────────────────────────────────────────────────────

    @staticmethod
    def setup_wizard():
        print("\n=== TikTok Content Posting API Setup ===")
        print("1. Go to https://developers.tiktok.com/")
        print("2. Create an app and apply for 'Content Posting API' access")
        print("3. Once approved, generate an access token via OAuth 2.0")
        print("4. Add TIKTOK_ACCESS_TOKEN to your .env file")
        print("\nNote: API approval can take 1-5 business days.")
