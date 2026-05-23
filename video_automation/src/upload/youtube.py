import os
import json
import logging
import pickle
from pathlib import Path

logger = logging.getLogger(__name__)

SCOPES = ["https://www.googleapis.com/auth/youtube.upload"]
TOKEN_FILE = "credentials/youtube_token.pickle"
CLIENT_SECRETS_FILE = "credentials/youtube_client_secrets.json"


class YouTubeUploader:
    def __init__(self, config):
        self.config = config
        self._service = None

    # ── Auth ──────────────────────────────────────────────────────────────────

    def _get_service(self):
        if self._service:
            return self._service
        try:
            from googleapiclient.discovery import build
            from google.oauth2.credentials import Credentials
            from google_auth_oauthlib.flow import InstalledAppFlow
            from google.auth.transport.requests import Request
        except ImportError:
            raise RuntimeError(
                "Google API client not installed. Run: pip install google-api-python-client google-auth-oauthlib"
            )

        creds = None

        # Load cached token
        if os.path.exists(TOKEN_FILE):
            with open(TOKEN_FILE, "rb") as f:
                creds = pickle.load(f)

        # Refresh or re-authenticate
        if not creds or not creds.valid:
            if creds and creds.expired and creds.refresh_token:
                from google.auth.transport.requests import Request
                creds.refresh(Request())
            else:
                if not os.path.exists(CLIENT_SECRETS_FILE):
                    raise FileNotFoundError(
                        f"YouTube client secrets not found at {CLIENT_SECRETS_FILE}.\n"
                        "Download from Google Cloud Console → APIs → Credentials → OAuth 2.0 Client IDs"
                    )
                flow = InstalledAppFlow.from_client_secrets_file(CLIENT_SECRETS_FILE, SCOPES)
                creds = flow.run_local_server(port=0)

            os.makedirs("credentials", exist_ok=True)
            with open(TOKEN_FILE, "wb") as f:
                pickle.dump(creds, f)

        self._service = build("youtube", "v3", credentials=creds)
        return self._service

    # ── Upload ────────────────────────────────────────────────────────────────

    def upload(self, video_path: str, script_data: dict, niche) -> dict:
        """Upload video to YouTube. Returns dict with video_id and url."""
        from googleapiclient.http import MediaFileUpload
        from googleapiclient.errors import HttpError

        service = self._get_service()

        tags = script_data.get("tags", []) + niche.youtube_hashtags
        body = {
            "snippet": {
                "title": script_data["title"],
                "description": script_data["description"],
                "tags": list(dict.fromkeys(tags))[:15],  # deduplicated, max 15
                "categoryId": niche.youtube_category_id,
                "defaultLanguage": "en",
            },
            "status": {
                "privacyStatus": "public",
                "selfDeclaredMadeForKids": False,
            },
        }

        media = MediaFileUpload(video_path, chunksize=-1, resumable=True, mimetype="video/mp4")

        logger.info("Uploading to YouTube: %s", script_data["title"])
        request = service.videos().insert(part=",".join(body.keys()), body=body, media_body=media)

        response = None
        while response is None:
            status, response = request.next_chunk()
            if status:
                pct = int(status.progress() * 100)
                logger.info("YouTube upload progress: %d%%", pct)

        video_id = response["id"]
        url = f"https://www.youtube.com/watch?v={video_id}"
        logger.info("YouTube upload complete: %s", url)
        return {"platform_id": video_id, "url": url}

    # ── OAuth setup wizard ────────────────────────────────────────────────────

    @staticmethod
    def setup_wizard():
        print("\n=== YouTube OAuth Setup ===")
        print("1. Go to https://console.cloud.google.com/")
        print("2. Create a project and enable 'YouTube Data API v3'")
        print("3. Create OAuth 2.0 credentials (Desktop app)")
        print(f"4. Download the JSON and save it as: {CLIENT_SECRETS_FILE}")
        print("5. Run this script again — a browser window will open for authentication")
        os.makedirs("credentials", exist_ok=True)
