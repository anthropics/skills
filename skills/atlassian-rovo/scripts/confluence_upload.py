"""Confluence image/attachment upload via REST API v1.

The Atlassian MCP server does NOT have an attachment upload tool.
This module provides upload, embed, and page update functionality
using Basic Auth (email + API token).

Usage:
    from confluence_upload import ConfluenceUploader, image_tag

    uploader = ConfluenceUploader(base_url, email, api_token)
    uploader.upload_attachment(page_id, "/path/to/chart.png")

    tag = image_tag("chart.png", width=700)
    page = uploader.get_page(page_id)
    body = page["body"]["storage"]["value"] + tag
    uploader.update_page_body(page_id, page["title"], body, page["version"]["number"] + 1)
"""

import os
import requests


class ConfluenceUploader:
    def __init__(self, base_url, email, api_token):
        self.base_url = base_url.rstrip("/")
        self.auth = (email, api_token)

    def upload_attachment(self, page_id, file_path):
        url = f"{self.base_url}/wiki/rest/api/content/{page_id}/child/attachment"
        headers = {"X-Atlassian-Token": "nocheck"}
        with open(file_path, "rb") as f:
            files = {"file": (os.path.basename(file_path), f)}
            data = {"minorEdit": "true"}
            resp = requests.put(url, auth=self.auth, headers=headers, files=files, data=data)
        resp.raise_for_status()
        result = resp.json()
        return result["results"][0] if "results" in result else result

    def get_page(self, page_id):
        url = f"{self.base_url}/wiki/rest/api/content/{page_id}"
        resp = requests.get(url, auth=self.auth, params={"expand": "version,body.storage"})
        resp.raise_for_status()
        return resp.json()

    def update_page_body(self, page_id, title, body_storage, version):
        url = f"{self.base_url}/wiki/rest/api/content/{page_id}"
        payload = {
            "version": {"number": version},
            "title": title,
            "type": "page",
            "body": {"storage": {"value": body_storage, "representation": "storage"}},
        }
        resp = requests.put(url, auth=self.auth, json=payload)
        resp.raise_for_status()
        return resp.json()


def image_tag(filename, width=600, align="center"):
    return (
        f'<ac:image ac:width="{width}" ac:align="{align}" ac:layout="{align}">'
        f'<ri:attachment ri:filename="{filename}" />'
        f"</ac:image>"
    )
