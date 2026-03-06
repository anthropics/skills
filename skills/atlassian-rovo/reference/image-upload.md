# Image Upload to Confluence — Reference

## Overview

The Atlassian MCP server does NOT have an attachment upload tool. To upload images to Confluence pages, use the **Confluence REST API v1** directly via Python/curl.

## Two-Step Process

1. **Upload** the image as an attachment to a page
2. **Update** the page body to embed the image at the desired location

## API Details

### Upload Endpoint

```
PUT /wiki/rest/api/content/{pageId}/child/attachment
```

- **Auth:** Basic Auth — `email:API_token` (base64)
- **Required header:** `X-Atlassian-Token: nocheck`
- **Body:** `multipart/form-data` with `file` part
- **Behavior:** Creates new attachment, or new version if filename already exists

### Embedding in Page Body (Storage Format)

Reference uploaded attachments by filename:

```xml
<ac:image ac:width="600" ac:align="center" ac:layout="center">
  <ri:attachment ri:filename="chart.png" />
</ac:image>
```

### Page Update

Update the page body via V1 API with incremented version number:

```
PUT /wiki/rest/api/content/{pageId}
Content-Type: application/json

{
  "version": {"number": <current + 1>},
  "title": "Page Title",
  "type": "page",
  "body": {
    "storage": {
      "value": "<p>Text</p><ac:image><ri:attachment ri:filename=\"chart.png\" /></ac:image>",
      "representation": "storage"
    }
  }
}
```

## Python Utility Example

```python
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
```

## Usage

```python
uploader = ConfluenceUploader(base_url, email, api_token)

# Upload image
uploader.upload_attachment(page_id, "/path/to/chart.png")

# Build page body with embedded image
tag = image_tag("chart.png", width=700)
body = f"<h2>Chart</h2>{tag}"

# Update page
page = uploader.get_page(page_id)
uploader.update_page_body(page_id, "Page Title", body, page["version"]["number"] + 1)
```

## Auth Setup

1. Generate API token at https://id.atlassian.com/manage-profile/security/api-tokens
2. Pass as environment variable (never commit tokens to files)

## Limitations

- Max file size: 100 MB
- Upload via V1 API only (V2 is read-only for attachments)
- Storage format is simpler than ADF for image embedding (reference by filename, no UUID needed)
- Re-uploading same filename creates a new version (not a duplicate); page body references stay valid
