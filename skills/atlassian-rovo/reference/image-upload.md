# Image Upload to Confluence — Reference

## Overview

Upload images to Confluence pages using the **Confluence REST API v1** via the bundled script or curl.

## Two-Step Process

1. **Upload** the image as an attachment to a page
2. **Update** the page body to embed the image at the desired location

## Bundled Script

Use `scripts/confluence_upload.py` for a ready-made Python utility:

```python
from confluence_upload import ConfluenceUploader, image_tag

uploader = ConfluenceUploader(base_url, email, api_token)

# Upload image
uploader.upload_attachment(page_id, "/path/to/chart.png")

# Build page body with embedded image
tag = image_tag("chart.png", width=700)
page = uploader.get_page(page_id)
body = page["body"]["storage"]["value"] + tag
uploader.update_page_body(page_id, page["title"], body, page["version"]["number"] + 1)
```

Requires `requests` package. Load credentials from `.env` or environment variables.

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

## Auth Setup

1. Generate API token at https://id.atlassian.com/manage-profile/security/api-tokens
2. Add to `.env` file (never commit tokens to source control):
   ```
   ATLASSIAN_API_TOKEN=<your-api-token>
   ATLASSIAN_EMAIL=<your-atlassian-email>
   ATLASSIAN_SITE=https://<your-site>.atlassian.net
   ```
3. Load in Python: `os.environ["ATLASSIAN_API_TOKEN"]` (or use `python-dotenv`)

See [setup.md](setup.md) for full setup instructions.

## Limitations

- Max file size: 100 MB
- Upload via V1 API only (V2 is read-only for attachments)
- Storage format is simpler than ADF for image embedding (reference by filename, no UUID needed)
- Re-uploading same filename creates a new version (not a duplicate); page body references stay valid
