"""Render an Office document to PDF using Microsoft Graph.

Usage:
    python graph_render.py input.docx output.pdf

Uses Word Online / PowerPoint Online / Excel Online engines for true
Microsoft-fidelity conversion. Falls back with a clear error if creds
missing — call soffice.py for the local LibreOffice path instead.

Credentials (env vars, client-credentials flow with app-only OneDrive):
    GRAPH_TENANT_ID
    GRAPH_CLIENT_ID
    GRAPH_CLIENT_SECRET
    GRAPH_DRIVE_ID        (target OneDrive/SharePoint drive)

Auth: OAuth2 client_credentials against
    https://login.microsoftonline.com/{tenant}/oauth2/v2.0/token
    scope=https://graph.microsoft.com/.default

Flow:
    1. PUT the file to /drives/{driveId}/root:/{name}:/content
    2. GET  /drives/{driveId}/items/{itemId}/content?format=pdf
       (302 redirect — requests follows automatically)
    3. DELETE the temp item

Requires: `requests` (stdlib-only fallback below is intentionally not provided;
install with `pip install requests` if missing).
"""
from __future__ import annotations

import os
import sys
import uuid
from pathlib import Path

import requests

GRAPH = "https://graph.microsoft.com/v1.0"
TOKEN_URL = "https://login.microsoftonline.com/{tenant}/oauth2/v2.0/token"


def _env(name: str) -> str:
    v = os.environ.get(name)
    if not v:
        sys.exit(f"missing env var: {name}")
    return v


def _token() -> str:
    tenant = _env("GRAPH_TENANT_ID")
    r = requests.post(
        TOKEN_URL.format(tenant=tenant),
        data={
            "client_id": _env("GRAPH_CLIENT_ID"),
            "client_secret": _env("GRAPH_CLIENT_SECRET"),
            "scope": "https://graph.microsoft.com/.default",
            "grant_type": "client_credentials",
        },
        timeout=30,
    )
    r.raise_for_status()
    return r.json()["access_token"]


def render_to_pdf(src: Path, dst: Path) -> None:
    if not src.exists():
        sys.exit(f"not found: {src}")
    token = _token()
    drive = _env("GRAPH_DRIVE_ID")
    hdr = {"Authorization": f"Bearer {token}"}
    tmp_name = f"_render_{uuid.uuid4().hex}{src.suffix}"

    up = requests.put(
        f"{GRAPH}/drives/{drive}/root:/{tmp_name}:/content",
        headers={**hdr, "Content-Type": "application/octet-stream"},
        data=src.read_bytes(),
        timeout=120,
    )
    up.raise_for_status()
    item_id = up.json()["id"]

    try:
        dl = requests.get(
            f"{GRAPH}/drives/{drive}/items/{item_id}/content",
            params={"format": "pdf"},
            headers=hdr,
            allow_redirects=True,
            timeout=120,
        )
        dl.raise_for_status()
        dst.write_bytes(dl.content)
    finally:
        requests.delete(f"{GRAPH}/drives/{drive}/items/{item_id}", headers=hdr, timeout=30)

    print(f"wrote {dst} ({dst.stat().st_size} bytes)")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit("usage: graph_render.py input.<docx|pptx|xlsx> output.pdf")
    render_to_pdf(Path(sys.argv[1]), Path(sys.argv[2]))
