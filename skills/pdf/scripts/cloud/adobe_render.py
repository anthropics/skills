"""Adobe PDF Services renderer.

Two modes:
  create   Office (docx/pptx/xlsx) → PDF via Acrobat's real conversion engine.
  to-image PDF pages → PNG/JPEG at higher fidelity than pdftoppm/LibreOffice.

Usage:
    python adobe_render.py create  input.docx output.pdf
    python adobe_render.py to-image input.pdf  out_prefix [--format png|jpeg] [--dpi 150]

Credentials (env vars — Service Account OAuth):
    ADOBE_CLIENT_ID
    ADOBE_CLIENT_SECRET

Uses the REST API (https://pdf-services.adobe.io) so no SDK install needed —
just `requests`. Async jobs: submit → poll `location` → download `downloadUri`.

Endpoints:
    POST /token                                    → access_token
    POST /assets                                   → uploadUri + assetID (S3 presigned)
    PUT  {uploadUri}                               → upload bytes
    POST /operation/createpdf                      → job (Office → PDF)
    POST /operation/pdftoimages                    → job (PDF → PNG/JPEG zip)
    GET  {job location}                            → status/result
"""
from __future__ import annotations

import argparse
import io
import mimetypes
import os
import sys
import time
import zipfile
from pathlib import Path

import requests

BASE = "https://pdf-services.adobe.io"
TOKEN = "https://pdf-services.adobe.io/token"


def _env(name: str) -> str:
    v = os.environ.get(name)
    if not v:
        sys.exit(f"missing env var: {name}")
    return v


def _token() -> str:
    r = requests.post(
        TOKEN,
        data={"client_id": _env("ADOBE_CLIENT_ID"), "client_secret": _env("ADOBE_CLIENT_SECRET")},
        headers={"Content-Type": "application/x-www-form-urlencoded"},
        timeout=30,
    )
    r.raise_for_status()
    return r.json()["access_token"]


def _hdr(token: str) -> dict[str, str]:
    return {"Authorization": f"Bearer {token}", "x-api-key": _env("ADOBE_CLIENT_ID")}


def _upload(token: str, path: Path) -> str:
    mime = mimetypes.guess_type(path.name)[0] or "application/octet-stream"
    a = requests.post(
        f"{BASE}/assets",
        headers={**_hdr(token), "Content-Type": "application/json"},
        json={"mediaType": mime},
        timeout=30,
    )
    a.raise_for_status()
    j = a.json()
    up = requests.put(j["uploadUri"], data=path.read_bytes(), headers={"Content-Type": mime}, timeout=300)
    up.raise_for_status()
    return j["assetID"]


def _poll(token: str, location: str, timeout: int = 300) -> dict:
    deadline = time.time() + timeout
    while time.time() < deadline:
        r = requests.get(location, headers=_hdr(token), timeout=30)
        r.raise_for_status()
        j = r.json()
        st = j.get("status")
        if st == "done":
            return j
        if st == "failed":
            sys.exit(f"adobe job failed: {j}")
        time.sleep(2)
    sys.exit("adobe job timed out")


def create_pdf(src: Path, dst: Path) -> None:
    token = _token()
    asset = _upload(token, src)
    r = requests.post(
        f"{BASE}/operation/createpdf",
        headers={**_hdr(token), "Content-Type": "application/json"},
        json={"assetID": asset},
        timeout=30,
    )
    if r.status_code != 201:
        sys.exit(f"createpdf submit failed: {r.status_code} {r.text}")
    result = _poll(token, r.headers["location"])
    dl = requests.get(result["asset"]["downloadUri"], timeout=300)
    dl.raise_for_status()
    dst.write_bytes(dl.content)
    print(f"wrote {dst} ({dst.stat().st_size} bytes)")


def to_images(src: Path, prefix: Path, fmt: str, dpi: int) -> None:
    token = _token()
    asset = _upload(token, src)
    r = requests.post(
        f"{BASE}/operation/pdftoimages",
        headers={**_hdr(token), "Content-Type": "application/json"},
        json={"assetID": asset, "outputFormat": fmt.upper(), "dpi": dpi},
        timeout=30,
    )
    if r.status_code != 201:
        sys.exit(f"pdftoimages submit failed: {r.status_code} {r.text}")
    result = _poll(token, r.headers["location"])
    dl = requests.get(result["asset"]["downloadUri"], timeout=300)
    dl.raise_for_status()
    with zipfile.ZipFile(io.BytesIO(dl.content)) as zf:
        names = sorted(zf.namelist())
        width = max(2, len(str(len(names))))
        for i, name in enumerate(names, 1):
            out = prefix.with_name(f"{prefix.name}-{i:0{width}d}.{fmt.lower()}")
            out.write_bytes(zf.read(name))
            print(f"wrote {out}")


def main() -> None:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("create")
    c.add_argument("src")
    c.add_argument("dst")
    t = sub.add_parser("to-image")
    t.add_argument("src")
    t.add_argument("prefix")
    t.add_argument("--format", default="png", choices=["png", "jpeg"])
    t.add_argument("--dpi", type=int, default=150)
    a = p.parse_args()
    if a.cmd == "create":
        create_pdf(Path(a.src), Path(a.dst))
    else:
        to_images(Path(a.src), Path(a.prefix), a.format, a.dpi)


if __name__ == "__main__":
    main()
