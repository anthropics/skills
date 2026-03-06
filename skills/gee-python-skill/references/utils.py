"""
GEE Python Operations - Utility Functions

Usage:
    from references.utils import ee_init, task_summary, task_check, asset_exists
    from references.utils import get_drive_service, download_drive_files

    ee_init('your-ee-project')
    tasks = task_summary()
    task_check('my_export', tasks)
"""

import ee
import json
import os
import io
from google.oauth2.credentials import Credentials
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload
from ee import oauth
from collections import Counter


def ee_init(project: str):
    """Initialize GEE with the given project ID."""
    ee.Initialize(project=project)


def task_summary():
    """Print count of tasks by state and return all tasks."""
    tasks = ee.batch.Task.list()
    states = Counter(t.status().get('state', '?') for t in tasks)
    print(dict(states))
    return tasks


def task_check(keyword: str, tasks=None):
    """Filter tasks by keyword and print their status."""
    if tasks is None:
        tasks = ee.batch.Task.list()
    filtered = [t for t in tasks if keyword in t.config.get('description', '')]
    for t in filtered:
        s = t.status()
        err = s.get('error_message', '')
        print(f'[{s["state"]}] {t.config["description"]}' + (f'  ERR: {err}' if err else ''))
    return filtered


def asset_exists(asset_id: str) -> bool:
    """Return True if a GEE asset exists."""
    try:
        ee.data.getAsset(asset_id)
        return True
    except ee.ee_exception.EEException:
        return False


def get_drive_service():
    """
    Build a Google Drive API v3 service using EE OAuth credentials.

    The EE credentials file (~/.config/earthengine/credentials) already
    includes the 'drive' scope, so no separate OAuth flow is needed.
    Uses ee.oauth.CLIENT_ID / CLIENT_SECRET — do NOT hardcode these.
    """
    cred_path = os.path.expanduser('~/.config/earthengine/credentials')
    with open(cred_path) as f:
        c = json.load(f)
    creds = Credentials(
        token=None,
        refresh_token=c['refresh_token'],
        token_uri='https://oauth2.googleapis.com/token',
        client_id=oauth.CLIENT_ID,
        client_secret=oauth.CLIENT_SECRET,
        scopes=c['scopes'],
    )
    return build('drive', 'v3', credentials=creds)


def download_drive_files(query: str, out_dir: str, skip_existing: bool = True):
    """
    Batch download Google Drive files matching a query string.

    Args:
        query:         Drive API query, e.g. "name contains 'export' and trashed=false"
        out_dir:       Local directory to save files into.
        skip_existing: Skip files that already exist locally.
    """
    service = get_drive_service()
    os.makedirs(out_dir, exist_ok=True)

    results = service.files().list(
        q=query, pageSize=200, fields='files(id, name)',
    ).execute()
    files = results.get('files', [])
    print(f'Found {len(files)} files -> {out_dir}')

    for i, f in enumerate(sorted(files, key=lambda x: x['name'])):
        out_path = os.path.join(out_dir, f['name'])
        if skip_existing and os.path.exists(out_path):
            print(f'  [{i+1}/{len(files)}] SKIP: {f["name"]}')
            continue
        request = service.files().get_media(fileId=f['id'])
        buf = io.BytesIO()
        downloader = MediaIoBaseDownload(buf, request)
        done = False
        while not done:
            _, done = downloader.next_chunk()
        with open(out_path, 'wb') as out:
            out.write(buf.getvalue())
        print(f'  [{i+1}/{len(files)}] OK: {f["name"]}  ({os.path.getsize(out_path)//1024} KB)')
