---
name: gee-python-skill
description: Google Earth Engine Python API operations — task submission, status checking, Google Drive download, asset management, and upload workflows. Use when submitting GEE batch tasks, monitoring task queues, downloading results from Google Drive, managing GEE assets, or uploading local files to GEE.
---

# GEE Python Operations Skill

> Requires: `earthengine-api`, `google-api-python-client`, `google-auth`
> Credentials: `~/.config/earthengine/credentials` (set by `ee.Authenticate()`)

---

## 1. Initialization

```python
import ee

ee.Initialize(project='your-ee-project')

# If token expired, re-authenticate:
# ee.Authenticate()
# ee.Initialize(project='your-ee-project')
```

---

## 2. Task Submission

### Export image to Asset

```python
task = ee.batch.Export.image.toAsset(
    image=my_image,
    description='task_description',
    assetId='projects/your-ee-project/assets/asset_name',
    region=aoi,
    crs='EPSG:4326',
    scale=30,
    maxPixels=1e13,
)
task.start()
print(f'Submitted: {task.id}')
```

### Export table to Google Drive

```python
task = ee.batch.Export.table.toDrive(
    collection=feature_collection,
    description='task_description',
    folder='GEE_Exports',
    fileNamePrefix='output_filename',  # no .csv extension
    fileFormat='CSV',
)
task.start()
print(f'Submitted: {task.id}')
```

### Batch submission with rate limiting

```python
import time

for year in range(2010, 2023):
    task = ee.batch.Export.table.toDrive(...)
    task.start()
    print(f'[{year}] {task.id}')
    time.sleep(0.5)  # prevent throttling
```

### Fix out-of-memory errors: tileScale

When `reduceRegions` or `reduceRegion` raises `Execution failed; out of memory`:

```python
result = image.reduceRegions(
    collection=regions,
    reducer=ee.Reducer.mean(),
    scale=30,
    tileScale=4,   # default 1; use 2/4/8/16 to fix memory errors
)
```

---

## 3. Task Status

### Summary of all tasks

```python
tasks = ee.batch.Task.list()
from collections import Counter
states = Counter(t.status().get('state', '?') for t in tasks)
print(dict(states))
# e.g. {'SUCCEEDED': 130, 'FAILED': 5, 'RUNNING': 2, 'READY': 3}
```

### Filter tasks by keyword

```python
keyword = 'my_export'
filtered = [t for t in tasks if keyword in t.config.get('description', '')]

for t in filtered:
    s = t.status()
    state = s.get('state', '?')
    err = s.get('error_message', '')
    print(f'[{state}] {t.config["description"]}' + (f'  ERR: {err}' if err else ''))
```

### Cancel tasks

```python
# Cancel all RUNNING tasks
for t in tasks:
    if t.status().get('state') == 'RUNNING':
        t.cancel()
        print(f'Cancelled: {t.config["description"]}')

# Cancel by keyword
for t in tasks:
    if 'my_export' in t.config.get('description', ''):
        t.cancel()
```

### Check if asset exists

```python
def asset_exists(asset_id: str) -> bool:
    try:
        ee.data.getAsset(asset_id)
        return True
    except ee.ee_exception.EEException:
        return False

if asset_exists('projects/your-ee-project/assets/my_asset'):
    print('exists')
```

---

## 4. Google Drive Download

> The EE OAuth2 token includes `drive` scope — no separate auth needed.

### Build Drive service connection

```python
import json, os
from google.oauth2.credentials import Credentials
from googleapiclient.discovery import build
from ee import oauth

def get_drive_service():
    cred_path = os.path.expanduser('~/.config/earthengine/credentials')
    with open(cred_path) as f:
        c = json.load(f)
    creds = Credentials(
        token=None,
        refresh_token=c['refresh_token'],
        token_uri='https://oauth2.googleapis.com/token',
        client_id=oauth.CLIENT_ID,       # use ee.oauth — NOT hardcoded values
        client_secret=oauth.CLIENT_SECRET,
        scopes=c['scopes'],
    )
    return build('drive', 'v3', credentials=creds)

service = get_drive_service()
```

### List files in Drive

```python
results = service.files().list(
    q="name contains 'my_export' and name contains '.csv' and trashed=false",
    pageSize=100,
    fields='files(id, name, size, modifiedTime)',
).execute()

files = results.get('files', [])
for f in sorted(files, key=lambda x: x['name']):
    print(f['name'], f.get('size', '?'), 'bytes')
```

**Common Drive query syntax:**
```
name contains 'keyword'
name = 'exact_name.csv'
trashed=false
'folder_id' in parents
mimeType = 'text/csv'
```

### Download single file

```python
import io
from googleapiclient.http import MediaIoBaseDownload

def download_file(service, file_id, out_path):
    request = service.files().get_media(fileId=file_id)
    buf = io.BytesIO()
    downloader = MediaIoBaseDownload(buf, request)
    done = False
    while not done:
        _, done = downloader.next_chunk()
    with open(out_path, 'wb') as f:
        f.write(buf.getvalue())
```

### Batch download

```python
def download_all(service, query, out_dir, skip_existing=True):
    os.makedirs(out_dir, exist_ok=True)
    results = service.files().list(
        q=query, pageSize=200,
        fields='files(id, name)',
    ).execute()
    files = results.get('files', [])
    print(f'Found {len(files)} files')

    for i, f in enumerate(sorted(files, key=lambda x: x['name'])):
        out_path = os.path.join(out_dir, f['name'])
        if skip_existing and os.path.exists(out_path):
            print(f'[{i+1}/{len(files)}] SKIP: {f["name"]}')
            continue
        request = service.files().get_media(fileId=f['id'])
        buf = io.BytesIO()
        downloader = MediaIoBaseDownload(buf, request)
        done = False
        while not done:
            _, done = downloader.next_chunk()
        with open(out_path, 'wb') as out:
            out.write(buf.getvalue())
        print(f'[{i+1}/{len(files)}] OK: {f["name"]}  ({os.path.getsize(out_path)//1024} KB)')

# Usage
service = get_drive_service()
download_all(
    service,
    query="name contains 'my_export' and name contains '.csv' and trashed=false",
    out_dir='/path/to/output',
)
```

---

## 5. GEE Asset Download (Asset → Local)

GEE assets cannot be downloaded directly — export to Drive first, then download.

### Image asset → Drive → local

```python
asset_id = 'projects/your-ee-project/assets/my_image_asset'
image = ee.Image(asset_id)

task = ee.batch.Export.image.toDrive(
    image=image,
    description='export_my_image',
    folder='GEE_Exports',
    fileNamePrefix='my_image_asset',
    region=aoi,
    scale=30,
    maxPixels=1e13,
    fileFormat='GeoTIFF',
)
task.start()
```

### FeatureCollection → Drive

```python
fc = ee.FeatureCollection('projects/your-ee-project/assets/my_vector_asset')

task = ee.batch.Export.table.toDrive(
    collection=fc,
    description='export_features',
    folder='GEE_Exports',
    fileNamePrefix='my_features',
    fileFormat='CSV',   # or 'GeoJSON', 'SHP', 'KML'
)
task.start()
```

---

## 6. GEE Asset Upload (Local → Asset)

> Direct REST API binary upload is not supported — must go through GCS or Colab.

### Method A: earthengine CLI + GCS (recommended)

```bash
# Push local file to GCS first
gsutil cp /path/to/file.tif gs://your-bucket/file.tif

# Ingest from GCS into Asset
earthengine upload image \
  --asset_id projects/your-ee-project/assets/asset_name \
  gs://your-bucket/file.tif
```

### Method B: Python API + GCS (requires billing)

```python
import ee, subprocess

PROJECT = 'your-ee-project'
BUCKET = 'your-gcs-bucket'
LOCAL_FILE = '/path/to/file.tif'
GCS_URI = f'gs://{BUCKET}/file.tif'
ASSET_ID = f'projects/{PROJECT}/assets/MyAsset'

subprocess.run(['gsutil', 'cp', LOCAL_FILE, GCS_URI], check=True)

ee.Initialize(project=PROJECT)
request = {
    'type': 'IMAGE',
    'gcs_location': {'uris': [GCS_URI]},
}
task = ee.data.startIngestion(
    request_id=ee.data.newTaskId()[0],
    params=request,
    allow_overwrite=True,
)
print('Ingestion task:', task)
```

### Method C: Google Colab (free, no billing required)

```python
# Run in Colab
from google.colab import auth
auth.authenticate_user()

import ee
ee.Authenticate()
ee.Initialize(project='your-ee-project')

from google.cloud import storage
client = storage.Client()
bucket = client.bucket('your-bucket')
blob = bucket.blob('file.tif')
blob.upload_from_filename('/content/file.tif')

request = {
    'type': 'IMAGE',
    'gcs_location': {'uris': ['gs://your-bucket/file.tif']},
}
ee.data.startIngestion(
    request_id=ee.data.newTaskId()[0],
    params=request,
)
```

### Method D: earthengine CLI direct upload (experimental, CLI >= 0.1.370)

```bash
earthengine upload image \
  --asset_id projects/your-ee-project/assets/asset_name \
  /path/to/file.tif
```

> Unstable for large files — prefer GCS-based methods.

---

## 7. Consolidated Utility Functions

See `references/utils.py` for all functions in one importable module.

```python
from references.utils import ee_init, task_summary, task_check, asset_exists, get_drive_service, download_drive_files

ee_init('your-ee-project')
task_summary()
task_check('my_export')
```

---

## 8. Quick Reference

| Operation | Code |
|-----------|------|
| Initialize | `ee.Initialize(project='...')` |
| Submit task | `task.start(); print(task.id)` |
| List all tasks | `ee.batch.Task.list()` |
| Task state | `t.status().get('state')` |
| Task error | `t.status().get('error_message')` |
| Cancel task | `t.cancel()` |
| Check asset exists | `ee.data.getAsset(id)` |
| Fix memory error | `reduceRegions(..., tileScale=4)` |
| Drive connection | `build('drive', 'v3', credentials=creds)` |
| List Drive files | `service.files().list(q=...).execute()` |
| Download file | `MediaIoBaseDownload(buf, request)` |
| Upload asset | earthengine CLI + GCS, or Colab |
