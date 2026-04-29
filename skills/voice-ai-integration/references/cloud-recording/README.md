# Agora Cloud Recording

Server-side recording of RTC channel audio/video. REST API only — no client SDK needed.

## Quick Reference

| Item | Value |
|------|-------|
| What it does | Records RTC channel audio/video to cloud storage |
| Interface | REST API only — no client SDK needed |
| Auth | HTTP Basic Auth (`AGORA_CUSTOMER_KEY:AGORA_CUSTOMER_SECRET`) |
| Prerequisite | Cloud Recording enabled in Agora Console |
| Depends on | Active RTC channel with participants |
| Full REST API reference | <https://docs-md.agora.io/en/cloud-recording/reference/restful-api.md> |

## Recording Lifecycle

```text
acquire → start → [query] → stop
```

**TTL gotcha:** `resourceId` expires 5 minutes after `acquire` — you must call `start` within that window.

### Step 1: Acquire Resource

```text
POST /v1/apps/{appId}/cloud_recording/acquire
```

Returns a `resourceId`. Valid for 5 minutes — call `start` immediately.

### Step 2: Start Recording

```text
POST /v1/apps/{appId}/cloud_recording/resourceid/{resourceId}/mode/{mode}/start
```

Choose a recording mode (see Recording Modes below). Returns a `sid` (session ID).

### Step 3: Query Status (optional)

```text
GET /v1/apps/{appId}/cloud_recording/resourceid/{resourceId}/sid/{sid}/mode/{mode}/query
```

Use to check recording status or verify the session is active.

### Step 4: Stop Recording

```text
POST /v1/apps/{appId}/cloud_recording/resourceid/{resourceId}/sid/{sid}/mode/{mode}/stop
```

Always call `stop` when recording is no longer needed to avoid unnecessary billing.

## Recording Modes

| Mode | Output | Use case |
|------|--------|----------|
| `individual` | Separate audio/video file per user | Post-processing, transcription |
| `mix` | Single mixed audio/video file | Archival, playback |
| `web` | Records a web page as video | Web app recording, whiteboard |

## Error Handling

| Error | Cause | Fix |
|-------|-------|-----|
| 403 | Cloud Recording not enabled in Console | Enable in Agora Console |
| 404 | Resource expired or invalid sid | Re-acquire resource; check sid |
| 432 | Recording already in progress | Query existing recording first |
| 435 | No users in channel | Ensure RTC channel has active participants before starting |
| Storage error | Wrong storage config | Verify bucket name, access keys, region |

## Auth Pattern

Same as all Agora REST APIs — HTTP Basic Auth:

```text
Authorization: Basic base64("{AGORA_CUSTOMER_KEY}:{AGORA_CUSTOMER_SECRET}")
```

Credentials must come from environment variables — never hardcoded.

## When to Fetch More

Always use Level 2 fetch for: full REST API field details, storage config options (S3/OSS/GCS), composite layout parameters, error code listings. Fetch directly: <https://docs-md.agora.io/en/cloud-recording/reference/restful-api.md>
