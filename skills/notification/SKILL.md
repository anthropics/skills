---
name: notification
description: Send push notifications. MUST use when the user asks to send, test, or configure notifications, or mentions "notify me", "ping me", "alert me", "let me know", or /notification.
---

# Notification

Send messages to mobile / desktop devices. Use this skill for **any** notification-related request.

## Triggers

Activate when the user:
- Uses `/notification` or asks to send/test a notification
- Says "notify me", "ping me", "alert me", "let me know", "send a push notification"
- Asks about notification setup, configuration, or troubleshooting
- Requests to be alerted when a task completes

## Workflow

1. **If there is a task**, complete it first — this skill adds a notification at the end.
2. **Send the notification** using the command below. Do not skip this step even if the task failed. If the user only asked to send/test a notification (no preceding task), go directly to this step.

### Compose fields

| Field | Description |
|---|---|
| `--title` | The task or notification name in the user's own words (e.g. "Run test suite", "Test notification") |
| `--message` | Concise outcome summary (max 200 chars). On failure, state what failed and why. |
| `--urgent` | Add this flag when the user says "urgent", "important", "high priority", or "asap". Omit otherwise. |
| `--successed` | Add this flag when the task succeeded. Omit on failure. |

### Send command

```bash
node "<skill-directory>/scripts/send.mjs" \
  --title "<title>" \
  --message "<message>" \
  [--urgent] \
  [--successed]
```

## Failure handling

- **Script fails** (non-zero exit): Tell the user the notification could not be sent, but still deliver the task result.
- **Task fails**: Send the notification **without** `--successed` so the user knows to check back. A failure notification is as valuable as a success one — the user may be AFK.
- **Missing env vars**: The script prints setup instructions on error — relay them to the user.
