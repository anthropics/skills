# Managed Agents — Webhooks

Anthropic can POST to your HTTPS endpoint when a Managed Agents resource changes state — an alternative to holding an SSE stream or polling. Payloads are **thin** (event type + resource IDs only); on receipt, fetch the resource for current state. Every delivery is HMAC-signed.

> **Direction matters.** This page covers *Anthropic → you* notifications about session/vault state. It does **not** cover *third-party → you* webhooks that *trigger* a session (e.g. a GitHub push handler that calls `sessions.create()`) — that's ordinary application code on your side with no Anthropic-specific wire format.

---

## Register an endpoint (Console only)

Console → **Manage → Webhooks**. There is no programmatic endpoint-management API yet. Secret rotation is supported from the same page.

| Field | Constraint |
|---|---|
| URL | HTTPS on port 443, publicly resolvable hostname |
| Event types | Subscribe per `data.type` — you only receive subscribed types (plus test events) |
| Signing secret | `whsec_`-prefixed, 32 bytes, **shown once at creation** — store it |

---

## Verify the signature

Every delivery is HMAC-signed. **Use the SDK's `client.beta.webhooks.unwrap()`** — it verifies the signature, rejects payloads more than ~5 minutes old, and returns the parsed event. It reads the `whsec_` secret from `ANTHROPIC_WEBHOOK_SIGNING_KEY`.

```python
import anthropic
from flask import Flask, request

client = anthropic.Anthropic()  # reads ANTHROPIC_WEBHOOK_SIGNING_KEY from env
app = Flask(__name__)


@app.route("/webhook", methods=["POST"])
def webhook():
    try:
        event = client.beta.webhooks.unwrap(
            request.get_data(as_text=True),
            headers=dict(request.headers),
        )
    except Exception:
        return "invalid signature", 400

    if event.id in seen_event_ids:  # dedupe retries — id is per-event, not per-delivery
        return "", 204
    seen_event_ids.add(event.id)

    match event.data.type:
        case "session.status_idled":
            session = client.beta.sessions.retrieve(event.data.id)
            notify_user(session)
        case "vault_credential.refresh_failed":
            alert_oncall(event.data.id)

    return "", 204
```

Pass the **raw request body** to `unwrap()` — frameworks that re-serialize JSON (Express `.json()`, Flask `.get_json()`) change the bytes and break the MAC. For other languages, look up the `beta.webhooks.unwrap` binding in the SDK repo (`shared/live-sources.md`); don't hand-roll verification.

---

## Payload envelope

```json
{
  "type": "event",
  "id": "event_01ABC...",
  "created_at": "2026-03-18T14:05:22Z",
  "data": {
    "type": "session.status_idled",
    "id": "session_01XYZ...",
    "organization_id": "8a3d2f1e-...",
    "workspace_id": "c7b0e4d9-..."
  }
}
```

Switch on `data.type`, fetch the resource by `data.id`, return any **2xx** to acknowledge. `created_at` is when the *state transition* happened, not when the webhook fired.

---

## Supported `data.type` values

| `data.type` | Fires when |
|---|---|
| `session.status_scheduled` | Session created and ready to accept events |
| `session.status_run_started` | Agent execution kicked off (every transition to `running`) |
| `session.status_idled` | Agent awaiting input (tool approval, custom tool result, or next message) |
| `session.status_terminated` | Session hit a terminal error |
| `session.thread_created` | Multiagent: coordinator opened a new subagent thread |
| `session.thread_idled` | Multiagent: a subagent thread is waiting for input |
| `session.outcome_evaluation_ended` | Outcome grader finished one iteration |
| `vault.archived` | Vault was archived |
| `vault.created` | Vault was created |
| `vault.deleted` | Vault was deleted |
| `vault_credential.archived` | Vault credential was archived |
| `vault_credential.created` | Vault credential was created |
| `vault_credential.deleted` | Vault credential was deleted |
| `vault_credential.refresh_failed` | MCP OAuth vault credential failed to refresh |

> These are **webhook** `data.type` values — a separate namespace from SSE event types (`session.status_idle`, `span.outcome_evaluation_end`, etc. in `shared/managed-agents-events.md`). Don't reuse SSE constants in webhook handlers.

---

## Delivery behavior & pitfalls

- **No ordering guarantee.** `session.status_idled` may arrive before `session.outcome_evaluation_ended` even if the evaluation finished first. Sort by envelope `created_at` if order matters.
- **Retries carry the same `event.id`.** At least one retry on non-2xx. Dedupe on `event.id`.
- **3xx is failure.** Redirects are not followed — update the URL in Console if your endpoint moves.
- **Auto-disable** after ~20 consecutive failed deliveries, or immediately if the hostname resolves to a private IP or returns a redirect. Re-enable manually in Console.
- **Thin payload is intentional.** Don't expect `stop_reason`, `outcome_evaluations`, credential secrets, etc. on the webhook body — fetch the resource.
