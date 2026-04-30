#!/usr/bin/env python3
"""
buyer-eval skill — opt-in usage telemetry.

What this script does:
  - Records whether the user has consented to share anonymized usage data.
  - When consented, sends events (vendor questions, scores, completion) to the
    Salespeak event-stream endpoint, and writes a local audit-log copy.
  - Respects an enterprise kill-switch (env var or /etc config) that blocks
    all telemetry regardless of user consent.

What this script never does:
  - Send anything before the user consents.
  - Block or slow down the skill on network errors (fire-and-forget, 2s timeout).
  - Surface errors to stderr (errors go only to the local audit log).
  - Collect anything beyond what's in the data dict each event call passes in.

Subcommands (called from SKILL.md):
  status [--machine]    Print state: consented | declined | locked_off | unasked
  event SUB --json STR  Send one event (only acts if state == consented)
  grant --events JSON   Record consent=yes, generate user_id, batch-send events
  decline               Record consent=no (so we never ask again)
  revoke                Set consent=no (user changed their mind)
  show                  Print user_id + state + audit-log path (for deletion requests)

Endpoint, org_id, campaign_id are constants at the top of the file. To audit:
  cat ~/.salespeak/buyer-eval.log
"""

import argparse
import json
import os
import subprocess
import sys
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants — every event sent uses these. Read once, never mutated.
# ---------------------------------------------------------------------------

ENDPOINT = os.environ.get(
    "BUYER_EVAL_ENDPOINT",
    "https://22i9zfydr3.execute-api.us-west-2.amazonaws.com/prod/event_stream",
)
ORGANIZATION_ID = "87996776-2ccf-4198-bd8a-3aa7c5a6986c"
CAMPAIGN_ID = "d6b3cf8a-9403-4b65-9d3b-366f4d1c9125"
EVENT_TYPE = "buyer_eval"
SOURCE_URL = "https://github.com/salespeak-ai/buyer-eval-skill"
SKILL_VERSION = "3.4.0"
USER_AGENT = f"buyer-eval-skill/{SKILL_VERSION} (+{SOURCE_URL})"
HTTP_TIMEOUT_SEC = 2.0

USER_CONFIG_DIR = Path.home() / ".salespeak"
USER_CONFIG_PATH = USER_CONFIG_DIR / "buyer-eval.json"
AUDIT_LOG_PATH = USER_CONFIG_DIR / "buyer-eval.log"
SYSTEM_CONFIG_PATH = Path("/etc/salespeak/buyer-eval.json")
ENV_KILL_SWITCH = "BUYER_EVAL_NO_TELEMETRY"

STATE_CONSENTED = "consented"
STATE_DECLINED = "declined"
STATE_LOCKED_OFF = "locked_off"
STATE_UNASKED = "unasked"


# ---------------------------------------------------------------------------
# State + storage helpers
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _ensure_config_dir() -> None:
    USER_CONFIG_DIR.mkdir(parents=True, exist_ok=True)


def _read_json(path: Path) -> dict | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def _kill_switch_active() -> bool:
    env = os.environ.get(ENV_KILL_SWITCH, "").strip().lower()
    if env in {"1", "true", "yes", "on"}:
        return True
    sys_cfg = _read_json(SYSTEM_CONFIG_PATH)
    if sys_cfg and sys_cfg.get("locked") is True and sys_cfg.get("consent") is False:
        return True
    return False


def get_state() -> str:
    """Return one of: consented | declined | locked_off | unasked."""
    if _kill_switch_active():
        return STATE_LOCKED_OFF
    cfg = _read_json(USER_CONFIG_PATH)
    if not cfg:
        return STATE_UNASKED
    if cfg.get("consent") is True and cfg.get("user_id"):
        return STATE_CONSENTED
    if cfg.get("consent") is False:
        return STATE_DECLINED
    return STATE_UNASKED


def get_user_id() -> str | None:
    cfg = _read_json(USER_CONFIG_PATH)
    return cfg.get("user_id") if cfg else None


def _write_user_config(consent: bool, user_id: str | None = None) -> None:
    _ensure_config_dir()
    payload = {
        "consent": consent,
        "user_id": user_id,
        "asked_at": _now_iso(),
        "schema_version": 1,
    }
    USER_CONFIG_PATH.write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )


# ---------------------------------------------------------------------------
# Audit log — every send (success or failure) is written here so the user
# can verify exactly what left their machine.
# ---------------------------------------------------------------------------


def _audit(action: str, **fields) -> None:
    try:
        _ensure_config_dir()
        line = json.dumps(
            {"ts": _now_iso(), "action": action, **fields},
            ensure_ascii=False,
            separators=(",", ":"),
        )
        with AUDIT_LOG_PATH.open("a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError:
        # Audit log is best-effort. Never raise from telemetry.
        pass


# ---------------------------------------------------------------------------
# Network — fire-and-forget POST. Never raises; logs all outcomes to audit log.
# ---------------------------------------------------------------------------


def _build_envelope(
    user_id: str, session_id: str, sub_event: str, data: dict
) -> dict:
    body = {
        "event_type": EVENT_TYPE,
        "user_id": user_id,
        "organization_id": ORGANIZATION_ID,
        "campaign_id": CAMPAIGN_ID,
        "session_id": session_id,
        "url": SOURCE_URL,
        "data": {"sub_event": sub_event, **data},
    }
    return body


def _post(envelope: dict) -> None:
    """POST the envelope to the event-stream endpoint via curl.

    Why curl and not urllib: macOS system Python ships without a working CA
    bundle, which makes urllib's HTTPS calls fail with CERTIFICATE_VERIFY_FAILED
    on a meaningful fraction of end-user machines. curl uses the OS cert store
    and is preinstalled on macOS, Linux, and Windows 10+. We accept the
    subprocess overhead in exchange for working out of the box.
    """
    body = json.dumps(envelope)
    started = time.time()
    try:
        result = subprocess.run(
            [
                "curl",
                "-sS",
                "--max-time", str(HTTP_TIMEOUT_SEC),
                "-X", "POST",
                "-H", "Content-Type: application/json",
                "-H", f"User-Agent: {USER_AGENT}",
                "--data-binary", body,
                "-o", "/dev/null",
                "-w", "%{http_code}",
                ENDPOINT,
            ],
            capture_output=True,
            text=True,
            timeout=HTTP_TIMEOUT_SEC + 1,
        )
        status_str = (result.stdout or "").strip()
        try:
            status = int(status_str)
        except ValueError:
            status = 0
        ms = int((time.time() - started) * 1000)

        if status == 201:
            _audit("sent", status=status, ms=ms, payload=envelope)
        elif status == 200:
            # Spec: 200 = silently dropped (UA blocked). Surface so anyone
            # reading their own audit log notices if the UA filter changes.
            _audit("dropped_by_server", status=status, ms=ms, payload=envelope)
        elif status == 0:
            _audit(
                "send_failed",
                error=(result.stderr or "curl exited with no status").strip()[:300],
                ms=ms,
                payload=envelope,
            )
        else:
            _audit(
                "send_failed",
                error=f"HTTP {status}",
                ms=ms,
                payload=envelope,
            )
    except FileNotFoundError:
        _audit("send_failed", error="curl not found on PATH", payload=envelope)
    except subprocess.TimeoutExpired:
        _audit(
            "send_failed",
            error=f"timeout after {HTTP_TIMEOUT_SEC}s",
            ms=int((time.time() - started) * 1000),
            payload=envelope,
        )
    except OSError as e:
        _audit(
            "send_failed",
            error=str(e),
            ms=int((time.time() - started) * 1000),
            payload=envelope,
        )


def _send_one(user_id: str, session_id: str, sub_event: str, data: dict) -> None:
    envelope = _build_envelope(user_id, session_id, sub_event, data)
    _post(envelope)


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------


def cmd_status(args) -> int:
    state = get_state()
    if args.machine:
        print(state)
        return 0
    print(f"telemetry state: {state}")
    if state == STATE_LOCKED_OFF:
        env_set = bool(os.environ.get(ENV_KILL_SWITCH))
        sys_set = SYSTEM_CONFIG_PATH.is_file()
        reasons = []
        if env_set:
            reasons.append(f"env {ENV_KILL_SWITCH} is set")
        if sys_set:
            reasons.append(f"system policy at {SYSTEM_CONFIG_PATH}")
        print("disabled by:", "; ".join(reasons) or "unknown")
    elif state == STATE_CONSENTED:
        uid = get_user_id() or "<missing>"
        print(f"user_id: {uid}")
    print(f"audit log: {AUDIT_LOG_PATH}")
    return 0


def cmd_event(args) -> int:
    if get_state() != STATE_CONSENTED:
        return 0
    user_id = get_user_id()
    if not user_id:
        return 0
    try:
        data = json.loads(args.json) if args.json else {}
        if not isinstance(data, dict):
            return 0
    except ValueError:
        _audit("event_parse_failed", sub_event=args.sub_event, raw=args.json)
        return 0
    session_id = args.session_id or str(uuid.uuid4())
    _send_one(user_id, session_id, args.sub_event, data)
    return 0


def cmd_grant(args) -> int:
    """User said yes at the consent prompt. Generate user_id, batch-send the
    accumulated events from this run, write the consent record."""
    state = get_state()
    if state == STATE_LOCKED_OFF:
        # Enterprise lock wins. Tell SKILL.md so it can show a one-liner.
        print("locked_off")
        return 0
    if state in (STATE_CONSENTED, STATE_DECLINED):
        # Already answered — defensive no-op (don't overwrite).
        print(state)
        return 0

    user_id = str(uuid.uuid4())
    _write_user_config(consent=True, user_id=user_id)
    _audit("consent_recorded", value="yes", user_id=user_id)

    # Send accumulated events from this run
    session_id = args.session_id or str(uuid.uuid4())
    try:
        events = json.loads(args.events) if args.events else []
        if not isinstance(events, list):
            events = []
    except ValueError:
        events = []
        _audit("grant_events_parse_failed", raw=args.events)

    for ev in events:
        if not isinstance(ev, dict):
            continue
        sub_event = ev.get("sub_event")
        if not sub_event:
            continue
        data = {k: v for k, v in ev.items() if k != "sub_event"}
        _send_one(user_id, session_id, sub_event, data)

    print("ok")
    return 0


def cmd_decline(args) -> int:
    state = get_state()
    if state == STATE_LOCKED_OFF:
        print("locked_off")
        return 0
    if state in (STATE_CONSENTED, STATE_DECLINED):
        print(state)
        return 0
    _write_user_config(consent=False, user_id=None)
    _audit("consent_recorded", value="no")
    print("ok")
    return 0


def cmd_revoke(args) -> int:
    if get_state() == STATE_LOCKED_OFF:
        print("locked_off — telemetry already disabled by system policy")
        return 0
    _write_user_config(consent=False, user_id=None)
    _audit("consent_revoked")
    print("Telemetry disabled. We will not collect or send any further data.")
    print(f"To re-enable, delete {USER_CONFIG_PATH} and run the skill again.")
    return 0


def cmd_show(args) -> int:
    state = get_state()
    print(f"state: {state}")
    uid = get_user_id()
    if uid:
        print(f"user_id: {uid}")
        print()
        print("To delete your data, email omer@salespeak.ai with the user_id above.")
    else:
        print("(no user_id — nothing to delete)")
    print(f"audit log: {AUDIT_LOG_PATH}")
    return 0


# ---------------------------------------------------------------------------
# argparse glue
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="track.py", description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_status = sub.add_parser("status", help="Show current consent state")
    p_status.add_argument("--machine", action="store_true",
                          help="Print just the state word (for scripts)")
    p_status.set_defaults(func=cmd_status)

    p_event = sub.add_parser("event", help="Send one event (run 2+ only)")
    p_event.add_argument("sub_event")
    p_event.add_argument("--json", default="{}",
                         help="Event-specific data as a JSON object")
    p_event.add_argument("--session-id", default=None,
                         help="UUID4 for this skill run")
    p_event.set_defaults(func=cmd_event)

    p_grant = sub.add_parser("grant",
                             help="Record consent=yes, batch-send run-1 events")
    p_grant.add_argument("--events", default="[]",
                         help="JSON array of accumulated events from this run")
    p_grant.add_argument("--session-id", default=None,
                         help="UUID4 for this skill run")
    p_grant.set_defaults(func=cmd_grant)

    p_decline = sub.add_parser("decline", help="Record consent=no")
    p_decline.set_defaults(func=cmd_decline)

    p_revoke = sub.add_parser("revoke", help="Disable telemetry (revoke consent)")
    p_revoke.set_defaults(func=cmd_revoke)

    p_show = sub.add_parser("show", help="Show user_id (for deletion requests)")
    p_show.set_defaults(func=cmd_show)

    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except Exception as e:  # pragma: no cover — defensive, never break the skill
        _audit("unhandled_error", error=str(e), cmd=args.cmd)
        return 0


if __name__ == "__main__":
    sys.exit(main())
