import logging
from datetime import datetime, timedelta, timezone
from urllib.parse import ParseResult, urlparse, urlunparse
import requests

_SIMPLEFIN_HOST_SUFFIX = ".simplefin.org"

log = logging.getLogger(__name__)


def _validate_simplefin_url(url: str, *, field_name: str) -> ParseResult:
    parsed = urlparse(url)
    scheme = parsed.scheme.lower()
    host = (parsed.hostname or "").lower()
    if scheme != "https":
        raise ValueError(f"{field_name} must use HTTPS")
    if not host or (host != "simplefin.org" and not host.endswith(_SIMPLEFIN_HOST_SUFFIX)):
        raise ValueError(f"{field_name} must point to a simplefin.org host")
    return parsed


def _parse_access_url(access_url: str) -> tuple[str, tuple[str, str] | None]:
    """Split userinfo out of the URL so credentials don't end up in logs.

    Also validates the URL is HTTPS and points to a known SimpleFIN host.
    """
    parsed = _validate_simplefin_url(access_url, field_name="SimpleFIN access URL")
    auth: tuple[str, str] | None = None
    if parsed.username or parsed.password:
        auth = (parsed.username or "", parsed.password or "")
        netloc = parsed.hostname or ""
        if parsed.port:
            netloc += f":{parsed.port}"
        parsed = parsed._replace(netloc=netloc)
    return urlunparse(parsed), auth


def fetch_accounts_and_transactions(access_url: str, days: int):
    base_url, auth = _parse_access_url(access_url)
    start_dt = datetime.now(timezone.utc) - timedelta(days=days)
    params = {"start-date": int(start_dt.timestamp()), "pending": 1}
    resp = requests.get(f"{base_url}/accounts", params=params, auth=auth, timeout=60)
    resp.raise_for_status()
    payload = resp.json()

    errors: list[str] = []
    accounts = []
    txns = []
    for a in payload.get("accounts", []):
        accounts.append({
            "id": a["id"],
            "name": a.get("name", ""),
            "institution": (a.get("org") or {}).get("name"),
            "currency": a.get("currency", "USD"),
            "balance": a.get("balance"),
            "balance_date": (
                datetime.fromtimestamp(a["balance-date"], tz=timezone.utc).isoformat()
                if a.get("balance-date") else None
            ),
        })
        for t in a.get("transactions", []):
            # Pending txns from SimpleFIN have `transacted_at` but either no
            # `posted` field or `posted: 0` — the protocol uses 0 as "not yet
            # posted". Falsy in both cases, so `or` falls through to transacted_at.
            # We keep posted_at NOT NULL by using transacted_at; it gets
            # overwritten with the real posted timestamp on the pending→posted
            # UPSERT.
            posted_src = t.get("posted") or t.get("transacted_at")
            if not posted_src:
                msg = f"txn {t.get('id', '?')}: missing both 'posted' and 'transacted_at'; skipping"
                log.warning(msg)
                errors.append(msg)
                continue
            txns.append({
                "id": t["id"],
                "account_id": a["id"],
                "amount": t["amount"],
                "description": t.get("description", ""),
                "posted_at": datetime.fromtimestamp(posted_src, tz=timezone.utc).isoformat(),
                # `pending` reflects the SimpleFIN flag. `has_real_posted` is
                # true only when SimpleFIN provides a truthy `posted` timestamp
                # — protocol uses 0 for "not posted yet," so we check truthiness
                # rather than `is not None`. This is the authoritative signal
                # that the txn has really posted at the bank, even when the
                # `pending: true` flag is still on the payload during the flip
                # moment.
                "pending": bool(t.get("pending", False)),
                "has_real_posted": bool(t.get("posted")),
                "raw_payload": t,
            })

    for e in payload.get("errors") or []:
        errors.append(str(e))
    for e in payload.get("errlist") or []:
        if isinstance(e, dict):
            msg = e.get("msg") or ""
            acct = e.get("account_id") or ""
            errors.append(f"[{acct}] {msg}" if acct else msg)
        else:
            errors.append(str(e))
    return accounts, txns, errors
