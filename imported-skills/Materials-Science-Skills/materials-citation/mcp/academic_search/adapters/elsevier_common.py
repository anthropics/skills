"""Shared Elsevier adapter helpers."""

from __future__ import annotations

import os
import re
from typing import Any, Callable

import httpx

from .base import AdapterDisabled, AdapterError, get_response_with_retries


ELSEVIER_STATUS_HINTS = {
    401: "authentication failed; check the API key.",
    403: "access forbidden; check API entitlement or institution token.",
    429: "rate limit exceeded; retry later or reduce request volume.",
}


def require_api_key(env_var: str, source: str) -> str:
    key = os.getenv(env_var, "").strip()
    if not key:
        raise AdapterDisabled(f"{source} skipped because {env_var} is not set.")
    return key


def elsevier_headers(api_key: str, *, insttoken: str | None = None) -> dict[str, str]:
    headers = {"X-ELS-APIKey": api_key, "Accept": "application/json"}
    token = insttoken if insttoken is not None else os.getenv("ELSEVIER_INSTTOKEN", "").strip()
    if token:
        headers["X-ELS-Insttoken"] = token
    return headers


def get_elsevier_json(
    source: str,
    url: str,
    *,
    params: dict[str, Any] | None = None,
    headers: dict[str, str] | None = None,
    timeout: float = 20.0,
    getter: Callable[..., Any] | None = None,
) -> dict[str, Any]:
    getter = getter or get_response_with_retries
    try:
        response = getter(url, params=params, headers=headers, timeout=timeout)
        if response.status_code in ELSEVIER_STATUS_HINTS:
            raise AdapterError(f"{source} returned {response.status_code}: {ELSEVIER_STATUS_HINTS[response.status_code]}")
        response.raise_for_status()
        return response.json()
    except AdapterError:
        raise
    except httpx.HTTPError as exc:
        status = getattr(getattr(exc, "response", None), "status_code", None)
        if status in ELSEVIER_STATUS_HINTS:
            raise AdapterError(f"{source} returned {status}: {ELSEVIER_STATUS_HINTS[status]}") from exc
        raise AdapterError(f"{source} request failed: {exc}") from exc


def year_from_cover_date(value: Any) -> int | None:
    match = re.search(r"\d{4}", str(value or ""))
    return int(match.group(0)) if match else None


def int_or_none(value: Any) -> int | None:
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def creator_names(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value] if value else []
    if isinstance(value, list):
        names = []
        for item in value:
            if isinstance(item, dict):
                name = item.get("$") or item.get("name") or item.get("preferred-name", {}).get("surname")
                if name:
                    names.append(str(name))
            elif item:
                names.append(str(item))
        return names
    return []
