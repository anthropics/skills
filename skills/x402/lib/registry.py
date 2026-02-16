"""Agent name registry — resolves short names to full URLs via x402agency.com."""
import json
import os
import time

import requests

REGISTRY_URL = "https://x402agency.com/.well-known/agents"

_CACHE_DIR = os.path.join(os.path.expanduser("~"), ".local", "share", "brc31-sessions")
_CACHE_FILE = os.path.join(_CACHE_DIR, "registry.json")
_TTL_SECONDS = 300  # 5 minutes


def _load_registry() -> dict:
    """Fetch the agent registry from REGISTRY_URL, caching to disk.

    On fetch failure, falls back to a cached copy (even if expired).
    Raises RuntimeError if fetch fails and no cache exists.
    """
    # Try to fetch fresh data
    try:
        resp = requests.get(REGISTRY_URL, timeout=10)
        resp.raise_for_status()
        data = resp.json()
        data["_fetched_at"] = time.time()

        # Write cache
        os.makedirs(_CACHE_DIR, exist_ok=True)
        with open(_CACHE_FILE, "w") as f:
            json.dump(data, f)

        return data
    except Exception:
        pass

    # Fetch failed — try cache (even if expired)
    if os.path.exists(_CACHE_FILE):
        with open(_CACHE_FILE, "r") as f:
            return json.load(f)

    raise RuntimeError(
        f"Could not fetch agent registry from {REGISTRY_URL} "
        "and no local cache exists."
    )


def _get_registry() -> dict:
    """Return the registry, using the cache if fresh enough."""
    if os.path.exists(_CACHE_FILE):
        try:
            with open(_CACHE_FILE, "r") as f:
                cached = json.load(f)
            fetched_at = cached.get("_fetched_at", 0)
            if time.time() - fetched_at < _TTL_SECONDS:
                return cached
        except (json.JSONDecodeError, OSError):
            pass

    return _load_registry()


def resolve(identifier: str) -> str:
    """Resolve an agent identifier to a full URL.

    If *identifier* starts with ``http://`` or ``https://``, it is returned
    as-is.  Otherwise the first ``/`` splits it into (name, path) and the
    name is looked up in the registry.

    Returns the full URL (``agent_url + "/" + path`` when a path is present).
    Raises ``ValueError`` if the name is not found.
    """
    if identifier.startswith("http://") or identifier.startswith("https://"):
        return identifier

    # Split on first "/" to separate name from path
    if "/" in identifier:
        name, path = identifier.split("/", 1)
    else:
        name = identifier
        path = ""

    reg = _get_registry()
    agents = reg.get("agents", [])

    for agent in agents:
        if agent.get("name", "").lower() == name.lower():
            base = agent["url"].rstrip("/")
            if path:
                return f"{base}/{path}"
            return base

    available = [a.get("name", "?") for a in agents]
    raise ValueError(
        f"Agent '{name}' not found in registry. "
        f"Available: {', '.join(available)}"
    )


def resolve_x402_info(identifier: str) -> str:
    """Resolve an identifier to its x402-info manifest URL.

    For agents with an ``x402_info`` field in the registry, returns that URL
    directly (e.g. a hosted manifest on x402agency.com for third-party services).
    Otherwise falls back to ``{agent_url}/.well-known/x402-info``.

    Full URLs are treated as base URLs and get ``/.well-known/x402-info``
    appended.
    """
    if identifier.startswith("http://") or identifier.startswith("https://"):
        return f"{identifier.rstrip('/')}/.well-known/x402-info"

    name = identifier.split("/")[0] if "/" in identifier else identifier

    reg = _get_registry()
    for agent in reg.get("agents", []):
        if agent.get("name", "").lower() == name.lower():
            return agent.get(
                "x402_info",
                f"{agent['url'].rstrip('/')}/.well-known/x402-info",
            )

    available = [a.get("name", "?") for a in reg.get("agents", [])]
    raise ValueError(
        f"Agent '{name}' not found in registry. "
        f"Available: {', '.join(available)}"
    )


def list_agents() -> list:
    """Return all agents from the registry."""
    reg = _get_registry()
    return reg.get("agents", [])
