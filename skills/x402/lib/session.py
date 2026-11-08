"""BRC-31 session persistence.

Stores BRC-31 sessions per-server so we can reuse them without
re-handshaking. Sessions are saved as JSON files in
~/.local/share/brc31-sessions/, keyed by a hash of the server URL.

Design decisions:
- XDG data dir pattern (~/.local/share/)
- File named by first 16 hex chars of SHA256(server_url)
- JSON format for easy debugging/inspection
- Default 1 hour TTL; expired sessions auto-cleaned on load
"""

import json
import hashlib
import time
from pathlib import Path


SESSION_DIR = Path.home() / ".local" / "share" / "brc31-sessions"
DEFAULT_TTL = 3600  # 1 hour


class Session:
    """A BRC-31 session with a specific server."""

    def __init__(
        self,
        server_url: str,
        server_identity_key: str,
        server_nonce_b64: str,
        client_nonce_b64: str,
        timestamp: float | None = None,
    ):
        self.server_url = server_url
        self.server_identity_key = server_identity_key
        self.server_nonce_b64 = server_nonce_b64
        self.client_nonce_b64 = client_nonce_b64
        self.timestamp = timestamp or time.time()

    def is_expired(self, ttl: int = DEFAULT_TTL) -> bool:
        """Check whether this session has exceeded its TTL."""
        return time.time() - self.timestamp > ttl

    def to_dict(self) -> dict:
        """Serialize session to a plain dict."""
        return {
            "server_url": self.server_url,
            "server_identity_key": self.server_identity_key,
            "server_nonce_b64": self.server_nonce_b64,
            "client_nonce_b64": self.client_nonce_b64,
            "timestamp": self.timestamp,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Session":
        """Deserialize a session from a plain dict."""
        return cls(
            server_url=d["server_url"],
            server_identity_key=d["server_identity_key"],
            server_nonce_b64=d["server_nonce_b64"],
            client_nonce_b64=d["client_nonce_b64"],
            timestamp=d.get("timestamp", 0),
        )

    def __repr__(self) -> str:
        age = time.time() - self.timestamp
        return (
            f"Session(server_url={self.server_url!r}, "
            f"server_identity_key={self.server_identity_key[:16]}..., "
            f"age={age:.0f}s)"
        )


def _session_path(server_url: str) -> Path:
    """Get the file path for a session, keyed by URL hash."""
    url_hash = hashlib.sha256(server_url.encode()).hexdigest()[:16]
    return SESSION_DIR / f"{url_hash}.json"


def save_session(session: Session) -> Path:
    """Save a session to disk. Returns the file path."""
    SESSION_DIR.mkdir(parents=True, exist_ok=True)
    path = _session_path(session.server_url)
    path.write_text(json.dumps(session.to_dict(), indent=2))
    return path


def load_session(server_url: str, ttl: int = DEFAULT_TTL) -> Session | None:
    """Load a session from disk. Returns None if not found or expired."""
    path = _session_path(server_url)
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text())
        session = Session.from_dict(data)
        if session.is_expired(ttl):
            path.unlink(missing_ok=True)
            return None
        return session
    except (json.JSONDecodeError, KeyError):
        path.unlink(missing_ok=True)
        return None


def clear_session(server_url: str) -> bool:
    """Delete a stored session. Returns True if deleted."""
    path = _session_path(server_url)
    if path.exists():
        path.unlink()
        return True
    return False


def clear_all_sessions() -> int:
    """Delete all stored sessions. Returns count deleted."""
    if not SESSION_DIR.exists():
        return 0
    count = 0
    for f in SESSION_DIR.glob("*.json"):
        f.unlink()
        count += 1
    return count


if __name__ == "__main__":
    from lib.nonce import generate_nonce_base64

    url = "https://poc-server.dev-a3e.workers.dev"
    identity_key = "02ce71d2f3a5a863ab5f2f12e52fdbaea2fba5ae9a212ac585dbb71608e218e40b"

    # Create a session
    session = Session(
        server_url=url,
        server_identity_key=identity_key,
        server_nonce_b64=generate_nonce_base64(),
        client_nonce_b64=generate_nonce_base64(),
    )
    print(f"Created:  {session}")
    print(f"Expired:  {session.is_expired()}")

    # Save it
    path = save_session(session)
    print(f"Saved to: {path}")

    # Load it back
    loaded = load_session(url)
    assert loaded is not None
    print(f"Loaded:   {loaded}")
    print(f"Match:    {loaded.server_nonce_b64 == session.server_nonce_b64}")

    # Clear it
    deleted = clear_session(url)
    print(f"Cleared:  {deleted}")

    # Verify it is gone
    gone = load_session(url)
    print(f"Gone:     {gone is None}")
