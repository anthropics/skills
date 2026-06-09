"""BRC-31 handshake: initialRequest -> initialResponse.

Performs the initial mutual authentication handshake defined by BRC-31.
The client sends an ``initialRequest`` to the server's
``/.well-known/auth`` endpoint and receives an ``initialResponse`` back.

After a successful handshake the client has:
- The server's identity key (66-char hex compressed public key).
- A server nonce and a client nonce for signing subsequent messages.

These are persisted as a :class:`~lib.session.Session` and reused until
the TTL expires.

Protocol details (from ts-sdk Peer.ts ``initiateHandshake``):
    The ``initialRequest`` carries:
        version, messageType="initialRequest", identityKey, initialNonce
    It does NOT carry a signature -- the client hasn't established a
    session yet.

    The ``initialResponse`` carries:
        version, messageType="initialResponse", identityKey,
        initialNonce (server nonce), yourNonce (echoed client nonce),
        signature
"""

from __future__ import annotations

import json
import logging
import requests as http_requests

from lib.metanet import get_identity_key, MetaNetClientError
from lib.nonce import generate_nonce, nonce_to_base64
from lib.session import Session, save_session, load_session
from lib.headers import AUTH_VERSION_VALUE

log = logging.getLogger(__name__)

AUTH_PROTOCOL = [2, "auth message signature"]
HANDSHAKE_PATH = "/.well-known/auth"


class HandshakeError(Exception):
    """Raised when the BRC-31 handshake fails."""
    pass


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def do_handshake(server_url: str) -> Session:
    """Perform a BRC-31 handshake with the server.

    This implements the client side of the BRC-31 initialRequest /
    initialResponse exchange, matching the TS SDK ``Peer.initiateHandshake``
    and the Rust server ``handle_initial_request``.

    Flow:
        1. Generate 32-byte client nonce.
        2. Get our identity key from MetaNet Client.
        3. POST initialRequest JSON to ``{server_url}/.well-known/auth``.
        4. Parse the initialResponse from response body and/or headers.
        5. Extract server identity key and server nonce.
        6. Persist and return a :class:`Session`.

    Args:
        server_url: Base URL of the server (e.g. ``"http://localhost:8787"``).

    Returns:
        :class:`Session` ready for use with authenticated requests.

    Raises:
        HandshakeError: if the handshake fails for any reason.
    """
    server_url = server_url.rstrip("/")

    # --- Step 1: generate client nonce ---
    client_nonce_bytes = generate_nonce()
    client_nonce_b64 = nonce_to_base64(client_nonce_bytes)

    # --- Step 2: get our identity key ---
    try:
        identity_key = get_identity_key()
    except MetaNetClientError as exc:
        raise HandshakeError(
            f"Cannot get identity key from MetaNet Client: {exc}"
        ) from exc

    # --- Step 3: build and send the initialRequest ---
    #
    # The TS SDK Peer.initiateHandshake sends:
    #   { version, messageType: "initialRequest", identityKey, initialNonce }
    #
    # Notably there is NO signature and NO ``nonce`` field (only
    # ``initialNonce``).  We match that exactly.
    body = {
        "version": AUTH_VERSION_VALUE,
        "messageType": "initialRequest",
        "identityKey": identity_key,
        "initialNonce": client_nonce_b64,
    }

    url = f"{server_url}{HANDSHAKE_PATH}"
    log.debug("BRC-31 handshake: POST %s", url)
    log.debug("  identityKey: %s", identity_key)
    log.debug("  initialNonce: %s", client_nonce_b64)

    try:
        resp = http_requests.post(
            url,
            headers={
                "Content-Type": "application/json",
                "Origin": "http://localhost",
            },
            data=json.dumps(body),
            timeout=30,
        )
    except http_requests.ConnectionError as exc:
        raise HandshakeError(
            f"Cannot connect to {url}. Is the server running?"
        ) from exc
    except http_requests.Timeout as exc:
        raise HandshakeError(
            f"Handshake request to {url} timed out."
        ) from exc
    except http_requests.RequestException as exc:
        raise HandshakeError(
            f"HTTP error during handshake with {url}: {exc}"
        ) from exc

    # --- Step 4: check response status ---
    if resp.status_code != 200:
        body_preview = resp.text[:500] if resp.text else "(empty body)"
        raise HandshakeError(
            f"Handshake failed: server returned HTTP {resp.status_code}. "
            f"Body: {body_preview}"
        )

    # --- Step 5: parse the initialResponse ---
    #
    # The server responds with auth data in BOTH the JSON body AND response
    # headers.  We prefer the body (since it is always present for the
    # handshake endpoint) but fall back to headers for resilience.
    server_identity_key, server_nonce_b64 = _parse_initial_response(
        resp, client_nonce_b64
    )

    # --- Step 6: build, persist, and return the session ---
    session = Session(
        server_url=server_url,
        server_identity_key=server_identity_key,
        server_nonce_b64=server_nonce_b64,
        client_nonce_b64=client_nonce_b64,
    )
    path = save_session(session)
    log.info(
        "BRC-31 session established with %s (saved to %s)",
        server_url,
        path,
    )
    return session


def get_or_create_session(server_url: str, ttl: int = 3600) -> Session:
    """Load an existing session or create one via handshake.

    Args:
        server_url: Base URL of the server.
        ttl: Session TTL in seconds (default 1 hour).

    Returns:
        Valid :class:`Session` object (either cached or freshly created).
    """
    server_url = server_url.rstrip("/")
    session = load_session(server_url, ttl=ttl)
    if session is not None:
        log.debug("Reusing existing session for %s", server_url)
        return session
    return do_handshake(server_url)


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------


def _parse_initial_response(
    resp: http_requests.Response,
    client_nonce_b64: str,
) -> tuple[str, str]:
    """Extract server identity key and server nonce from the response.

    The server may put the data in the JSON body, in BRC-104 response
    headers, or both.  We check the body first (canonical), then fall
    back to headers.

    Args:
        resp: The HTTP response from the handshake POST.
        client_nonce_b64: Our client nonce, to validate ``yourNonce``.

    Returns:
        Tuple of ``(server_identity_key, server_nonce_b64)``.

    Raises:
        HandshakeError: if mandatory fields are missing or invalid.
    """
    # --- Try JSON body first ---
    server_identity_key: str | None = None
    server_nonce_b64: str | None = None
    your_nonce: str | None = None

    try:
        data = resp.json()
    except (ValueError, json.JSONDecodeError):
        data = None

    if isinstance(data, dict):
        # The TS SDK Peer.processInitialRequest sends:
        #   identityKey, initialNonce (= server nonce), yourNonce (= client nonce)
        #
        # The server may also include a top-level "nonce" that mirrors
        # initialNonce.  We prefer initialNonce.
        server_identity_key = (
            data.get("identityKey")
            or data.get("identity_key")
        )
        server_nonce_b64 = (
            data.get("initialNonce")
            or data.get("initial_nonce")
            or data.get("nonce")
        )
        your_nonce = (
            data.get("yourNonce")
            or data.get("your_nonce")
        )

    # --- Fall back to BRC-104 response headers ---
    if not server_identity_key:
        server_identity_key = resp.headers.get("x-bsv-auth-identity-key")
    if not server_nonce_b64:
        server_nonce_b64 = (
            resp.headers.get("x-bsv-auth-initial-nonce")
            or resp.headers.get("x-bsv-auth-nonce")
        )
    if not your_nonce:
        your_nonce = resp.headers.get("x-bsv-auth-your-nonce")

    # --- Validate ---
    if not server_identity_key:
        raise HandshakeError(
            "Server initialResponse is missing the server identity key. "
            f"Body: {resp.text[:300]}"
        )
    if not server_nonce_b64:
        raise HandshakeError(
            "Server initialResponse is missing the server nonce "
            "(initialNonce). "
            f"Body: {resp.text[:300]}"
        )

    # Verify the server echoed back our nonce (yourNonce should match our
    # client nonce).  This guards against replays / mix-ups.
    if your_nonce and your_nonce != client_nonce_b64:
        raise HandshakeError(
            f"Server yourNonce mismatch: expected {client_nonce_b64!r}, "
            f"got {your_nonce!r}. Possible MITM or server bug."
        )

    # Verify the server nonce is not empty or obviously invalid.
    if len(server_nonce_b64) < 4:
        raise HandshakeError(
            f"Server nonce is suspiciously short: {server_nonce_b64!r}"
        )

    log.debug("  server identityKey: %s", server_identity_key)
    log.debug("  server nonce: %s", server_nonce_b64)
    log.debug("  yourNonce match: %s", your_nonce == client_nonce_b64)

    return server_identity_key, server_nonce_b64


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys

    logging.basicConfig(level=logging.DEBUG, format="%(message)s")

    url = sys.argv[1] if len(sys.argv) > 1 else "http://localhost:8787"
    print(f"Performing BRC-31 handshake with {url}...")
    try:
        session = do_handshake(url)
        print(f"Success! {session}")
        print(f"  Server key:   {session.server_identity_key}")
        print(f"  Server nonce: {session.server_nonce_b64}")
        print(f"  Client nonce: {session.client_nonce_b64}")
    except HandshakeError as e:
        print(f"Handshake failed: {e}", file=sys.stderr)
        sys.exit(1)
