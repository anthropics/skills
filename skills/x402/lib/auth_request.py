"""Build and send BRC-31 authenticated HTTP requests (General messages).

This module is the main entry point for making authenticated requests.
It orchestrates the full BRC-31 general message flow:

    1. Ensure a session exists (handshake if needed)
    2. Generate per-message nonce + request ID
    3. Parse URL, collect signable headers, prepare body
    4. Serialize the request into BRC-31 binary format
    5. Sign the serialized payload via MetaNet Client wallet
    6. Attach BRC-104 auth headers alongside original headers
    7. Send the HTTP request via ``requests`` library
    8. Return the raw Response (caller handles 200, 402, etc.)

Reference implementations:
    - TS SDK: ``AuthFetch.fetch()`` + ``AuthFetch.serializeRequest()``
    - TS SDK: ``SimplifiedFetchTransport.send()`` (general message branch)
    - Rust:   ``middleware/auth.rs`` verify_message_signature (server side)
"""

from __future__ import annotations

import requests as _requests
from urllib.parse import urlparse

from lib.serialize import serialize_request
from lib.headers import filter_signable_headers, build_auth_headers
from lib.metanet import get_identity_key, create_signature
from lib.nonce import generate_nonce, generate_request_id, nonce_to_base64
from lib.session import Session
from lib.handshake import get_or_create_session


# Protocol ID for BRC-31 general message signatures.
# Matches AUTH_PROTOCOL_ID in both TS SDK and Rust SDK.
AUTH_PROTOCOL = [2, "auth message signature"]


class AuthRequestError(Exception):
    """Raised when an authenticated request fails at the protocol level.

    This does NOT cover HTTP-level errors (4xx, 5xx) from the server.
    Those come back as normal ``requests.Response`` objects for the caller
    to interpret. This exception is for local failures: serialization,
    signing, wallet errors, etc.
    """
    pass


def authenticated_request(
    method: str,
    url: str,
    headers: dict[str, str] | None = None,
    body: bytes | str | None = None,
    session: Session | None = None,
) -> _requests.Response:
    """Make an authenticated BRC-31 request.

    This is the Python equivalent of ``AuthFetch.fetch()`` from the TS SDK.
    It performs the complete signing flow and sends the request. The caller
    is responsible for inspecting the response (status code, headers, body).

    Args:
        method: HTTP method (GET, POST, etc.).
        url: Full URL to request, e.g. "https://example.com/api/resource?q=1".
        headers: Optional extra headers. Only these are allowed (matching
            SimplifiedFetchTransport):
            - ``content-type`` (media-type only is signed; params stripped)
            - ``authorization``
            - ``x-bsv-*`` (excluding ``x-bsv-auth-*``)
            Auth headers (``x-bsv-auth-*``) must NOT be passed here; they
            are generated automatically.
        body: Request body. ``str`` is encoded to UTF-8 bytes; ``bytes``
            used as-is; ``None`` means no body.
        session: Optional existing session. If None, will load from disk
            or perform a handshake to create one.

    Returns:
        ``requests.Response`` object. The caller inspects status, headers,
        and body. Common outcomes:
        - 200: success
        - 402: payment required (caller should use payment.py)
        - 401: session expired or invalid (caller may retry with fresh session)

    Raises:
        AuthRequestError: If the request cannot be constructed or signed
            (wallet unreachable, serialization error, etc.).
        lib.metanet.MetaNetClientError: If the wallet call fails.
    """
    if headers is None:
        headers = {}

    # -----------------------------------------------------------------------
    # 1. Parse URL
    # -----------------------------------------------------------------------
    parsed = urlparse(url)
    server_base = f"{parsed.scheme}://{parsed.netloc}"
    path = parsed.path or None
    query = f"?{parsed.query}" if parsed.query else None

    # -----------------------------------------------------------------------
    # 2. Get or create session (handshake if needed)
    # -----------------------------------------------------------------------
    if session is None:
        try:
            session = get_or_create_session(server_base)
        except Exception as e:
            raise AuthRequestError(
                f"Failed to establish BRC-31 session with {server_base}: {e}"
            ) from e

    # -----------------------------------------------------------------------
    # 3. Body handling
    # -----------------------------------------------------------------------
    # Normalize JSON bodies to compact form (no extra whitespace) so the
    # bytes we sign match what the server will reconstruct via
    # JSON.parse -> JSON.stringify on its side.
    body_bytes: bytes | None = None
    if isinstance(body, str):
        import json as _json
        try:
            body_bytes = _json.dumps(
                _json.loads(body), separators=(",", ":")
            ).encode("utf-8")
        except (_json.JSONDecodeError, ValueError):
            body_bytes = body.encode("utf-8")
    elif isinstance(body, bytes):
        body_bytes = body
    # else: body is None -> body_bytes stays None

    # If body is present but no content-type, default to application/json.
    # This matches the TS SDK behavior where a missing content-type with
    # a body triggers an error; we're slightly more lenient by defaulting.
    if body_bytes is not None and not _has_content_type(headers):
        headers["content-type"] = "application/json"

    # -----------------------------------------------------------------------
    # 4. Generate per-message nonce and request ID
    # -----------------------------------------------------------------------
    msg_nonce_bytes = generate_nonce()
    msg_nonce_b64 = nonce_to_base64(msg_nonce_bytes)

    request_id_bytes = generate_request_id()
    request_id_b64 = nonce_to_base64(request_id_bytes)

    # -----------------------------------------------------------------------
    # 5. Filter and sort signable headers
    # -----------------------------------------------------------------------
    signable_headers = filter_signable_headers(headers)

    # -----------------------------------------------------------------------
    # 6. Serialize the request into BRC-31 binary format
    # -----------------------------------------------------------------------
    try:
        serialized = serialize_request(
            request_id_bytes=request_id_bytes,
            method=method.upper(),
            path=path,
            query=query,
            signable_headers=signable_headers,
            body=body_bytes,
        )
    except Exception as e:
        raise AuthRequestError(f"Failed to serialize request: {e}") from e

    # -----------------------------------------------------------------------
    # 7. Sign the serialized payload
    #
    # key_id format: "{per_message_nonce_b64} {server_session_nonce_b64}"
    # counterparty: server's identity key from the session
    # protocol_id: [2, "auth message signature"]
    # -----------------------------------------------------------------------
    key_id = f"{msg_nonce_b64} {session.server_nonce_b64}"

    try:
        signature = create_signature(
            data=serialized,
            protocol_id=AUTH_PROTOCOL,
            key_id=key_id,
            counterparty=session.server_identity_key,
        )
    except Exception as e:
        raise AuthRequestError(f"Failed to sign request: {e}") from e

    # -----------------------------------------------------------------------
    # 8. Build BRC-104 auth headers
    # -----------------------------------------------------------------------
    try:
        my_identity_key = get_identity_key()
    except Exception as e:
        raise AuthRequestError(f"Failed to get identity key: {e}") from e

    auth_headers = build_auth_headers(
        identity_key=my_identity_key,
        message_type="general",
        nonce_b64=msg_nonce_b64,
        your_nonce_b64=session.server_nonce_b64,
        signature_hex=signature.hex(),
        request_id_b64=request_id_b64,
    )

    # -----------------------------------------------------------------------
    # 9. Merge headers: original + auth (auth takes precedence on conflict)
    # -----------------------------------------------------------------------
    merged_headers = {**headers, **auth_headers}

    # -----------------------------------------------------------------------
    # 10. Send the HTTP request
    # -----------------------------------------------------------------------
    try:
        response = _requests.request(
            method=method.upper(),
            url=url,
            headers=merged_headers,
            data=body_bytes,
            timeout=30,
        )
    except _requests.RequestException as e:
        raise AuthRequestError(f"HTTP request failed: {e}") from e

    return response


def _has_content_type(headers: dict[str, str]) -> bool:
    """Check whether any header key is 'content-type' (case-insensitive)."""
    for key in headers:
        if key.lower() == "content-type":
            return True
    return False
