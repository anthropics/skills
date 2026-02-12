"""BRC-31 header filtering and auth header construction.

This module implements the BRC-104 HTTP header conventions for BRC-31
mutual authentication:

1. filter_signable_headers — determines which headers are included in
   the signed payload for requests (matching SimplifiedFetchTransport
   and the Rust server's extract_signable_headers).

2. build_auth_headers — constructs the x-bsv-auth-* header dict that
   rides alongside a General (authenticated) HTTP request.

3. build_handshake_body — constructs the JSON body for handshake
   messages (initialRequest / initialResponse).

Header filtering rules (from TS SDK and Rust middleware):
    - Include x-bsv-* headers EXCEPT x-bsv-auth-* (auth headers carry
      the signature itself; signing them would be circular).
    - Include the ``authorization`` header.
    - Include the ``content-type`` header, but only the media-type part
      (strip parameters like charset, boundary, etc.).
    - Sort alphabetically by lowercase key.
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# Constants — BRC-104 auth header names
# ---------------------------------------------------------------------------

AUTH_VERSION_HEADER = "x-bsv-auth-version"
AUTH_IDENTITY_KEY_HEADER = "x-bsv-auth-identity-key"
AUTH_MESSAGE_TYPE_HEADER = "x-bsv-auth-message-type"
AUTH_NONCE_HEADER = "x-bsv-auth-nonce"
AUTH_YOUR_NONCE_HEADER = "x-bsv-auth-your-nonce"
AUTH_SIGNATURE_HEADER = "x-bsv-auth-signature"
AUTH_REQUEST_ID_HEADER = "x-bsv-auth-request-id"
AUTH_INITIAL_NONCE_HEADER = "x-bsv-auth-initial-nonce"
AUTH_REQUESTED_CERTIFICATES_HEADER = "x-bsv-auth-requested-certificates"

AUTH_VERSION_VALUE = "0.1"


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def filter_signable_headers(headers: dict[str, str]) -> list[tuple[str, str]]:
    """Filter and sort headers for BRC-31 signature.

    Rules (matching SimplifiedFetchTransport and Rust extract_signable_headers):
    - Include ``x-bsv-*`` headers (excluding ``x-bsv-auth-*``)
    - Include the ``authorization`` header
    - Include the ``content-type`` header (media type only — strip params)
    - Sort alphabetically by key (lowercase)
    - All keys are lowercased in the output

    Args:
        headers: dict of header name -> value.  Keys may be any case.

    Returns:
        Sorted list of ``(lowercase_key, value)`` tuples.
    """
    result: list[tuple[str, str]] = []

    for key, value in headers.items():
        lower = key.lower()

        # Exclude x-bsv-auth-* — these carry the auth metadata itself.
        if lower.startswith("x-bsv-auth-"):
            continue

        # Include any other x-bsv-* header (e.g. x-bsv-payment).
        if lower.startswith("x-bsv-"):
            result.append((lower, value))
            continue

        # Include authorization verbatim.
        if lower == "authorization":
            result.append((lower, value))
            continue

        # Include content-type but strip parameters (e.g. "; charset=utf-8").
        if lower == "content-type":
            media_type = value.split(";")[0].strip()
            result.append((lower, media_type))
            continue

        # All other headers are silently excluded.

    result.sort(key=lambda pair: pair[0])
    return result


def build_auth_headers(
    identity_key: str,
    message_type: str,
    nonce_b64: str,
    your_nonce_b64: str | None = None,
    signature_hex: str = "",
    request_id_b64: str | None = None,
    initial_nonce_b64: str | None = None,
) -> dict[str, str]:
    """Build BRC-31 auth headers dict.

    Args:
        identity_key: 66-char hex compressed public key.
        message_type: ``"initialRequest"``, ``"initialResponse"``, or ``"general"``.
        nonce_b64: base64-encoded nonce for this message.
        your_nonce_b64: base64-encoded peer's nonce (general messages and initialResponse).
        signature_hex: hex-encoded DER signature.
        request_id_b64: base64-encoded request ID (general messages only).
        initial_nonce_b64: base64-encoded initial nonce (initialResponse only).

    Returns:
        Dict of auth header names -> values.  Only headers that have a
        meaningful value are included (no ``None``/empty entries).
    """
    h: dict[str, str] = {
        AUTH_VERSION_HEADER: AUTH_VERSION_VALUE,
        AUTH_IDENTITY_KEY_HEADER: identity_key,
        AUTH_MESSAGE_TYPE_HEADER: message_type,
        AUTH_NONCE_HEADER: nonce_b64,
    }

    if your_nonce_b64 is not None:
        h[AUTH_YOUR_NONCE_HEADER] = your_nonce_b64

    if signature_hex:
        h[AUTH_SIGNATURE_HEADER] = signature_hex

    if request_id_b64 is not None:
        h[AUTH_REQUEST_ID_HEADER] = request_id_b64

    if initial_nonce_b64 is not None:
        h[AUTH_INITIAL_NONCE_HEADER] = initial_nonce_b64

    return h


def build_handshake_body(
    identity_key: str,
    message_type: str,
    nonce_b64: str,
    signature_hex: str = "",
    your_nonce_b64: str | None = None,
    initial_nonce_b64: str | None = None,
) -> dict:
    """Build the JSON body for handshake messages.

    The handshake body mirrors the auth headers as a JSON object.
    Fields that are ``None`` or empty are omitted.

    Args:
        identity_key: 66-char hex compressed public key.
        message_type: ``"initialRequest"`` or ``"initialResponse"``.
        nonce_b64: base64-encoded nonce.
        signature_hex: hex-encoded DER signature (empty string if unsigned).
        your_nonce_b64: peer's nonce (echoed back in initialResponse).
        initial_nonce_b64: initial nonce (initialResponse only).

    Returns:
        Dict suitable for ``json.dumps()``.
    """
    body: dict = {
        "version": AUTH_VERSION_VALUE,
        "messageType": message_type,
        "identityKey": identity_key,
        "nonce": nonce_b64,
    }

    if your_nonce_b64 is not None:
        body["yourNonce"] = your_nonce_b64

    if initial_nonce_b64 is not None:
        body["initialNonce"] = initial_nonce_b64

    if signature_hex:
        body["signature"] = signature_hex

    return body
