"""BRC-29 payment construction and 402 auto-retry flow.

When a BRC-31 authenticated request gets an HTTP 402 response, the server
is requesting payment.  This module:

    1. Parses the 402 response headers for payment requirements.
    2. Derives a payment public key via BRC-42 key derivation.
    3. Builds a P2PKH locking script for that derived key.
    4. Creates a funded transaction via MetaNet Client (``createAction``).
    5. Packages the payment as JSON in the ``x-bsv-payment`` header.
    6. Retries the original request with the payment attached.

Reference implementations:
    - TS SDK: ``AuthFetch.handlePaymentAndRetry()`` + ``createPaymentContext()``
    - Rust:   ``middleware/payment.rs`` ``process_payment()`` (server side)
    - Rust:   ``poc-server/src/lib.rs`` ``handle_paid()`` (server handler)

Protocol:
    The payment JSON sent in the ``x-bsv-payment`` header:
        ``{"derivationPrefix": "...", "derivationSuffix": "...", "transaction": "..."}``
    No ``senderIdentityKey`` field -- identity comes from BRC-31 auth context.
"""

from __future__ import annotations

import json
import os
import base64
import hashlib
import logging
import requests

from lib.metanet import get_public_key, create_action
from lib.auth_request import authenticated_request
from lib.session import Session
from lib.handshake import get_or_create_session

log = logging.getLogger(__name__)

# Payment key derivation protocol ID.
# Matches the TS SDK AuthFetch.createPaymentContext() exactly:
#   protocolID: [2, '3241645161d8']
# The server (poc-server) internalizes via storage.babbage.systems with
# protocol "wallet payment".  The hex string 3241645161d8 is the protocol
# identifier that the wallet maps to "wallet payment" internally.
PAYMENT_PROTOCOL = [2, "3241645161d8"]

# BRC-29 payment protocol version.  Must match server expectation.
PAYMENT_VERSION = "1.0"

# Maximum number of payment retry attempts before giving up.
MAX_PAYMENT_ATTEMPTS = 3

# Header threshold: if the payment JSON exceeds this size, send it in
# the request body instead of the header (matches TS SDK's 6KB threshold).
HEADER_SIZE_THRESHOLD = 6144  # 6KB


class PaymentError(Exception):
    """Raised when payment construction or submission fails."""
    pass


class PaymentRequired:
    """Parsed 402 response data.

    Attributes:
        satoshis:           Amount required in satoshis.
        derivation_prefix:  Server-generated HMAC nonce for key derivation.
        version:            Payment protocol version (should be "1.0").
    """

    def __init__(
        self,
        satoshis: int,
        derivation_prefix: str,
        version: str = PAYMENT_VERSION,
    ):
        self.satoshis = satoshis
        self.derivation_prefix = derivation_prefix
        self.version = version

    def __repr__(self) -> str:
        return (
            f"PaymentRequired(satoshis={self.satoshis}, "
            f"derivation_prefix={self.derivation_prefix[:16]}..., "
            f"version={self.version!r})"
        )


# ---------------------------------------------------------------------------
# 402 Parsing
# ---------------------------------------------------------------------------


def parse_402_response(response: requests.Response) -> PaymentRequired:
    """Parse payment requirements from a 402 response.

    Reads the BRC-29 payment headers:
        - ``x-bsv-payment-version``
        - ``x-bsv-payment-satoshis-required``
        - ``x-bsv-payment-derivation-prefix``

    Args:
        response: HTTP response with status 402.

    Returns:
        ``PaymentRequired`` with the parsed fields.

    Raises:
        PaymentError: if required headers are missing or invalid.
    """
    # Version check
    version = response.headers.get("x-bsv-payment-version")
    if not version:
        raise PaymentError(
            "402 response is missing x-bsv-payment-version header. "
            "The server may not support BRC-29 payments."
        )
    if version != PAYMENT_VERSION:
        raise PaymentError(
            f"Unsupported payment version: server={version!r}, "
            f"client={PAYMENT_VERSION!r}"
        )

    # Satoshis required
    satoshis_str = response.headers.get("x-bsv-payment-satoshis-required")
    if not satoshis_str:
        raise PaymentError(
            "402 response is missing x-bsv-payment-satoshis-required header."
        )
    try:
        satoshis = int(satoshis_str)
    except ValueError:
        raise PaymentError(
            f"Invalid x-bsv-payment-satoshis-required value: {satoshis_str!r}"
        )
    if satoshis <= 0:
        raise PaymentError(
            f"x-bsv-payment-satoshis-required must be > 0, got {satoshis}"
        )

    # Derivation prefix (server-generated HMAC nonce)
    derivation_prefix = response.headers.get("x-bsv-payment-derivation-prefix")
    if not derivation_prefix:
        raise PaymentError(
            "402 response is missing x-bsv-payment-derivation-prefix header."
        )

    payment_req = PaymentRequired(
        satoshis=satoshis,
        derivation_prefix=derivation_prefix,
        version=version,
    )
    log.debug("Parsed 402: %s", payment_req)
    return payment_req


# ---------------------------------------------------------------------------
# Cryptographic helpers
# ---------------------------------------------------------------------------


def hash160(data: bytes) -> bytes:
    """Compute RIPEMD160(SHA256(data)).

    This is the standard Bitcoin hash160 used in P2PKH addresses.

    Args:
        data: Raw bytes to hash (typically a compressed public key).

    Returns:
        20-byte hash.
    """
    sha256_digest = hashlib.sha256(data).digest()
    try:
        # Try the C-extension RIPEMD160 first (available on most systems
        # with OpenSSL compiled with legacy algorithms enabled).
        ripemd160 = hashlib.new("ripemd160")
        ripemd160.update(sha256_digest)
        return ripemd160.digest()
    except ValueError:
        # RIPEMD160 not available in hashlib -- this can happen on some
        # Python builds where OpenSSL has RIPEMD160 disabled (FIPS mode
        # or stripped builds).  Fall back to a pure-Python implementation.
        return _ripemd160_pure(sha256_digest)


def _ripemd160_pure(data: bytes) -> bytes:
    """Pure-Python RIPEMD-160 implementation (fallback).

    This is a minimal, correct RIPEMD-160 implementation used only when
    hashlib doesn't have RIPEMD-160 available.  It follows the original
    specification from Hans Dobbertin, Antoon Bosselaers, and Bart Preneel.
    """
    # Initial hash values
    h0 = 0x67452301
    h1 = 0xEFCDAB89
    h2 = 0x98BADCFE
    h3 = 0x10325476
    h4 = 0xC3D2E1F0

    # Constants
    KL = [0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
    KR = [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

    # Selection of message word
    RL = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
        3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
        1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
        4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
    ]
    RR = [
        5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
        6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
        15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
        8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
        12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
    ]

    # Left rotate amounts
    SL = [
        11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
        7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
        11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
        11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
        9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
    ]
    SR = [
        8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
        9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
        9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
        15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
        8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
    ]

    MASK = 0xFFFFFFFF

    def _rotl(x, n):
        return ((x << n) | (x >> (32 - n))) & MASK

    def _f(j, x, y, z):
        if j < 16:
            return x ^ y ^ z
        elif j < 32:
            return (x & y) | (~x & MASK & z)
        elif j < 48:
            return (x | ~y & MASK) ^ z
        elif j < 64:
            return (x & z) | (y & ~z & MASK)
        else:
            return x ^ (y | ~z & MASK)

    # Pre-processing: padding
    msg = bytearray(data)
    msg_len = len(data) * 8
    msg.append(0x80)
    while len(msg) % 64 != 56:
        msg.append(0x00)
    msg += msg_len.to_bytes(8, byteorder="little")

    # Process each 512-bit block
    for i in range(0, len(msg), 64):
        block = msg[i:i + 64]
        X = [int.from_bytes(block[j:j + 4], "little") for j in range(0, 64, 4)]

        al, bl, cl, dl, el = h0, h1, h2, h3, h4
        ar, br, cr, dr, er = h0, h1, h2, h3, h4

        for j in range(80):
            rnd = j // 16
            # Left
            t = (al + _f(j, bl, cl, dl) + X[RL[j]] + KL[rnd]) & MASK
            t = (_rotl(t, SL[j]) + el) & MASK
            al = el
            el = dl
            dl = _rotl(cl, 10)
            cl = bl
            bl = t
            # Right
            t = (ar + _f(79 - j, br, cr, dr) + X[RR[j]] + KR[rnd]) & MASK
            t = (_rotl(t, SR[j]) + er) & MASK
            ar = er
            er = dr
            dr = _rotl(cr, 10)
            cr = br
            br = t

        t = (h1 + cl + dr) & MASK
        h1 = (h2 + dl + er) & MASK
        h2 = (h3 + el + ar) & MASK
        h3 = (h4 + al + br) & MASK
        h4 = (h0 + bl + cr) & MASK
        h0 = t

    return b"".join(v.to_bytes(4, "little") for v in [h0, h1, h2, h3, h4])


def build_p2pkh_script(pubkey_hex: str) -> str:
    """Build a P2PKH locking script from a hex public key.

    P2PKH script template:
        OP_DUP OP_HASH160 <20-byte-hash> OP_EQUALVERIFY OP_CHECKSIG
        76     a9          14 {hash160}   88              ac

    Args:
        pubkey_hex: Compressed public key as hex string (66 chars).

    Returns:
        Hex-encoded locking script.

    Raises:
        PaymentError: if the public key format is invalid.
    """
    # Validate pubkey format
    if not pubkey_hex or len(pubkey_hex) != 66:
        raise PaymentError(
            f"Invalid public key length: expected 66 hex chars, "
            f"got {len(pubkey_hex) if pubkey_hex else 0}"
        )
    if pubkey_hex[0:2] not in ("02", "03"):
        raise PaymentError(
            f"Invalid compressed public key prefix: {pubkey_hex[:2]!r}. "
            "Expected '02' or '03'."
        )

    try:
        pubkey_bytes = bytes.fromhex(pubkey_hex)
    except ValueError as e:
        raise PaymentError(f"Invalid hex in public key: {e}") from e

    # hash160 = RIPEMD160(SHA256(pubkey))
    pkh = hash160(pubkey_bytes)
    assert len(pkh) == 20

    # OP_DUP OP_HASH160 OP_PUSH20 <hash160> OP_EQUALVERIFY OP_CHECKSIG
    script = b"\x76\xa9\x14" + pkh + b"\x88\xac"
    return script.hex()


# ---------------------------------------------------------------------------
# Payment construction
# ---------------------------------------------------------------------------


def create_payment(
    derivation_prefix: str,
    server_identity_key: str,
    satoshis: int,
    server_url: str = "",
) -> dict:
    """Create a BRC-29 payment.

    Derives a payment key, builds a P2PKH output, creates a transaction
    via MetaNet Client, and packages everything into the payment JSON
    structure expected by the server.

    Args:
        derivation_prefix:  From the server's 402 response header.
        server_identity_key: Server's identity public key (66-char hex).
        satoshis:           Amount to pay.
        server_url:         For the transaction description (cosmetic).

    Returns:
        Dict with keys:
            - ``derivationPrefix``: echoed from the 402 response
            - ``derivationSuffix``: client-generated UUID
            - ``transaction``:      base64-encoded BEEF transaction

    Raises:
        PaymentError: if key derivation, script building, or tx creation fails.
    """
    # Step 1: Generate a random derivation suffix.
    # The storage server requires this to be a valid base64 string.
    # The TS SDK uses a random base64 value (not UUID).
    derivation_suffix = base64.b64encode(os.urandom(32)).decode("ascii")

    log.info(
        "Creating payment: %d sats to %s... (prefix=%s..., suffix=%s)",
        satoshis,
        server_identity_key[:16],
        derivation_prefix[:16],
        derivation_suffix[:8],
    )

    # Step 2: Derive the payment public key.
    # The TS SDK uses:
    #   protocolID: [2, '3241645161d8']
    #   keyID: `${derivationPrefix} ${derivationSuffix}`
    #   counterparty: serverIdentityKey
    key_id = f"{derivation_prefix} {derivation_suffix}"
    try:
        payment_pubkey = get_public_key(
            protocol_id=PAYMENT_PROTOCOL,
            key_id=key_id,
            counterparty=server_identity_key,
            for_self=False,
        )
    except Exception as e:
        raise PaymentError(f"Failed to derive payment public key: {e}") from e

    log.debug("Derived payment pubkey: %s", payment_pubkey)

    # Step 3: Build P2PKH locking script from the derived pubkey.
    locking_script = build_p2pkh_script(payment_pubkey)
    log.debug("P2PKH locking script: %s", locking_script)

    # Step 4: Create the transaction via MetaNet Client.
    # Matches TS SDK AuthFetch.createPaymentContext():
    #   wallet.createAction({ outputs: [{satoshis, lockingScript, ...}], ... })
    description = f"BRC-29 payment: {satoshis} sats"
    if server_url:
        description += f" to {server_url}"

    try:
        result = create_action(
            outputs=[{
                "lockingScript": locking_script,
                "satoshis": satoshis,
                "outputDescription": "BRC-29 payment output",
            }],
            description=description,
            accept_delayed_broadcast=False,
            randomize_outputs=False,
        )
    except Exception as e:
        raise PaymentError(f"Failed to create payment transaction: {e}") from e

    txid = result.get("txid", "unknown")
    tx_bytes = result.get("tx")
    if tx_bytes is None:
        raise PaymentError(
            "createAction returned no transaction data. "
            f"Response: {result}"
        )

    log.info("Payment tx created: txid=%s, size=%d bytes", txid, len(tx_bytes))

    # Step 5: Base64-encode the transaction.
    tx_b64 = base64.b64encode(tx_bytes).decode("ascii")

    # Step 6: Build the payment JSON (camelCase keys to match server expectation).
    # NOTE: no senderIdentityKey -- identity comes from BRC-31 auth context.
    payment = {
        "derivationPrefix": derivation_prefix,
        "derivationSuffix": derivation_suffix,
        "transaction": tx_b64,
    }

    log.debug(
        "Payment JSON: prefix=%s..., suffix=%s, tx_b64_len=%d",
        derivation_prefix[:16],
        derivation_suffix[:8],
        len(tx_b64),
    )
    return payment


# ---------------------------------------------------------------------------
# High-level paid request
# ---------------------------------------------------------------------------


def paid_request(
    method: str,
    url: str,
    headers: dict[str, str] | None = None,
    body: bytes | str | None = None,
    max_payment_attempts: int = MAX_PAYMENT_ATTEMPTS,
) -> requests.Response:
    """Make a BRC-31 authenticated request, handling 402 payment automatically.

    This is the main entry point for interacting with paid endpoints.
    It orchestrates the full flow:

        1. Make an authenticated request via ``authenticated_request()``.
        2. If the server returns 402, parse the payment requirements.
        3. Create a payment transaction.
        4. Retry the original request with the ``x-bsv-payment`` header.
        5. Return the final response.

    The payment is only created on a 402 response.  If the initial request
    succeeds (or fails with a non-402 status), it is returned as-is.

    Args:
        method:    HTTP method (GET, POST, etc.).
        url:       Full URL to request.
        headers:   Optional headers (same restrictions as ``authenticated_request``).
        body:      Optional request body (str or bytes).
        max_payment_attempts: Maximum times to attempt payment (default 3).

    Returns:
        ``requests.Response`` from the final attempt.

    Raises:
        PaymentError: if payment construction/submission fails after all attempts.
        lib.auth_request.AuthRequestError: if the authenticated request itself
            fails at the protocol level.
    """
    if headers is None:
        headers = {}

    # Keep a copy of original headers so retries don't accumulate payment headers.
    original_headers = dict(headers)

    # --- Step 1: Initial authenticated request ---
    log.info("paid_request: %s %s", method, url)
    response = authenticated_request(
        method=method,
        url=url,
        headers=dict(original_headers),
        body=body,
    )

    if response.status_code != 402:
        log.debug(
            "paid_request: initial request returned %d (not 402), done.",
            response.status_code,
        )
        return response

    # --- Step 2: Handle 402 Payment Required ---
    log.info(
        "paid_request: got 402 Payment Required (attempt 0/%d)",
        max_payment_attempts,
    )

    # We need the server identity key from the session for key derivation.
    # Re-derive the server base URL to look up the session.
    from urllib.parse import urlparse
    parsed = urlparse(url)
    server_base = f"{parsed.scheme}://{parsed.netloc}"

    session = get_or_create_session(server_base)
    server_identity_key = session.server_identity_key

    # Also check if the 402 response has the identity key in headers
    # (it should, since the 402 is a signed response from an authenticated session).
    header_identity = response.headers.get("x-bsv-auth-identity-key")
    if header_identity:
        server_identity_key = header_identity

    for attempt in range(1, max_payment_attempts + 1):
        log.info(
            "paid_request: payment attempt %d/%d",
            attempt,
            max_payment_attempts,
        )

        try:
            # Parse 402 requirements (re-parse each time in case server changes them)
            payment_req = parse_402_response(response)
        except PaymentError as e:
            log.error("Failed to parse 402 response: %s", e)
            raise

        try:
            # Create payment
            payment = create_payment(
                derivation_prefix=payment_req.derivation_prefix,
                server_identity_key=server_identity_key,
                satoshis=payment_req.satoshis,
                server_url=server_base,
            )
        except PaymentError as e:
            log.error(
                "Payment creation failed (attempt %d/%d): %s",
                attempt, max_payment_attempts, e,
            )
            if attempt >= max_payment_attempts:
                raise
            continue

        # Build the payment header value
        payment_json = json.dumps(payment, separators=(",", ":"))

        # Determine transport mode (header vs body).
        # Body mode ONLY works when the original request has no body to
        # preserve — otherwise we'd overwrite the application payload
        # (e.g. {"fileSize":...}) with payment JSON.  Most servers
        # (NanoStore, banana-agent) don't support body mode anyway.
        retry_headers = dict(original_headers)
        has_original_body = body is not None and len(body) > 0

        if len(payment_json) > HEADER_SIZE_THRESHOLD and not has_original_body:
            # Large payment, no original body -- send as body.
            log.debug(
                "Payment JSON too large for header (%d bytes), using body transport",
                len(payment_json),
            )
            retry_headers["x-bsv-payment"] = "body"
            retry_body = payment_json.encode("utf-8")
            retry_headers["content-type"] = "application/json"
        else:
            # Normal case -- payment JSON in header.
            # For large payments with an original body, we must use the
            # header even though it's big.  Express/GCP allows headers
            # up to ~80KB; Cloudflare Workers up to 8KB per header.
            if len(payment_json) > HEADER_SIZE_THRESHOLD:
                log.warning(
                    "Payment JSON is %d bytes but body mode unavailable "
                    "(original body present). Sending in header anyway.",
                    len(payment_json),
                )
            retry_headers["x-bsv-payment"] = payment_json
            retry_body = body

        # Retry with payment
        try:
            response = authenticated_request(
                method=method,
                url=url,
                headers=retry_headers,
                body=retry_body,
            )
        except Exception as e:
            log.error(
                "Paid request failed (attempt %d/%d): %s",
                attempt, max_payment_attempts, e,
            )
            if attempt >= max_payment_attempts:
                raise PaymentError(
                    f"Paid request to {url} failed after {attempt} attempts: {e}"
                ) from e
            continue

        if response.status_code == 402:
            # Server still wants payment -- maybe requirements changed.
            log.warning(
                "Server returned 402 again after payment (attempt %d/%d). "
                "Will retry if attempts remain.",
                attempt, max_payment_attempts,
            )
            if attempt >= max_payment_attempts:
                raise PaymentError(
                    f"Paid request to {url} still getting 402 after "
                    f"{attempt} payment attempts. Last response: "
                    f"{response.text[:500]}"
                )
            continue

        # Success (or at least not 402 anymore)
        log.info(
            "paid_request: payment accepted! status=%d (attempt %d/%d)",
            response.status_code, attempt, max_payment_attempts,
        )

        # Auto-detect and internalize refunds in error responses
        if response.status_code >= 400:
            try:
                from lib.refund import parse_refund, process_refund
                resp_body = response.json()
                refund = parse_refund(resp_body)
                if refund:
                    try:
                        refund_result = process_refund(refund)
                        log.info(
                            "Refund auto-internalized: %d sats, accepted=%s",
                            refund.satoshis,
                            refund_result.get("accepted", False),
                        )
                    except Exception as re:
                        log.error("Failed to internalize refund: %s", re)
            except Exception:
                pass  # Response not JSON or no refund — that's fine

        return response

    # Should not reach here, but just in case
    raise PaymentError(
        f"Paid request to {url} exhausted all {max_payment_attempts} attempts."
    )


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    import sys

    logging.basicConfig(
        level=logging.DEBUG,
        format="%(name)s %(levelname)s: %(message)s",
    )

    # Quick test: parse a mock 402, build a P2PKH script
    print("=== hash160 test ===")
    # Known test vector: hash160 of 0x00 should be a specific value
    test_hash = hash160(b"\x00")
    print(f"hash160(0x00) = {test_hash.hex()}")
    assert len(test_hash) == 20

    print("\n=== P2PKH script test ===")
    # Use a dummy compressed pubkey for testing
    dummy_pubkey = "02" + "ab" * 32
    script = build_p2pkh_script(dummy_pubkey)
    print(f"P2PKH script for {dummy_pubkey[:16]}...: {script}")
    assert script.startswith("76a914")
    assert script.endswith("88ac")
    assert len(script) == 50  # 25 bytes * 2 hex chars

    print("\n=== All local tests passed ===")

    if len(sys.argv) > 1 and sys.argv[1] == "--live":
        # Live test against poc-server's /paid endpoint
        print("\n=== Live test: paid_request to poc-server ===")
        poc_url = "https://poc-server.dev-a3e.workers.dev/paid"
        try:
            resp = paid_request("POST", poc_url)
            print(f"Response: HTTP {resp.status_code}")
            print(f"Headers: {dict(resp.headers)}")
            print(f"Body: {resp.text[:500]}")
        except Exception as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
