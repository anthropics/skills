"""MetaNet Client HTTP wrapper.

Provides a Python interface to the MetaNet Client wallet application
running locally on macOS. MetaNet Client implements the BRC-100 wallet
interface and exposes it via HTTP at localhost:3321.

All methods make synchronous HTTP calls using the requests library.
"""

import requests
import json


METANET_URL = "http://localhost:3321"

COMMON_HEADERS = {
    "Origin": "http://localhost",
    "Content-Type": "application/json",
}


class MetaNetClientError(Exception):
    """Raised when MetaNet Client returns an error or is unreachable."""
    pass


def _call(method_name: str, params: dict) -> dict:
    """Make a POST request to MetaNet Client.

    Args:
        method_name: API method (e.g. "getPublicKey", "createSignature").
            This becomes the URL path: POST http://localhost:3321/{method_name}
        params: JSON body params to send.

    Returns:
        Parsed JSON response dict.

    Raises:
        MetaNetClientError: if the request fails, times out, or the
            wallet returns an error response.
    """
    url = f"{METANET_URL}/{method_name}"
    try:
        resp = requests.post(
            url,
            headers=COMMON_HEADERS,
            json=params,
            timeout=30,
        )
    except requests.ConnectionError as e:
        raise MetaNetClientError(
            f"Cannot connect to MetaNet Client at {METANET_URL}. "
            "Is the application running?"
        ) from e
    except requests.Timeout as e:
        raise MetaNetClientError(
            f"MetaNet Client request to /{method_name} timed out. "
            "The wallet may be waiting for user approval."
        ) from e
    except requests.RequestException as e:
        raise MetaNetClientError(
            f"HTTP error calling MetaNet Client /{method_name}: {e}"
        ) from e

    # Parse the response body
    try:
        data = resp.json()
    except (json.JSONDecodeError, ValueError) as e:
        raise MetaNetClientError(
            f"MetaNet Client /{method_name} returned invalid JSON "
            f"(HTTP {resp.status_code}): {resp.text[:200]}"
        ) from e

    # Check for error responses from the wallet
    if not resp.ok:
        error_msg = data.get("message") or data.get("error") or resp.text[:200]
        raise MetaNetClientError(
            f"MetaNet Client /{method_name} returned HTTP {resp.status_code}: "
            f"{error_msg}"
        )

    # Some wallet errors come back as 200 with an error field
    if isinstance(data, dict) and data.get("error"):
        raise MetaNetClientError(
            f"MetaNet Client /{method_name} error: {data['error']}"
        )

    return data


def get_identity_key() -> str:
    """Get the wallet's identity public key (66-char hex compressed).

    Calls POST /getPublicKey with {"identityKey": true}.

    Returns:
        Hex public key string, e.g. "03abc..."
    """
    result = _call("getPublicKey", {"identityKey": True})
    pubkey = result.get("publicKey")
    if not pubkey or not isinstance(pubkey, str):
        raise MetaNetClientError(
            f"Unexpected getPublicKey response (missing 'publicKey'): {result}"
        )
    return pubkey


def get_public_key(
    protocol_id: list,
    key_id: str,
    counterparty: str,
    for_self: bool = False,
) -> str:
    """Derive a public key via BRC-42 key derivation.

    Calls POST /getPublicKey with protocol, keyID, and counterparty params.

    Args:
        protocol_id: Protocol identifier, e.g. [2, "auth message signature"]
            or [2, "wallet payment"]. The first element is the security level
            (integer), the second is the protocol name (string).
        key_id: String key identifier, e.g. "{nonce1} {nonce2}" for auth
            or "{derivationPrefix} {derivationSuffix}" for payments.
        counterparty: Hex public key of the other party (66-char compressed).
        for_self: If True, derive for self instead of counterparty.

    Returns:
        Hex public key string (66-char compressed).
    """
    result = _call("getPublicKey", {
        "protocolID": protocol_id,
        "keyID": key_id,
        "counterparty": counterparty,
        "forSelf": for_self,
    })
    pubkey = result.get("publicKey")
    if not pubkey or not isinstance(pubkey, str):
        raise MetaNetClientError(
            f"Unexpected getPublicKey response (missing 'publicKey'): {result}"
        )
    return pubkey


def create_signature(
    data: bytes,
    protocol_id: list,
    key_id: str,
    counterparty: str,
) -> bytes:
    """Sign data with a derived key via BRC-42 + ECDSA.

    Calls POST /createSignature. MetaNet Client expects the data as a JSON
    number array [0-255] and returns the signature as a JSON number array.

    Args:
        data: Raw bytes to sign (the serialized message payload).
        protocol_id: Protocol identifier, e.g. [2, "auth message signature"].
        key_id: String key identifier, e.g. "{nonce1} {nonce2}".
        counterparty: Hex public key of the other party (66-char compressed).

    Returns:
        Signature as raw bytes (DER-encoded ECDSA signature).
    """
    # Convert bytes to JSON number array for the wallet
    data_array = list(data)

    result = _call("createSignature", {
        "data": data_array,
        "protocolID": protocol_id,
        "keyID": key_id,
        "counterparty": counterparty,
    })

    sig_array = result.get("signature")
    if sig_array is None:
        raise MetaNetClientError(
            f"Unexpected createSignature response (missing 'signature'): {result}"
        )
    if not isinstance(sig_array, list):
        raise MetaNetClientError(
            f"Unexpected createSignature response ('signature' is not an array): "
            f"{type(sig_array)}"
        )

    # Convert JSON number array back to bytes
    return bytes(sig_array)


def create_action(
    outputs: list[dict],
    description: str,
    accept_delayed_broadcast: bool = False,
    randomize_outputs: bool = True,
) -> dict:
    """Create a transaction via MetaNet Client.

    Calls POST /createAction. The wallet builds, signs, and (optionally)
    broadcasts a transaction with the specified outputs.

    Args:
        outputs: List of output dicts, each with:
            - "lockingScript": hex-encoded locking script (e.g. P2PKH)
            - "satoshis": integer amount in satoshis
        description: Human-readable description of the transaction purpose.
        accept_delayed_broadcast: If False (default), broadcast immediately.
            If True, the wallet may delay broadcasting.
        randomize_outputs: If True (default), wallet may reorder outputs.
            Set to False for BRC-29 payments to ensure payment is at index 0.

    Returns:
        Dict with at minimum:
            - "txid": transaction ID hex string
            - "tx": raw transaction as bytes (converted from JSON number array)
            - other fields the wallet may include (e.g. "sendWithResults")

    Note:
        The wallet returns "tx" as a JSON number array. This function converts
        it to bytes. For BRC-29 payments, the caller should base64-encode the
        tx bytes for the x-bsv-payment header.
    """
    result = _call("createAction", {
        "description": description,
        "outputs": outputs,
        "options": {
            "acceptDelayedBroadcast": accept_delayed_broadcast,
            "randomizeOutputs": randomize_outputs,
        },
    })

    if "txid" not in result:
        raise MetaNetClientError(
            f"Unexpected createAction response (missing 'txid'): {result}"
        )

    # Convert tx from JSON number array to bytes
    tx_array = result.get("tx")
    if isinstance(tx_array, list):
        result["tx"] = bytes(tx_array)
    elif tx_array is not None:
        raise MetaNetClientError(
            f"Unexpected createAction response ('tx' is not an array): "
            f"{type(tx_array)}"
        )

    return result


def internalize_action(
    tx_bytes: bytes,
    outputs: list,
    description: str = "Incoming payment",
) -> dict:
    """Internalize an incoming transaction into the wallet.

    This is the receiving side of a BRC-29 payment. The wallet records
    the specified outputs as owned, allowing the user to spend them later.

    Used for refunds: when a server returns a payment after failing to
    deliver a service.

    Args:
        tx_bytes: Raw transaction bytes (BEEF format).
        outputs: List of output specs, each with:
            - "outputIndex": int (which output in the tx belongs to us)
            - "protocol": "wallet payment"
            - "paymentRemittance": {
                "derivationPrefix": str,
                "derivationSuffix": str,
                "senderIdentityKey": str (66-char hex, the PAYER's key)
              }
        description: Human-readable description (min 5 chars).

    Returns:
        Dict with "accepted": bool and possibly other fields.

    Raises:
        MetaNetClientError: if the wallet rejects the internalization.
    """
    result = _call("internalizeAction", {
        "tx": list(tx_bytes),       # JSON number array, same as createAction
        "outputs": outputs,
        "description": description,
    })
    return result
