"""BRC-31 nonce and request ID generation.

BRC-31 authentication uses random nonces at two levels:
- Session nonce: 32 random bytes, generated once per handshake.
- Per-message nonce: 32 random bytes, generated fresh for every request.
- Request ID: 32 random bytes, generated fresh for every request.

All are represented as base64 strings in HTTP headers and JSON bodies.
"""

import os
import base64


def generate_nonce() -> bytes:
    """Generate 32 random bytes for use as a nonce."""
    return os.urandom(32)


def generate_nonce_base64() -> str:
    """Generate a nonce and return as base64 string."""
    return base64.b64encode(generate_nonce()).decode("ascii")


def generate_request_id() -> bytes:
    """Generate 32 random bytes for use as a request ID."""
    return os.urandom(32)


def generate_request_id_base64() -> str:
    """Generate a request ID and return as base64 string."""
    return base64.b64encode(generate_request_id()).decode("ascii")


def nonce_to_base64(nonce_bytes: bytes) -> str:
    """Convert nonce bytes to base64 string."""
    return base64.b64encode(nonce_bytes).decode("ascii")


def nonce_from_base64(nonce_b64: str) -> bytes:
    """Convert base64 string back to nonce bytes."""
    return base64.b64decode(nonce_b64)


if __name__ == "__main__":
    # Demonstrate nonce generation and conversion
    nonce = generate_nonce()
    nonce_b64 = nonce_to_base64(nonce)
    roundtrip = nonce_from_base64(nonce_b64)

    print(f"Nonce (hex):    {nonce.hex()}")
    print(f"Nonce (base64): {nonce_b64}")
    print(f"Roundtrip OK:   {nonce == roundtrip}")
    print(f"Length (bytes):  {len(nonce)}")
    print()

    # Generate convenience base64 versions directly
    print(f"Random nonce:      {generate_nonce_base64()}")
    print(f"Random request ID: {generate_request_id_base64()}")
