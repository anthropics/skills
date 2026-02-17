"""
BRC-31 HTTP request/response binary serialization.

Matches the wire format used by:
  - TS SDK: SimplifiedFetchTransport.deserializeRequestPayload() (server reads)
  - TS SDK: AuthFetch.serializeRequest() (client writes)
  - Rust:   cloudflare.rs build_request_payload() / HttpResponseData::to_payload()

Binary format — Request:
    [request_id: raw 32 bytes]
    [method: varint_len + utf8]
    [path: varint_len + utf8, or EMPTY_SENTINEL]
    [query: varint_len + utf8, or EMPTY_SENTINEL]
    [headers: varint_count + sorted pairs]
    [body: varint_len + bytes, or EMPTY_SENTINEL]

Binary format — Response:
    [request_id: raw 32 bytes]
    [status_code: varint]
    [headers: varint_count + sorted pairs]
    [body: varint_len + bytes, or EMPTY_SENTINEL]

EMPTY_SENTINEL is 9 bytes of 0xFF, equivalent to writeVarIntNum(-1) in the
TS SDK. It signals "missing/empty" for optional fields (path, query, body).
"""

import struct
from io import BytesIO


class Writer:
    """Minimal Bitcoin varint writer (inline, no external deps)."""

    def __init__(self):
        self._buf = BytesIO()

    def write(self, data: bytes) -> None:
        self._buf.write(data)

    def write_var_int_num(self, n: int) -> None:
        """Write a Bitcoin-style variable-length integer."""
        if n < 0:
            raise ValueError("Negative varint not supported; use EMPTY_SENTINEL directly")
        if n <= 252:
            self._buf.write(struct.pack('<B', n))
        elif n <= 0xFFFF:
            self._buf.write(b'\xfd')
            self._buf.write(struct.pack('<H', n))
        elif n <= 0xFFFFFFFF:
            self._buf.write(b'\xfe')
            self._buf.write(struct.pack('<I', n))
        else:
            self._buf.write(b'\xff')
            self._buf.write(struct.pack('<Q', n))

    def to_bytes(self) -> bytes:
        return self._buf.getvalue()


class Reader:
    """Minimal Bitcoin varint reader (inline, no external deps)."""

    def __init__(self, data: bytes):
        self._buf = BytesIO(data)
        self._data = data

    def read(self, n: int) -> bytes:
        result = self._buf.read(n)
        if len(result) != n:
            raise ValueError(f"Expected {n} bytes, got {len(result)}")
        return result

    def read_var_int_num(self) -> int:
        """Read a Bitcoin-style variable-length integer."""
        first = self._buf.read(1)
        if not first:
            raise ValueError("Unexpected end of data reading varint")
        b = first[0]
        if b <= 252:
            return b
        elif b == 0xfd:
            return struct.unpack('<H', self._buf.read(2))[0]
        elif b == 0xfe:
            return struct.unpack('<I', self._buf.read(4))[0]
        else:  # 0xff
            return struct.unpack('<Q', self._buf.read(8))[0]

    def tell(self) -> int:
        return self._buf.tell()

    def seek(self, pos: int) -> None:
        self._buf.seek(pos)

    def eof(self) -> bool:
        """Return True if the read position is at end of data."""
        return self._buf.tell() >= len(self._data)


# 9 bytes of 0xFF — the "missing/empty" sentinel.
# Produced by TS Writer.writeVarIntNum(-1) which encodes -1 as
# unsigned 0xFFFFFFFFFFFFFFFF in the 0xFF + 8-byte-LE varint form.
EMPTY_SENTINEL = b'\xff' * 9


def _write_varint_bytes(writer: Writer, data: bytes) -> None:
    """Write a varint-prefixed byte string to the writer."""
    writer.write_var_int_num(len(data))
    writer.write(data)


def _write_optional_string(writer: Writer, value: str | None) -> None:
    """Write a string field, or EMPTY_SENTINEL if missing/empty."""
    if value is None or len(value) == 0:
        writer.write(EMPTY_SENTINEL)
    else:
        encoded = value.encode('utf-8')
        _write_varint_bytes(writer, encoded)


def _write_optional_bytes(writer: Writer, data: bytes | None) -> None:
    """Write a body field, or EMPTY_SENTINEL if missing/empty."""
    if data is None or len(data) == 0:
        writer.write(EMPTY_SENTINEL)
    else:
        _write_varint_bytes(writer, data)


def _write_headers(writer: Writer, headers: list[tuple[str, str]]) -> None:
    """Write varint header count followed by each (key, value) pair."""
    writer.write_var_int_num(len(headers))
    for key, value in headers:
        key_bytes = key.encode('utf-8')
        _write_varint_bytes(writer, key_bytes)
        val_bytes = value.encode('utf-8')
        _write_varint_bytes(writer, val_bytes)


def serialize_request(
    request_id_bytes: bytes,
    method: str,
    path: str | None,
    query: str | None,
    signable_headers: list[tuple[str, str]],
    body: bytes | None,
) -> bytes:
    """Serialize an HTTP request into BRC-31 binary format for signing.

    This matches the TS SDK's AuthFetch.serializeRequest() and the Rust
    cloudflare.rs build_request_payload() exactly.

    Args:
        request_id_bytes: 32 random bytes (NOT base64-encoded, raw bytes).
        method: HTTP method string, e.g. "POST".
        path: URL path, e.g. "/paid", or None/empty for EMPTY_SENTINEL.
        query: URL query string, e.g. "?q=test", or None/empty for EMPTY_SENTINEL.
        signable_headers: Pre-sorted list of (lowercase_key, value) tuples.
            Only x-bsv-* (excluding x-bsv-auth-*), content-type (media type only),
            and authorization headers should be included. Must be sorted
            alphabetically by key before passing in.
        body: Request body bytes, or None for EMPTY_SENTINEL.

    Returns:
        Binary serialized payload ready for signing.
    """
    if len(request_id_bytes) != 32:
        raise ValueError(f"request_id_bytes must be exactly 32 bytes, got {len(request_id_bytes)}")

    w = Writer()

    # 1. Request ID — raw 32 bytes, NOT varint-prefixed
    w.write(request_id_bytes)

    # 2. Method — always present, varint-prefixed UTF-8
    method_bytes = method.encode('utf-8')
    _write_varint_bytes(w, method_bytes)

    # 3. Path — varint-prefixed string, or EMPTY_SENTINEL
    _write_optional_string(w, path)

    # 4. Query — varint-prefixed string, or EMPTY_SENTINEL
    _write_optional_string(w, query)

    # 5. Headers — varint count + sorted pairs
    _write_headers(w, signable_headers)

    # 6. Body — varint-prefixed bytes, or EMPTY_SENTINEL
    _write_optional_bytes(w, body)

    return w.to_bytes()


def serialize_response(
    request_id_bytes: bytes,
    status_code: int,
    signable_headers: list[tuple[str, str]],
    body: bytes | None,
) -> bytes:
    """Serialize an HTTP response into BRC-31 binary format for verification.

    This matches the TS SDK's SimplifiedFetchTransport response payload
    construction (lines 172-223) and the Rust HttpResponseData::to_payload().

    Args:
        request_id_bytes: 32 bytes from the original request (raw bytes).
        status_code: HTTP status code, e.g. 200, 402.
        signable_headers: Pre-sorted list of (lowercase_key, value) tuples.
            Only x-bsv-* (excluding x-bsv-auth-*) and authorization headers
            should be included, sorted alphabetically by key.
        body: Response body bytes, or None for EMPTY_SENTINEL.

    Returns:
        Binary serialized payload ready for signature verification.
    """
    if len(request_id_bytes) != 32:
        raise ValueError(f"request_id_bytes must be exactly 32 bytes, got {len(request_id_bytes)}")

    w = Writer()

    # 1. Request ID — raw 32 bytes
    w.write(request_id_bytes)

    # 2. Status code — as varint (replaces method field in request format)
    w.write_var_int_num(status_code)

    # 3. Headers — varint count + sorted pairs
    _write_headers(w, signable_headers)

    # 4. Body — varint-prefixed bytes, or EMPTY_SENTINEL
    _write_optional_bytes(w, body)

    return w.to_bytes()


def _is_empty_sentinel(data: bytes, offset: int) -> bool:
    """Check if 9 bytes starting at offset are all 0xFF."""
    if offset + 9 > len(data):
        return False
    return data[offset:offset + 9] == EMPTY_SENTINEL


def deserialize_request(payload: bytes) -> dict:
    """Deserialize a BRC-31 request payload back into components.

    This matches the TS SDK's SimplifiedFetchTransport.deserializeRequestPayload().

    The TS Reader.readVarIntNum(signed=True) interprets the 9-byte sentinel
    (0xFF * 9) as -1. The Python py-sdk Reader reads it as unsigned, yielding
    a huge number. We handle this by checking for the sentinel before reading.

    Args:
        payload: Raw binary payload bytes.

    Returns:
        Dict with keys: request_id, method, path, query, headers, body.
    """
    r = Reader(payload)

    # 1. Request ID — raw 32 bytes
    request_id = r.read(32)

    # 2. Method — varint-prefixed string
    method_len = r.read_var_int_num()
    method = r.read(method_len).decode('utf-8') if method_len and method_len > 0 else 'GET'

    # 3. Path — check for sentinel first
    pos_before = r.tell()
    if _is_empty_sentinel(payload, pos_before):
        r.seek(pos_before + 9)
        path = ''
    else:
        path_len = r.read_var_int_num()
        path = r.read(path_len).decode('utf-8') if path_len and path_len > 0 else ''

    # 4. Query — check for sentinel first
    pos_before = r.tell()
    if _is_empty_sentinel(payload, pos_before):
        r.seek(pos_before + 9)
        query = ''
    else:
        query_len = r.read_var_int_num()
        query = r.read(query_len).decode('utf-8') if query_len and query_len > 0 else ''

    # 5. Headers
    headers = {}
    n_headers = r.read_var_int_num()
    if n_headers and n_headers > 0:
        for _ in range(n_headers):
            key_len = r.read_var_int_num()
            key = r.read(key_len).decode('utf-8')
            val_len = r.read_var_int_num()
            value = r.read(val_len).decode('utf-8')
            headers[key] = value

    # 6. Body — check for sentinel first
    pos_before = r.tell()
    if _is_empty_sentinel(payload, pos_before):
        r.seek(pos_before + 9)
        body = None
    else:
        body_len = r.read_var_int_num()
        body = r.read(body_len) if body_len and body_len > 0 else None

    return {
        'request_id': request_id,
        'method': method,
        'path': path,
        'query': query,
        'headers': headers,
        'body': body,
    }


def deserialize_response(payload: bytes) -> dict:
    """Deserialize a BRC-31 response payload back into components.

    Args:
        payload: Raw binary payload bytes.

    Returns:
        Dict with keys: request_id, status_code, headers, body.
    """
    r = Reader(payload)

    # 1. Request ID — raw 32 bytes
    request_id = r.read(32)

    # 2. Status code — varint
    status_code = r.read_var_int_num()

    # 3. Headers
    headers = {}
    n_headers = r.read_var_int_num()
    if n_headers and n_headers > 0:
        for _ in range(n_headers):
            key_len = r.read_var_int_num()
            key = r.read(key_len).decode('utf-8')
            val_len = r.read_var_int_num()
            value = r.read(val_len).decode('utf-8')
            headers[key] = value

    # 4. Body — check for sentinel first
    pos_before = r.tell()
    if _is_empty_sentinel(payload, pos_before):
        r.seek(pos_before + 9)
        body = None
    else:
        body_len = r.read_var_int_num()
        body = r.read(body_len) if body_len and body_len > 0 else None

    return {
        'request_id': request_id,
        'status_code': status_code,
        'headers': headers,
        'body': body,
    }
