"""Tests for webapp-testing with_server.is_server_ready."""

import socket
import sys
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from with_server import is_server_ready


def _start_listener(port: int) -> socket.socket:
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(("127.0.0.1", port))
    s.listen(1)
    return s


def _free_port() -> int:
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


def test_is_server_ready_returns_true_when_port_open():
    port = _free_port()
    listener = _start_listener(port)
    try:
        assert is_server_ready(port, timeout=5) is True
    finally:
        listener.close()


def test_is_server_ready_returns_false_when_port_closed():
    port = _free_port()
    # nothing listens on this port now
    assert is_server_ready(port, timeout=2) is False


def test_is_server_ready_returns_true_after_accepting():
    """A server that accepts the connection should still report ready
    (is_server_ready only checks connectability, not HTTP readiness)."""
    port = _free_port()
    listener = _start_listener(port)

    def accept_loop():
        try:
            while True:
                conn, _ = listener.accept()
                conn.close()
        except OSError:
            pass

    t = threading.Thread(target=accept_loop, daemon=True)
    t.start()
    time.sleep(0.2)
    try:
        assert is_server_ready(port, timeout=5) is True
    finally:
        listener.close()
        time.sleep(0.1)
