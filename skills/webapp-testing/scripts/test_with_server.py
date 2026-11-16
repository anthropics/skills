#!/usr/bin/env python3
"""Tests for with_server.py. Run: python -m unittest scripts/test_with_server.py -v"""

import os
import socket
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "with_server.py"
POSIX = os.name == "posix"

# A tiny server: optional startup noise, then listen until killed.
SERVER_PY = textwrap.dedent(
    """
    import socket, sys, time
    port = int(sys.argv[1]); noise = int(sys.argv[2])
    sys.stdout.write("o" * noise); sys.stdout.flush()
    sys.stderr.write("e" * noise); sys.stderr.flush()
    s = socket.socket(); s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(("127.0.0.1", port)); s.listen()
    while True: time.sleep(0.1)
    """
)


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def port_open(port):
    try:
        with socket.create_connection(("127.0.0.1", port), timeout=0.3):
            return True
    except OSError:
        return False


def wait_closed(port, seconds=5):
    deadline = time.time() + seconds
    while time.time() < deadline:
        if not port_open(port):
            return True
        time.sleep(0.1)
    return False


class WithServerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.server = Path(self.tmp.name) / "server.py"
        self.server.write_text(SERVER_PY)

    def run_script(self, *args, timeout=30):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *args],
            capture_output=True, text=True, timeout=timeout,
        )

    def server_cmd(self, port, noise=0):
        return f'"{sys.executable}" "{self.server}" {port} {noise}'

    def test_command_runs_and_exit_code_propagates(self):
        port = free_port()
        r = self.run_script("--server", self.server_cmd(port), "--port", str(port),
                            "--", sys.executable, "-c", "import sys; sys.exit(7)")
        self.assertEqual(r.returncode, 7, r.stdout + r.stderr)
        self.assertIn("ready", r.stdout)

    def test_chatty_server_does_not_deadlock(self):
        # Unread stdout/stderr pipes fill at ~64 KiB and block the server forever.
        port = free_port()
        r = self.run_script("--server", self.server_cmd(port, noise=1_000_000), "--port", str(port),
                            "--timeout", "15", "--", sys.executable, "-c", "pass")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_server_that_dies_fails_fast_with_its_output(self):
        port = free_port()
        cmd = f'"{sys.executable}" -c "import sys; print(\'boom-from-server\'); sys.exit(3)"'
        start = time.time()
        r = self.run_script("--server", cmd, "--port", str(port), "--timeout", "20",
                            "--", sys.executable, "-c", "pass")
        self.assertNotEqual(r.returncode, 0)
        self.assertLess(time.time() - start, 10, "should not wait for the full timeout")
        self.assertIn("boom-from-server", r.stdout + r.stderr)

    def test_port_already_in_use_is_an_error(self):
        # Otherwise a stale server is mistaken for the one we just started.
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0)); s.listen()
            port = s.getsockname()[1]
            r = self.run_script("--server", self.server_cmd(port), "--port", str(port),
                                "--", sys.executable, "-c", "pass")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("already in use", r.stdout + r.stderr)

    @unittest.skipUnless(POSIX, "process groups are POSIX-specific here")
    def test_no_orphaned_server_after_run(self):
        # shell=True means terminate() alone only kills the shell, not the server it spawned.
        port = free_port()
        cmd = f"{self.server_cmd(port)} & wait"
        r = self.run_script("--server", cmd, "--port", str(port),
                            "--", sys.executable, "-c", "pass")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertTrue(wait_closed(port), "server child survived cleanup")

    def test_multiple_servers(self):
        p1, p2 = free_port(), free_port()
        r = self.run_script("--server", self.server_cmd(p1), "--port", str(p1),
                            "--server", self.server_cmd(p2), "--port", str(p2),
                            "--", sys.executable, "-c", "pass")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("All 2 server(s) ready", r.stdout)

    def test_mismatched_server_and_port_counts(self):
        r = self.run_script("--server", "x", "--port", "1", "--port", "2", "--", "true")
        self.assertEqual(r.returncode, 1)


if __name__ == "__main__":
    unittest.main()
