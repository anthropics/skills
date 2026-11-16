import os
import shlex
import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


class WithServerTests(unittest.TestCase):
    @unittest.skipIf(os.name == "nt", "the helper's server commands use a POSIX shell")
    def test_large_pre_bind_output_does_not_block_startup(self):
        helper = Path(__file__).parents[1] / "scripts" / "with_server.py"

        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            server_script = temp_path / "server.py"
            marker = temp_path / "consumer-ran"
            pid_file = temp_path / "server.pid"
            server_script.write_text(
                """import os
import socket
import sys

port, stream, pid_file = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
with open(pid_file, "w") as pid_file_handle:
    pid_file_handle.write(str(os.getpid()))
payload = memoryview(b"x" * (8 * 1024 * 1024))
while payload:
    payload = payload[os.write(stream, payload):]
server = socket.socket()
server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
server.bind(("127.0.0.1", port))
server.listen()
while True:
    connection, _ = server.accept()
    connection.close()
"""
            )

            for stream, output_name in ((1, "stdout"), (2, "stderr")):
                with self.subTest(output=output_name):
                    if marker.exists():
                        marker.unlink()
                    if pid_file.exists():
                        pid_file.unlink()
                    with socket.socket() as sock:
                        sock.bind(("127.0.0.1", 0))
                        port = sock.getsockname()[1]

                    server_command = "exec " + " ".join(
                        shlex.quote(value)
                        for value in (
                            sys.executable,
                            str(server_script),
                            str(port),
                            str(stream),
                            str(pid_file),
                        )
                    )
                    result = subprocess.run(
                        [
                            sys.executable,
                            str(helper),
                            "--server",
                            server_command,
                            "--port",
                            str(port),
                            "--timeout",
                            "4",
                            "--",
                            sys.executable,
                            "-c",
                            f"from pathlib import Path; Path({str(marker)!r}).touch()",
                        ],
                        capture_output=True,
                        timeout=10,
                    )

                    self.assertEqual(result.returncode, 0, result.stderr[-1000:])
                    self.assertTrue(marker.exists(), "consumer command did not run")
                    output = result.stdout if stream == 1 else result.stderr
                    self.assertGreaterEqual(len(output), 8 * 1024 * 1024)

                    server_pid = int(pid_file.read_text())
                    with self.assertRaises(ProcessLookupError):
                        os.kill(server_pid, 0)


if __name__ == "__main__":
    unittest.main()
