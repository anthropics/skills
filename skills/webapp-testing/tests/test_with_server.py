import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "with_server.py"


class WithServerTests(unittest.TestCase):
    def test_occupied_port_does_not_run_command_against_another_server(self):
        with socket.socket() as listener, tempfile.TemporaryDirectory() as temp_dir:
            listener.bind(("127.0.0.1", 0))
            listener.listen()
            port = listener.getsockname()[1]
            marker = Path(temp_dir) / "command-ran"

            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT),
                    "--server",
                    subprocess.list2cmdline([sys.executable, "-c", "pass"]),
                    "--port",
                    str(port),
                    "--timeout",
                    "1",
                    "--",
                    sys.executable,
                    "-c",
                    f"from pathlib import Path; Path({str(marker)!r}).touch()",
                ],
                capture_output=True,
                text=True,
                timeout=5,
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(marker.exists())
            self.assertIn("already in use", result.stderr)


if __name__ == "__main__":
    unittest.main()
