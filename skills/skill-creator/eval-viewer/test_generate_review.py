"""Regression tests for the local evaluation viewer."""

import contextlib
import importlib.util
import io
import socket
import sys
import tempfile
import unittest
from http.server import HTTPServer
from pathlib import Path
from unittest.mock import patch


SCRIPT = Path(__file__).with_name("generate_review.py")
spec = importlib.util.spec_from_file_location("generate_review", SCRIPT)
generate_review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generate_review)


class ViewerPortTests(unittest.TestCase):
    def test_occupied_port_does_not_kill_other_listener(self):
        with tempfile.TemporaryDirectory() as tmpdir, socket.socket() as listener:
            workspace = Path(tmpdir)
            outputs = workspace / "eval-1" / "with_skill" / "run-1" / "outputs"
            outputs.mkdir(parents=True)
            (outputs / "answer.txt").write_text("answer", encoding="utf-8")

            listener.bind(("127.0.0.1", 0))
            listener.listen()
            occupied_port = listener.getsockname()[1]

            output = io.StringIO()
            argv = [str(SCRIPT), str(workspace), "--port", str(occupied_port)]
            with (
                patch.object(sys, "argv", argv),
                patch.object(generate_review, "_kill_port", side_effect=AssertionError("killed other process"), create=True),
                patch.object(generate_review.webbrowser, "open"),
                patch.object(HTTPServer, "serve_forever", lambda server: server.server_close()),
                contextlib.redirect_stdout(output),
            ):
                generate_review.main()

            self.assertNotIn(f"http://localhost:{occupied_port}", output.getvalue())
            self.assertIn("URL:", output.getvalue())
            self.assertEqual(listener.getsockname()[1], occupied_port)


if __name__ == "__main__":
    unittest.main()
