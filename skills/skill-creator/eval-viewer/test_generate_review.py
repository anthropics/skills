#!/usr/bin/env python3
"""Regression tests for the eval-viewer feedback endpoint origin/content-type checks.

Covers https://github.com/anthropics/skills/issues/1789: the /api/feedback
endpoint must reject cross-origin POSTs and non-JSON content types instead of
writing arbitrary pages' payloads into the local feedback file.

Run:  python -m unittest discover -s skills/skill-creator/eval-viewer -p "test_*.py" -v
"""

import http.client
import json
import tempfile
import threading
import unittest
from pathlib import Path

from generate_review import ReviewHandler
from http.server import HTTPServer


def start_server(tmpdir: Path):
    workspace = tmpdir / "workspace"
    workspace.mkdir()
    feedback_path = tmpdir / "feedback.json"
    handler = lambda *args, **kwargs: ReviewHandler(  # noqa: E731
        workspace, "test-skill", feedback_path, {}, None, *args, **kwargs
    )
    server = HTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return server, feedback_path


def post(port: int, body: dict, content_type: str, origin: str | None):
    conn = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
    headers = {"Content-Type": content_type}
    if origin is not None:
        headers["Origin"] = origin
    conn.request("POST", "/api/feedback", body=json.dumps(body), headers=headers)
    resp = conn.getresponse()
    data = resp.read().decode()
    conn.close()
    return resp.status, data


class FeedbackEndpointValidationTest(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self._server, self.feedback_path = start_server(Path(self._tmp.name))
        self.port = self._server.server_port

    def tearDown(self):
        self._server.shutdown()
        self._server.server_close()
        self._tmp.cleanup()

    def _reviews_payload(self):
        return {"reviews": {"run-1": {"feedback": "ok", "outputs": []}}}

    def test_valid_json_no_origin_accepts(self):
        status, data = post(self.port, self._reviews_payload(), "application/json", None)
        self.assertEqual(status, 200)
        self.assertIn("ok", data)
        saved = json.loads(self.feedback_path.read_text())
        self.assertIn("run-1", saved["reviews"])

    def test_valid_json_localhost_origin_accepts(self):
        for origin in (
            "http://localhost:3117",
            "http://127.0.0.1:3117",
            f"http://127.0.0.1:{self.port}",
        ):
            with self.subTest(origin=origin):
                status, _ = post(self.port, self._reviews_payload(), "application/json", origin)
                self.assertEqual(status, 200)

    def test_wrong_content_type_rejected(self):
        for ctype in ("text/plain", "application/x-www-form-urlencoded", "multipart/form-data"):
            with self.subTest(ctype=ctype):
                status, data = post(self.port, self._reviews_payload(), ctype, None)
                self.assertEqual(status, 403)
                self.assertIn("Content-Type", data)
        self.assertFalse(self.feedback_path.exists())

    def test_cross_origin_rejected(self):
        for origin in (
            "https://evil.example",
            "http://localhost.evil.example",
            "https://evil.example:8443",
            "http://192.168.1.10",
        ):
            with self.subTest(origin=origin):
                status, data = post(self.port, self._reviews_payload(), "application/json", origin)
                self.assertEqual(status, 403)
                self.assertIn("Cross-origin", data)
        self.assertFalse(self.feedback_path.exists())

    def test_json_content_type_with_params_accepted(self):
        status, _ = post(self.port, self._reviews_payload(), "application/json; charset=utf-8", None)
        self.assertEqual(status, 200)


if __name__ == "__main__":
    unittest.main()
