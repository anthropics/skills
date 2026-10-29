"""Ensure eval reports never follow links to files outside the workspace."""

import importlib.util
import json
import tempfile
import threading
import unittest
import urllib.request
from functools import partial
from http.server import HTTPServer
from pathlib import Path


SCRIPT = Path(__file__).with_name("generate_review.py")
spec = importlib.util.spec_from_file_location("generate_review", SCRIPT)
generate_review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generate_review)


class ViewerSymlinkTests(unittest.TestCase):
    def test_symlinked_workspace_root_is_supported(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            workspace = root / "workspace"
            outputs = workspace / "eval-1" / "outputs"
            outputs.mkdir(parents=True)
            (outputs / "answer.txt").write_text("expected output", encoding="utf-8")
            alias = root / "workspace-alias"
            alias.symlink_to(workspace, target_is_directory=True)

            runs = generate_review.find_runs(alias)

            self.assertEqual(len(runs), 1)
            self.assertEqual([item["name"] for item in runs[0]["outputs"]], ["answer.txt"])

    def test_linked_output_file_is_not_embedded(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            workspace = root / "workspace"
            outputs = workspace / "eval-1" / "with_skill" / "run-1" / "outputs"
            outputs.mkdir(parents=True)
            (outputs / "answer.txt").write_text("expected output", encoding="utf-8")
            secret = root / "private.txt"
            secret.write_text("PRIVATE-MARKER", encoding="utf-8")
            (outputs / "linked.txt").symlink_to(secret)

            runs = generate_review.find_runs(workspace)

            self.assertEqual(len(runs), 1)
            self.assertEqual([item["name"] for item in runs[0]["outputs"]], ["answer.txt"])
            self.assertNotIn("PRIVATE-MARKER", generate_review.generate_html(runs, "test"))

    def test_linked_output_directory_is_not_traversed(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            workspace = root / "workspace"
            run = workspace / "eval-1" / "with_skill" / "run-1"
            run.mkdir(parents=True)
            secret_outputs = root / "private-outputs"
            secret_outputs.mkdir()
            (secret_outputs / "secret.txt").write_text("PRIVATE-MARKER", encoding="utf-8")
            (run / "outputs").symlink_to(secret_outputs, target_is_directory=True)

            self.assertEqual(generate_review.find_runs(workspace), [])

    def test_linked_run_directory_is_not_traversed(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            workspace = root / "workspace"
            workspace.mkdir()
            outside_run = root / "private-run"
            (outside_run / "outputs").mkdir(parents=True)
            (outside_run / "outputs" / "secret.txt").write_text("PRIVATE-MARKER", encoding="utf-8")
            (workspace / "linked-run").symlink_to(outside_run, target_is_directory=True)

            self.assertEqual(generate_review.find_runs(workspace), [])

    def test_linked_metadata_is_not_embedded(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            workspace = root / "workspace"
            run = workspace / "eval-1" / "with_skill" / "run-1"
            (run / "outputs").mkdir(parents=True)
            secret = root / "private.json"
            secret.write_text(json.dumps({"prompt": "PRIVATE-MARKER"}), encoding="utf-8")
            (run / "eval_metadata.json").symlink_to(secret)

            runs = generate_review.find_runs(workspace)

            self.assertEqual(runs[0]["prompt"], "(No prompt found)")
            self.assertNotIn("PRIVATE-MARKER", generate_review.generate_html(runs, "test"))

    def test_feedback_save_replaces_link_without_overwriting_target(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            workspace = root / "workspace"
            workspace.mkdir()
            secret = root / "private.txt"
            secret.write_text("PRIVATE-MARKER", encoding="utf-8")
            feedback = workspace / "feedback.json"
            feedback.symlink_to(secret)

            handler = partial(
                generate_review.ReviewHandler, workspace, "test", feedback, {}, None,
            )
            server = HTTPServer(("127.0.0.1", 0), handler)
            thread = threading.Thread(target=server.serve_forever)
            thread.start()
            try:
                url = f"http://127.0.0.1:{server.server_address[1]}/api/feedback"
                with urllib.request.urlopen(url, timeout=5) as response:
                    self.assertEqual(response.read(), b"{}")
                data = json.dumps({"reviews": []}).encode("utf-8")
                request = urllib.request.Request(
                    url, data=data, headers={"Content-Type": "application/json"}, method="POST",
                )
                with urllib.request.urlopen(request, timeout=5) as response:
                    self.assertEqual(response.status, 200)
                self.assertEqual(secret.read_text(encoding="utf-8"), "PRIVATE-MARKER")
                self.assertFalse(feedback.is_symlink())
                self.assertEqual(json.loads(feedback.read_text(encoding="utf-8")), {"reviews": []})
            finally:
                server.shutdown()
                server.server_close()
                thread.join(timeout=5)


if __name__ == "__main__":
    unittest.main()
