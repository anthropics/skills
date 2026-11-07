"""Exercise workspace discovery, feedback identity, and the local HTTP API."""

import functools
import http.client
import importlib.util
import json
import subprocess
import sys
import tempfile
import threading
import unittest
from http.server import HTTPServer
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "eval-viewer" / "generate_review.py"
spec = importlib.util.spec_from_file_location("generate_review", SCRIPT)
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)


class ReviewWorkspaceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.parent = Path(self.temp.name)
        self.root = self.parent / "workspace"
        self.root.mkdir()

    def run_fixture(self, name, eval_id=None):
        path = self.root / name
        (path / "outputs").mkdir(parents=True)
        (path / "outputs" / "answer.txt").write_text("Synthetic answer")
        if eval_id is not None:
            (path / "eval_metadata.json").write_text(json.dumps({"eval_id": eval_id, "prompt": name}))
        return path

    def test_optional_eval_id_static_cli(self):
        self.run_fixture("annotated", 1)
        self.run_fixture("unannotated")
        output = self.parent / "review.html"
        completed = subprocess.run([
            sys.executable, "-B", "-X", "utf8", str(SCRIPT), str(self.root), "--static", str(output),
        ], capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertTrue(output.is_file())

    def test_colliding_paths_have_distinct_stable_ids_and_no_ambiguous_migration(self):
        self.run_fixture("eval-a/b", 1)
        self.run_fixture("eval/a-b", 2)
        ids = [run["id"] for run in review.find_runs(self.root)]
        self.assertEqual(ids, ["eval-a/b", "eval/a-b"])
        (self.root / "feedback.json").write_text(json.dumps({"reviews": [
            {"run_id": "eval-a-b", "feedback": "ambiguous old note"},
            {"run_id": "eval/a-b", "feedback": "canonical note"},
        ]}))
        previous = review.load_previous_iteration(self.root)
        self.assertEqual(previous["eval-a/b"]["feedback"], "")
        self.assertEqual(previous["eval/a-b"]["feedback"], "canonical note")
        self.assertEqual(previous["eval-a-b"]["feedback"], "ambiguous old note")

    def test_unique_legacy_feedback_migrates_in_previous_and_http_get(self):
        self.run_fixture("eval-a/run-1", 1)
        feedback = {"reviews": [{"run_id": "eval-a-run-1", "feedback": "old note"}]}
        (self.root / "feedback.json").write_text(json.dumps(feedback))
        self.assertEqual(review.load_previous_iteration(self.root)["eval-a/run-1"]["feedback"], "old note")
        connection = self.serve()
        connection.request("GET", "/api/feedback")
        response = connection.getresponse()
        self.assertEqual(response.status, 200)
        self.assertEqual(json.loads(response.read())["reviews"][0]["run_id"], "eval-a/run-1")

    def test_parent_metadata_stays_in_workspace(self):
        self.run_fixture(".")
        for filename, payload in (
            ("eval_metadata.json", {"eval_id": 1, "prompt": "OUTSIDE_SENTINEL"}),
            ("grading.json", {"summary": {"pass_rate": 1}}),
        ):
            (self.parent / filename).write_text(json.dumps(payload))
        run = review.find_runs(self.root)[0]
        self.assertEqual(run["prompt"], "(No prompt found)")
        self.assertIsNone(run["grading"])

    def test_get_then_post_cannot_drop_unresolved_legacy_or_unknown_notes(self):
        self.run_fixture("eval-a/b", 1)
        self.run_fixture("eval/a-b", 2)
        original = json.dumps({"reviews": [
            {"run_id": "eval-a-b", "feedback": "ambiguous note"},
            {"run_id": "unknown", "feedback": "orphan note"},
        ]})
        path = self.root / "feedback.json"
        path.write_text(original)
        connection = self.serve()
        connection.request("GET", "/api/feedback")
        response = connection.getresponse()
        loaded = json.loads(response.read())
        self.assertEqual(response.status, 200)
        self.assertEqual(len(loaded["reviews"]), 2)
        for reviews in ([], [{"run_id": "eval-a/b", "feedback": "new note"}]):
            connection.request("POST", "/api/feedback", json.dumps({"reviews": reviews, "status": "complete"}))
            response = connection.getresponse()
            self.assertIn("reconcile", response.read().decode())
            self.assertEqual(response.status, 409)
            self.assertEqual(path.read_text(), original)
        connection.request("POST", "/api/feedback", json.dumps(loaded))
        response = connection.getresponse()
        response.read()
        self.assertEqual(response.status, 200)
        self.assertEqual(json.loads(path.read_text())["reviews"], loaded["reviews"])

    def test_legacy_alias_of_existing_flat_run_is_explicit_conflict(self):
        self.run_fixture("eval-a/b", 1)
        self.run_fixture("eval-a-b", 2)
        path = self.root / "feedback.json"
        original = '{"reviews": [{"run_id": "eval-a-b", "feedback": "ambiguous"}]}'
        path.write_text(original)
        with self.assertRaises(review.FeedbackConflictError):
            review.load_previous_iteration(self.root)
        connection = self.serve()
        connection.request("GET", "/api/feedback")
        response = connection.getresponse()
        self.assertIn("Ambiguous", response.read().decode())
        self.assertEqual(response.status, 409)
        connection.request("POST", "/api/feedback", '{"reviews": []}')
        response = connection.getresponse()
        response.read()
        self.assertEqual(response.status, 409)
        self.assertEqual(path.read_text(), original)

    def test_actual_static_browser_export_and_autosave_roundtrip(self):
        # Node executes the actual generated browser producer, including its
        # failed-fetch download fallback; no browser/model/service is required.
        self.run_fixture("eval-a/b", 1)
        self.run_fixture("eval-a-b", 2)
        page = review.generate_html(review.find_runs(self.root), "synthetic")
        javascript = r'''
const vm = require('node:vm');
const fs = require('node:fs');
const page = fs.readFileSync(0, 'utf8');
const embedded = JSON.parse(page.match(/const EMBEDDED_DATA = (.*);/)[1]);
const source = page.slice(page.indexOf('    function saveCurrentFeedback()'), page.indexOf('    // ---- Toast ----'));
const requests = [], downloads = [];
const elements = {feedback: {value: 'nested note'}, 'feedback-status': {}, 'done-overlay': {classList: {add() {}}}};
const context = vm.createContext({
  EMBEDDED_DATA: embedded, currentIndex: 0,
  feedbackMap: {'eval-a/b': 'nested note', 'eval-a-b': 'flat note'},
  Date, Blob,
  document: {getElementById(id) {return elements[id]}, createElement() {return {click() {}}}},
  URL: {createObjectURL(blob) {downloads.push(blob); return 'blob:synthetic'}, revokeObjectURL() {}},
  fetch(_url, options) {requests.push(JSON.parse(options.body)); return Promise.reject(new Error('static mode'))},
});
vm.runInContext(source, context);
vm.runInContext('saveCurrentFeedback(); showDoneDialog();', context);
setImmediate(async () => console.log(JSON.stringify({requests, download: JSON.parse(await downloads[0].text())})));
'''
        completed = subprocess.run(["node", "-e", javascript], input=page, capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        payloads = json.loads(completed.stdout)
        for payload in [*payloads["requests"], payloads["download"]]:
            self.assertEqual(payload.get("run_id_format"), "relative_path")
            (self.root / "feedback.json").write_text(json.dumps(payload))
            previous = review.load_previous_iteration(self.root)
            self.assertEqual(previous["eval-a/b"]["feedback"], "nested note")
            self.assertEqual(previous["eval-a-b"]["feedback"], "flat note")

    def test_parent_metadata_fallback_inside_workspace_is_preserved(self):
        path = self.run_fixture("eval-1/run-1")
        (path.parent / "eval_metadata.json").write_text(json.dumps({"prompt": "inside", "eval_id": 1}))
        (path.parent / "grading.json").write_text('{"summary": {"pass_rate": 1}}')
        run = review.find_runs(self.root)[0]
        self.assertEqual(run["prompt"], "inside")
        self.assertEqual(run["grading"]["summary"]["pass_rate"], 1)

    def serve(self):
        handler = functools.partial(review.ReviewHandler, self.root, "test", self.root / "feedback.json", {}, None)
        server = HTTPServer(("127.0.0.1", 0), handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        def close():
            server.shutdown()
            server.server_close()
            thread.join(timeout=5)
        self.addCleanup(close)
        connection = http.client.HTTPConnection(*server.server_address, timeout=5)
        self.addCleanup(connection.close)
        return connection

    def test_invalid_post_preserves_good_feedback_then_valid_post_loads(self):
        self.run_fixture("run", 1)
        path = self.root / "feedback.json"
        original = '{"reviews": [{"run_id": "run", "feedback": "good"}]}'
        path.write_text(original)
        connection = self.serve()
        bad = [
            {"reviews": "invalid"}, {"reviews": ["invalid"]},
            {"reviews": [{"run_id": "run", "feedback": 1}]},
            {"reviews": [{"run_id": 1, "feedback": "x"}]},
            {"reviews": [{"run_id": "run", "feedback": "x"}] * 2},
            {"reviews": [], "status": "invalid"},
        ]
        for payload in bad:
            with self.subTest(payload=payload):
                connection.request("POST", "/api/feedback", json.dumps(payload), {"Content-Type": "application/json"})
                response = connection.getresponse()
                response.read()
                self.assertEqual(response.status, 400)
                self.assertEqual(path.read_text(), original)
        valid = {"reviews": [{"run_id": "run", "feedback": "new", "timestamp": "2026-01-01"}], "status": "complete"}
        connection.request("POST", "/api/feedback", json.dumps(valid), {"Content-Type": "application/json"})
        response = connection.getresponse()
        response.read()
        self.assertEqual(response.status, 200)
        self.assertEqual(review.load_previous_iteration(self.root)["run"]["feedback"], "new")


if __name__ == "__main__":
    unittest.main()
