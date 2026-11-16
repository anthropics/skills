"""Test the actual eval-review producer CLI against script/HTML boundaries."""

import html
import json
import re
import subprocess
import sys
import tempfile
import unittest
from html.parser import HTMLParser
from pathlib import Path

SCRIPT = Path(__file__).with_name("generate_eval_review.py")


class PageParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.scripts = []
        self.active = False

    def handle_starttag(self, tag, attrs):
        if tag == "script":
            self.scripts.append("")
            self.active = True

    def handle_endtag(self, tag):
        if tag == "script":
            self.active = False

    def handle_data(self, data):
        if self.active:
            self.scripts[-1] += data


class GenerateEvalReviewTests(unittest.TestCase):
    def test_cli_preserves_data_without_extra_script_or_placeholder_expansion(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            payload = '</script><script>SYNTHETIC_VISIBLE_SENTINEL</script> " \\ ą \u2028 & __SKILL_NAME_PLACEHOLDER__'
            evals = [{"query": payload, "should_trigger": True}, {"query": "__EVAL_DATA_PLACEHOLDER__", "should_trigger": False}]
            input_path = root / "evals.json"
            input_path.write_text(json.dumps(evals), encoding="utf-8")
            name = '<img src=x onerror="SENTINEL">__SKILL_DESCRIPTION_PLACEHOLDER__'
            description = 'Description & "quotes" </p><script>SENTINEL</script>'
            output = root / "review.html"
            completed = subprocess.run([
                sys.executable, "-B", str(SCRIPT), str(input_path), "--skill-name", name,
                "--skill-description", description, "--output", str(output),
            ], capture_output=True, text=True)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            page = output.read_text(encoding="utf-8")
            parsed = PageParser()
            parsed.feed(page)
            self.assertEqual(len(parsed.scripts), 1)
            match = re.search(r"const EVAL_DATA = (.*);", parsed.scripts[0])
            self.assertEqual(json.loads(match.group(1)), evals)
            self.assertIn(html.escape(name), page)
            self.assertIn(html.escape(description), page)
            self.assertIn("__SKILL_DESCRIPTION_PLACEHOLDER__", page)

    def test_invalid_eval_input_does_not_replace_existing_page(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            output = root / "review.html"
            output.write_text("previous page")
            for payload in ({"query": "wrong container"}, [{"query": 1, "should_trigger": True}], [{"query": "q", "should_trigger": "false"}]):
                with self.subTest(payload=payload):
                    input_path = root / "evals.json"
                    input_path.write_text(json.dumps(payload))
                    completed = subprocess.run([
                        sys.executable, "-B", str(SCRIPT), str(input_path), "--skill-name", "demo",
                        "--skill-description", "demo", "--output", str(output),
                    ], capture_output=True, text=True)
                    self.assertNotEqual(completed.returncode, 0)
                    self.assertIn("Expected an eval array", completed.stderr)
                    self.assertEqual(output.read_text(), "previous page")


if __name__ == "__main__":
    unittest.main()
