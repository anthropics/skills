"""Validation tests for MCP evaluation input files."""

import tempfile
import unittest
from pathlib import Path

from evaluation import parse_evaluation_file


class EvaluationFileTests(unittest.TestCase):
    def parse(self, content: str):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "evaluation.xml"
            path.write_text(content, encoding="utf-8")
            return parse_evaluation_file(path)

    def test_valid_pairs_are_kept(self):
        self.assertEqual(
            self.parse("<evaluation><qa_pair><question>Q?</question><answer>A</answer></qa_pair></evaluation>"),
            [{"question": "Q?", "answer": "A"}],
        )

    def test_malformed_xml_fails_instead_of_reporting_zero_tasks(self):
        with self.assertRaisesRegex(ValueError, "Invalid evaluation XML"):
            self.parse("<evaluation><qa_pair>")

    def test_no_qa_pairs_fails_instead_of_reporting_zero_tasks(self):
        with self.assertRaisesRegex(ValueError, "No qa_pair"):
            self.parse("<evaluation />")

    def test_incomplete_pair_cannot_inflate_accuracy(self):
        with self.assertRaisesRegex(ValueError, "qa_pair 2"):
            self.parse(
                "<evaluation>"
                "<qa_pair><question>Q1?</question><answer>A1</answer></qa_pair>"
                "<qa_pair><question>Q2?</question></qa_pair>"
                "</evaluation>"
            )

    def test_blank_answer_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "qa_pair 1"):
            self.parse(
                "<evaluation><qa_pair><question>Q?</question><answer>  </answer></qa_pair></evaluation>"
            )


if __name__ == "__main__":
    unittest.main()
