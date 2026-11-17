"""Regression coverage for SKILL.md frontmatter parsing.

Run from the skill-creator directory: python -m unittest discover -s tests
"""

import tempfile
import unittest
from pathlib import Path

from scripts.utils import parse_skill_md


class ParseSkillMdTests(unittest.TestCase):
    def parse(self, frontmatter):
        content = f"---\n{frontmatter}\n---\n# Instructions\n\nKeep this body.\n"
        with tempfile.TemporaryDirectory() as directory:
            skill_path = Path(directory)
            (skill_path / "SKILL.md").write_text(content)
            name, description, full_content = parse_skill_md(skill_path)
        self.assertEqual(full_content, content)
        return name, description

    def test_plain_description(self):
        for description in ("Review reports.", 'Use for requests like "review my draft."'):
            with self.subTest(description=description):
                self.assertEqual(
                    self.parse(f"name: report-review\ndescription: {description}"),
                    ("report-review", description),
                )

    def test_quoted_scalars(self):
        cases = [
            ("'Review the user''s draft.'", "Review the user's draft."),
            (r'"Read \"Q4\" reports."', 'Read "Q4" reports.'),
            ('\'Explain "Q4"\'', 'Explain "Q4"'),
        ]
        for scalar, expected in cases:
            with self.subTest(scalar=scalar):
                self.assertEqual(
                    self.parse(f"name: report-review\ndescription: {scalar}"),
                    ("report-review", expected),
                )

    def test_comments_are_not_part_of_scalars(self):
        self.assertEqual(
            self.parse(
                "name: report-review # identifier\n"
                "description: Review reports. # author note"
            ),
            ("report-review", "Review reports."),
        )

    def test_block_scalars_preserve_yaml_semantics(self):
        cases = [
            (">-\n  Review reports.\n  Check totals.", "Review reports. Check totals."),
            ("|-\n  Review reports.\n  Check totals.", "Review reports.\nCheck totals."),
            (">-\n  Review reports.\n\n  Check totals.", "Review reports.\nCheck totals."),
            (">\n  Review reports.", "Review reports.\n"),
        ]
        for scalar, expected in cases:
            with self.subTest(scalar=scalar):
                self.assertEqual(
                    self.parse(f"name: report-review\ndescription: {scalar}"),
                    ("report-review", expected),
                )

    def test_invalid_frontmatter_raises_value_error(self):
        cases = [
            "name: report-review\ndescription: [unclosed",
            "- report-review",
            "name: report-review\ndescription: [Review, reports]",
            "name: 123\ndescription: Review reports.",
            "name: report-review\ndescription: !!python/object:example {}",
        ]
        for frontmatter in cases:
            with self.subTest(frontmatter=frontmatter):
                with self.assertRaises(ValueError):
                    self.parse(frontmatter)


if __name__ == "__main__":
    unittest.main()
