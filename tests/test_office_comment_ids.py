import contextlib
import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
PML = "http://schemas.openxmlformats.org/presentationml/2006/main"


class CommentIdTests(unittest.TestCase):
    def validate_parts(self, skill, parts):
        office = ROOT / "skills" / skill / "scripts" / "office"
        spec = importlib.util.spec_from_file_location(
            f"{skill}_validator_base", office / "validators" / "base.py"
        )
        module = importlib.util.module_from_spec(spec)
        sys.path.insert(0, str(office))
        try:
            spec.loader.exec_module(module)
        finally:
            sys.path.pop(0)

        with tempfile.TemporaryDirectory() as directory:
            for name, content in parts.items():
                path = Path(directory) / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")
            validator = module.BaseSchemaValidator(directory)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                valid = validator.validate_unique_ids()
            return valid, output.getvalue()

    def comments(self, *pairs):
        comments = "".join(
            f'<p:cm authorId="{author}" idx="{index}"/>'
            for author, index in pairs
        )
        return f'<p:cmLst xmlns:p="{PML}">{comments}</p:cmLst>'

    def test_distinct_comments_by_one_author_are_valid(self):
        for skill in ("pptx", "docx", "xlsx"):
            with self.subTest(skill=skill):
                valid, output = self.validate_parts(skill, {
                    "ppt/comments/comment1.xml": self.comments((0, 1), (0, 2)),
                    "ppt/comments/comment2.xml": self.comments((0, 3)),
                })
                self.assertTrue(valid, output)

    def test_different_authors_can_reuse_an_index(self):
        for skill in ("pptx", "docx", "xlsx"):
            with self.subTest(skill=skill):
                valid, output = self.validate_parts(skill, {
                    "ppt/comments/comment1.xml": self.comments((0, 1), (1, 1)),
                })
                self.assertTrue(valid, output)

    def test_duplicate_pair_is_rejected_within_and_across_parts(self):
        for skill in ("pptx", "docx", "xlsx"):
            for across_parts in (False, True):
                with self.subTest(skill=skill, across_parts=across_parts):
                    parts = {
                        "ppt/comments/comment1.xml": self.comments((0, 1)),
                    }
                    if across_parts:
                        parts["ppt/comments/comment2.xml"] = self.comments((0, 1))
                    else:
                        parts["ppt/comments/comment1.xml"] = self.comments((0, 1), (0, 1))
                    valid, output = self.validate_parts(skill, parts)
                    self.assertFalse(valid)
                    self.assertIn("Duplicate comment authorId='0', idx='1'", output)

    def test_word_comment_ids_still_require_uniqueness(self):
        for skill in ("pptx", "docx", "xlsx"):
            with self.subTest(skill=skill):
                valid, output = self.validate_parts(skill, {
                    "word/comments.xml": (
                        '<w:comments xmlns:w="http://schemas.openxmlformats.org/'
                        'wordprocessingml/2006/main">'
                        '<w:comment w:id="1"/><w:comment w:id="1"/>'
                        '</w:comments>'
                    ),
                })
                self.assertFalse(valid)
                self.assertIn("Duplicate id='1'", output)


if __name__ == "__main__":
    unittest.main()
