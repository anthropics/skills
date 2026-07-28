import tempfile
import unittest
from pathlib import Path

from quick_validate import validate_skill


class UserInvocableValidationTests(unittest.TestCase):
    def _validate(self, frontmatter):
        with tempfile.TemporaryDirectory() as directory:
            skill = Path(directory)
            (skill / "SKILL.md").write_text(
                f"---\n{frontmatter}\n---\n\n# Test\n"
            )
            return validate_skill(skill)

    def test_user_invocable_boolean_is_accepted(self):
        self.assertEqual(
            self._validate("name: test\ndescription: A test skill\nuser-invocable: true"),
            (True, "Skill is valid!"),
        )

    def test_user_invocable_must_be_boolean(self):
        valid, message = self._validate(
            "name: test\ndescription: A test skill\nuser-invocable: 1"
        )
        self.assertFalse(valid)
        self.assertIn("user-invocable must be a boolean", message)


if __name__ == "__main__":
    unittest.main()
