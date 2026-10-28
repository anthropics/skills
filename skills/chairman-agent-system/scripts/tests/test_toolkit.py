"""Real tools under governance: path confinement and derived sensitivity."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from chairman import (
    Classification,
    Level,
    PermissionDenied,
    Registry,
    Session,
    Store,
    Tool,
)
from chairman.toolkit import build_repo_toolkit, classify_path

COMPLETE = dict(
    purpose="Repository inspection",
    objectives=["Report on code health"],
    reporting="Per session",
    risks="Reads source; a write agent can alter the tree",
)


class ToolkitTestCase(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        (self.root / "README.md").write_text("# Project\n")
        (self.root / "main.py").write_text("print('hi')\n")
        (self.root / ".env").write_text("API_KEY=sk-live-secret\n")
        (self.root / "deploy.pem").write_text("-----BEGIN KEY-----\n")
        (self.root / "src").mkdir()
        (self.root / "src" / "app.py").write_text("x = 1\n")
        (self.root / ".git").mkdir()
        (self.root / ".git" / "config").write_text("[remote]\n")

        self.store = Store(":memory:")
        self.registry = Registry(self.store)
        self.registry.install_chairman()
        self.box = build_repo_toolkit(self.root)

    def tearDown(self):
        self.store.close()
        self._tmp.cleanup()

    def session_for(self, name, level=Level.OPERATOR,
                    classification=Classification.INTERNAL):
        request = self.registry.request_agent(
            requested_by="chairman", name=name, level=level,
            tools=[Tool.DEVELOPER], max_classification=classification, **COMPLETE,
        )
        self.registry.approve_request(request.request_id, approver="chairman")
        return Session(self.registry, self.box, name)


class TestPathClassification(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def test_secrets_are_restricted(self):
        for path in (".env", ".env.production", "deploy.pem", "server.key",
                     "id_rsa", "aws_credentials", "my_secret.txt", ".netrc"):
            with self.subTest(path=path):
                self.assertEqual(
                    classify_path(self.root, path), Classification.RESTRICTED
                )

    def test_vcs_internals_are_confidential(self):
        self.assertEqual(
            classify_path(self.root, ".git/config"), Classification.CONFIDENTIAL
        )

    def test_project_docs_are_public(self):
        for path in ("README.md", "LICENSE", "CHANGELOG.md", "docs/guide.md"):
            with self.subTest(path=path):
                self.assertEqual(
                    classify_path(self.root, path), Classification.PUBLIC
                )

    def test_source_defaults_to_internal(self):
        self.assertEqual(classify_path(self.root, "src/app.py"), Classification.INTERNAL)

    def test_traversal_is_refused(self):
        for path in ("../outside.txt", "../../etc/passwd", "src/../../escape"):
            with self.subTest(path=path):
                with self.assertRaises(PermissionDenied) as ctx:
                    classify_path(self.root, path)
                self.assertIn("escapes the governed root", str(ctx.exception))

    def test_absolute_path_outside_root_is_refused(self):
        with self.assertRaises(PermissionDenied):
            classify_path(self.root, "/etc/passwd")

    def test_absolute_path_inside_root_is_allowed(self):
        inside = str(self.root / "src" / "app.py")
        self.assertEqual(classify_path(self.root, inside), Classification.INTERNAL)

    def test_symlink_pointing_outside_is_refused(self):
        outside = Path(tempfile.mkdtemp()) / "target.txt"
        outside.write_text("secret")
        link = self.root / "innocent.txt"
        try:
            link.symlink_to(outside)
        except OSError:
            self.skipTest("symlinks unavailable")
        with self.assertRaises(PermissionDenied):
            classify_path(self.root, "innocent.txt")


class TestGovernedReads(ToolkitTestCase):
    def test_reads_public_and_internal_within_clearance(self):
        session = self.session_for("reviewer")
        self.assertIn("# Project", session.invoke("fs.read", "README.md"))
        self.assertIn("x = 1", session.invoke("fs.read", "src/app.py"))

    def test_secret_file_refused_at_internal_clearance(self):
        session = self.session_for("reviewer", classification=Classification.INTERNAL)
        with self.assertRaises(PermissionDenied) as ctx:
            session.invoke("fs.read", ".env")
        self.assertIn("RESTRICTED", str(ctx.exception))

    def test_traversal_refused_before_authorization(self):
        """Escape is malformed, not merely sensitive."""
        session = self.session_for("reviewer")
        with self.assertRaises(PermissionDenied) as ctx:
            session.invoke("fs.read", "../../etc/passwd")
        self.assertIn("escapes the governed root", str(ctx.exception))

    def test_restricted_clearance_still_cannot_escape_root(self):
        session = self.session_for(
            "executive", level=Level.EXECUTIVE, classification=Classification.RESTRICTED
        )
        session.invoke("fs.read", ".env")  # in-root secret: permitted at this clearance
        with self.assertRaises(PermissionDenied):
            session.invoke("fs.read", "/etc/passwd")

    def test_listing_is_governed_by_directory_sensitivity(self):
        session = self.session_for("reviewer")
        entries = session.invoke("fs.list", ".")
        self.assertIn("README.md", entries)
        self.assertIn("src/", entries)


class TestGovernedWrites(ToolkitTestCase):
    def test_read_only_agent_cannot_write(self):
        session = self.session_for("reviewer", level=Level.INTERNAL)
        with self.assertRaises(PermissionDenied) as ctx:
            session.invoke("fs.write", "notes.txt", "hello")
        self.assertIn("write requires", str(ctx.exception))
        self.assertFalse((self.root / "notes.txt").exists())

    def test_operator_can_write_and_the_file_really_changes(self):
        session = self.session_for("maintainer", level=Level.OPERATOR)
        session.invoke("fs.write", "notes.txt", "hello")
        self.assertEqual((self.root / "notes.txt").read_text(), "hello")

    def test_writing_a_secret_path_refused_below_restricted(self):
        session = self.session_for(
            "maintainer", level=Level.OPERATOR, classification=Classification.CONFIDENTIAL
        )
        with self.assertRaises(PermissionDenied):
            session.invoke("fs.write", ".env", "API_KEY=stolen")
        self.assertIn("sk-live-secret", (self.root / ".env").read_text())


class TestAuditOfRealWork(ToolkitTestCase):
    def test_real_operations_are_recorded_with_their_paths(self):
        session = self.session_for("reviewer")
        session.invoke("fs.read", "README.md")
        entries = self.registry.audit_log()
        invokes = [e for e in entries if e.action == "invoke:fs.read"]
        self.assertTrue(invokes)
        self.assertEqual(invokes[-1].details["classification"], "PUBLIC")

    def test_chain_verifies_after_mixed_real_traffic(self):
        session = self.session_for("maintainer", level=Level.OPERATOR)
        session.invoke("fs.read", "README.md")
        session.invoke("fs.write", "out.txt", "data")
        for bad in ("../escape", ".env"):
            with self.assertRaises(PermissionDenied):
                session.invoke("fs.read", bad)
        ok, problems = self.registry.verify_audit()
        self.assertTrue(ok, problems)


if __name__ == "__main__":
    unittest.main()
