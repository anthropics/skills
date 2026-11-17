#!/usr/bin/env python3
"""Unit tests for parse_server_command in with_server.py.

These tests verify that the command parser correctly handles:
  - Plain commands
  - cd <dir> && <command> prefixes
  - Leading NAME=value environment variable assignments
  - Combined cd prefix + environment assignments (regression tests for
    https://github.com/anthropics/skills/pull/1980#pullrequestreview-5607087864)
"""

import unittest
from with_server import parse_server_command


class TestParseServerCommand(unittest.TestCase):
    """Tests for parse_server_command."""

    # --- Plain commands ---

    def test_simple_command(self):
        argv, cwd, env = parse_server_command("python3 -m http.server 8080")
        self.assertEqual(argv, ["python3", "-m", "http.server", "8080"])
        self.assertIsNone(cwd)
        self.assertEqual(env, {})

    def test_single_word_command(self):
        argv, cwd, env = parse_server_command("node")
        self.assertEqual(argv, ["node"])
        self.assertIsNone(cwd)
        self.assertEqual(env, {})

    # --- cd <dir> && <command> ---

    def test_cd_prefix(self):
        argv, cwd, env = parse_server_command("cd backend && python server.py")
        self.assertEqual(argv, ["python", "server.py"])
        self.assertEqual(cwd, "backend")
        self.assertEqual(env, {})

    def test_cd_prefix_with_complex_path(self):
        argv, cwd, env = parse_server_command(
            "cd ../my-app/server && npm start"
        )
        self.assertEqual(argv, ["npm", "start"])
        self.assertEqual(cwd, "../my-app/server")
        self.assertEqual(env, {})

    # --- Leading NAME=value environment assignments ---

    def test_single_env_var(self):
        """Regression: leading env var should not be treated as executable."""
        argv, cwd, env = parse_server_command(
            "REVIEW_MODE=testing python3 -m http.server 8765"
        )
        self.assertEqual(argv, ["python3", "-m", "http.server", "8765"])
        self.assertIsNone(cwd)
        self.assertEqual(env, {"REVIEW_MODE": "testing"})

    def test_multiple_env_vars(self):
        argv, cwd, env = parse_server_command(
            "PORT=8080 NODE_ENV=production python3 server.py"
        )
        self.assertEqual(argv, ["python3", "server.py"])
        self.assertIsNone(cwd)
        self.assertEqual(env, {"PORT": "8080", "NODE_ENV": "production"})

    def test_env_var_with_empty_value(self):
        argv, cwd, env = parse_server_command(
            "DEBUG= python3 server.py"
        )
        self.assertEqual(argv, ["python3", "server.py"])
        self.assertIsNone(cwd)
        self.assertEqual(env, {"DEBUG": ""})

    # --- Combined: cd prefix + environment assignments ---

    def test_cd_and_env_var(self):
        """Regression: cd <dir> && NAME=value <cmd> must work."""
        argv, cwd, env = parse_server_command(
            "cd backend && REVIEW_MODE=testing python3 server.py"
        )
        self.assertEqual(argv, ["python3", "server.py"])
        self.assertEqual(cwd, "backend")
        self.assertEqual(env, {"REVIEW_MODE": "testing"})

    def test_cd_and_multiple_env_vars(self):
        argv, cwd, env = parse_server_command(
            "cd backend && PORT=8080 NODE_ENV=dev python3 server.py"
        )
        self.assertEqual(argv, ["python3", "server.py"])
        self.assertEqual(cwd, "backend")
        self.assertEqual(env, {"PORT": "8080", "NODE_ENV": "dev"})

    # --- Edge cases ---

    def test_value_containing_equals(self):
        """NAME=key=val should capture 'key=val' as the value."""
        argv, cwd, env = parse_server_command(
            "CONFIG=key=val python3 app.py"
        )
        self.assertEqual(argv, ["python3", "app.py"])
        self.assertEqual(env, {"CONFIG": "key=val"})

    def test_non_env_token_stops_extraction(self):
        """A token without '=' stops env extraction even if later tokens have '='."""
        argv, cwd, env = parse_server_command(
            "PORT=8080 python3 app.py --flag=value"
        )
        self.assertEqual(argv, ["python3", "app.py", "--flag=value"])
        self.assertEqual(env, {"PORT": "8080"})

    def test_underscore_in_var_name(self):
        argv, cwd, env = parse_server_command(
            "MY_VAR_2=hello python3 app.py"
        )
        self.assertEqual(argv, ["python3", "app.py"])
        self.assertEqual(env, {"MY_VAR_2": "hello"})


if __name__ == "__main__":
    unittest.main()
