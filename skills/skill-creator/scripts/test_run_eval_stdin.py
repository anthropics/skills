import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run_eval


class RunEvalProcessTests(unittest.TestCase):
    def test_nested_claude_process_does_not_inherit_stdin(self):
        process = unittest.mock.Mock()
        process.poll.return_value = 0
        process.stdout.read.return_value = b""

        with tempfile.TemporaryDirectory() as root, patch.object(
            run_eval.subprocess, "Popen", return_value=process
        ) as popen:
            run_eval.run_single_query(
                "query", "demo", "description", 1, Path(root)
            )

        self.assertIs(popen.call_args.kwargs["stdin"], run_eval.subprocess.DEVNULL)


if __name__ == "__main__":
    unittest.main()
