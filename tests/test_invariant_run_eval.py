import pytest
import subprocess
import sys
import os
from unittest.mock import patch, MagicMock

# Import the actual module
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
from skills.skill_creator.scripts.run_eval import main

@pytest.mark.parametrize("payload", [
    # Exact exploit case - command injection
    "test'; rm -rf /tmp/dummy; echo '",
    # Alternative injection pattern
    "$(whoami)",
    # Backtick execution
    "`id`",
    # Valid input (should pass)
    "normal query text",
])
def test_shell_command_injection_safety(payload):
    """Invariant: Shell commands never include unsanitized user input"""
    
    # Mock the subprocess.Popen to capture the actual command being executed
    mock_process = MagicMock()
    mock_process.communicate.return_value = (b"mocked output", b"")
    mock_process.returncode = 0
    
    captured_command = None
    
    def capture_popen(cmd, *args, **kwargs):
        nonlocal captured_command
        captured_command = cmd
        return mock_process
    
    # Mock the necessary dependencies
    with patch('subprocess.Popen', side_effect=capture_popen), \
         patch('sys.argv', ['run_eval.py', '--eval_set', 'test_set', '--query', payload]), \
         patch('os.path.exists', return_value=True), \
         patch('builtins.open'), \
         patch('json.load', return_value={'test_set': [{'query': payload}]}):
        
        try:
            main()
        except SystemExit:
            pass
        
        # Assert that if a command was captured, it doesn't contain unsanitized payload
        if captured_command:
            # Convert command list to string for checking
            cmd_str = ' '.join(captured_command)
            # The payload should NOT appear in the command string unless properly escaped
            # We check that the raw payload isn't directly concatenated
            assert payload not in cmd_str or \
                   f"'{payload}'" in cmd_str or \
                   f'"{payload}"' in cmd_str, \
                f"Unsanitized user input '{payload}' found in shell command: {cmd_str}"