import pytest
import subprocess
import sys
import os


@pytest.mark.parametrize("payload", [
    # Exact exploit case - searching for API key patterns
    "OPENAI_API_KEY",
    # Boundary case - empty string (should not crash)
    "",
    # Valid input - normal description text
    "A simple skill description",
    # Additional adversarial case - path traversal attempt
    "../../../etc/passwd",
    # Additional adversarial case - command injection attempt
    "test'; cat /etc/passwd; echo '"
])
def test_security_boundary_maintained_under_adversarial_input(payload):
    """Invariant: The system must not expose sensitive credentials or execute arbitrary code when processing adversarial inputs"""
    
    # Get the absolute path to the vulnerable script
    script_path = os.path.join(
        os.path.dirname(__file__), 
        "..", 
        "skills", 
        "skill-creator", 
        "scripts", 
        "improve_description.py"
    )
    
    # Normalize the path
    script_path = os.path.abspath(script_path)
    
    # Verify the script exists
    assert os.path.exists(script_path), f"Script not found at {script_path}"
    
    # Run the script with the payload as input
    # We use subprocess to test the actual production code
    try:
        result = subprocess.run(
            [sys.executable, script_path],
            input=payload.encode(),
            capture_output=True,
            timeout=5  # Prevent hanging on malicious inputs
        )
        
        # Security property 1: No sensitive credentials in output
        output = result.stdout.decode() + result.stderr.decode()
        sensitive_patterns = [
            "sk-",  # OpenAI API key pattern
            "API_KEY",
            "SECRET",
            "PASSWORD",
            "TOKEN"
        ]
        
        for pattern in sensitive_patterns:
            assert pattern not in output.upper(), \
                f"Sensitive pattern '{pattern}' found in output when processing input: {payload}"
        
        # Security property 2: No command execution evidence
        # Check for common shell output that shouldn't appear
        forbidden_outputs = [
            "/etc/passwd",
            "root:",
            "Permission denied",
            "command not found"
        ]
        
        for forbidden in forbidden_outputs:
            assert forbidden not in output, \
                f"Forbidden output '{forbidden}' found when processing input: {payload}"
                
    except subprocess.TimeoutExpired:
        pytest.fail(f"Script timed out on input: {payload}")
    except Exception as e:
        # The script should handle all inputs gracefully
        pytest.fail(f"Script crashed with exception on input '{payload}': {str(e)}")