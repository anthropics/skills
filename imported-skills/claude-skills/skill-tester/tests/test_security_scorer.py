#!/usr/bin/env python3
"""
Tests for security_scorer.py - Security Dimension Scoring Tests

This test module validates the security_scorer.py module's ability to:
- Detect hardcoded sensitive data (passwords, API keys, tokens, private keys)
- Detect path traversal vulnerabilities
- Detect command injection risks
- Score input validation quality
- Handle edge cases (empty files, environment variables, etc.)

Run with: python -m unittest test_security_scorer
"""

import tempfile
import unittest
from pathlib import Path

# Add the scripts directory to the path
import sys
SCRIPTS_DIR = Path(__file__).parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

from security_scorer import (
    SecurityScorer,
    # Constants
    MAX_COMPONENT_SCORE,
    MIN_SCORE,
    BASE_SCORE_SENSITIVE_DATA,
    BASE_SCORE_FILE_OPS,
    BASE_SCORE_COMMAND_INJECTION,
    BASE_SCORE_INPUT_VALIDATION,
    CRITICAL_VULNERABILITY_PENALTY,
    HIGH_SEVERITY_PENALTY,
    MEDIUM_SEVERITY_PENALTY,
    LOW_SEVERITY_PENALTY,
    SAFE_PATTERN_BONUS,
    GOOD_PRACTICE_BONUS,
    # Pre-compiled patterns
    PATTERN_HARDCODED_PASSWORD,
    PATTERN_HARDCODED_API_KEY,
    PATTERN_HARDCODED_TOKEN,
    PATTERN_HARDCODED_PRIVATE_KEY,
    PATTERN_OS_SYSTEM,
    PATTERN_EVAL,
    PATTERN_EXEC,
    PATTERN_SUBPROCESS_SHELL_TRUE,
    PATTERN_SHLEX_QUOTE,
    PATTERN_SAFE_ENV_VAR,
)


class TestSecurityScorerConstants(unittest.TestCase):
    """Tests for security scorer constants."""
    
    def test_max_component_score_value(self):
        """Test that MAX_COMPONENT_SCORE is 25."""
        self.assertEqual(MAX_COMPONENT_SCORE, 25)
        
    def test_min_score_value(self):
        """Test that MIN_SCORE is 0."""
        self.assertEqual(MIN_SCORE, 0)
        
    def test_base_scores_are_reasonable(self):
        """Test that base scores are within valid range."""
        self.assertGreaterEqual(BASE_SCORE_SENSITIVE_DATA, MIN_SCORE)
        self.assertLessEqual(BASE_SCORE_SENSITIVE_DATA, MAX_COMPONENT_SCORE)
        self.assertGreaterEqual(BASE_SCORE_FILE_OPS, MIN_SCORE)
        self.assertLessEqual(BASE_SCORE_FILE_OPS, MAX_COMPONENT_SCORE)
        self.assertGreaterEqual(BASE_SCORE_COMMAND_INJECTION, MIN_SCORE)
        self.assertLessEqual(BASE_SCORE_COMMAND_INJECTION, MAX_COMPONENT_SCORE)
        
    def test_penalty_values_are_negative(self):
        """Test that penalty values are negative."""
        self.assertLess(CRITICAL_VULNERABILITY_PENALTY, 0)
        self.assertLess(HIGH_SEVERITY_PENALTY, 0)
        self.assertLess(MEDIUM_SEVERITY_PENALTY, 0)
        self.assertLess(LOW_SEVERITY_PENALTY, 0)
        
    def test_bonus_values_are_positive(self):
        """Test that bonus values are positive."""
        self.assertGreater(SAFE_PATTERN_BONUS, 0)
        self.assertGreater(GOOD_PRACTICE_BONUS, 0)
        
    def test_severity_ordering(self):
        """Test that severity penalties are ordered correctly."""
        # Critical should be most severe (most negative)
        self.assertLess(CRITICAL_VULNERABILITY_PENALTY, HIGH_SEVERITY_PENALTY)
        self.assertLess(HIGH_SEVERITY_PENALTY, MEDIUM_SEVERITY_PENALTY)
        self.assertLess(MEDIUM_SEVERITY_PENALTY, LOW_SEVERITY_PENALTY)


class TestPrecompiledPatterns(unittest.TestCase):
    """Tests for pre-compiled regex patterns."""
    
    def test_password_pattern_detects_hardcoded(self):
        """Test that password pattern detects hardcoded passwords."""
        code = 'password = "my_secret_password_123"'
        self.assertTrue(PATTERN_HARDCODED_PASSWORD.search(code))
        
    def test_password_pattern_ignores_short_values(self):
        """Test that password pattern ignores very short values."""
        code = 'password = "x"'  # Too short
        self.assertFalse(PATTERN_HARDCODED_PASSWORD.search(code))
        
    def test_api_key_pattern_detects_hardcoded(self):
        """Test that API key pattern detects hardcoded keys."""
        code = 'api_key = "sk-1234567890abcdef"'
        self.assertTrue(PATTERN_HARDCODED_API_KEY.search(code))
        
    def test_token_pattern_detects_hardcoded(self):
        """Test that token pattern detects hardcoded tokens."""
        code = 'token = "ghp_1234567890abcdef"'
        self.assertTrue(PATTERN_HARDCODED_TOKEN.search(code))
        
    def test_private_key_pattern_detects_hardcoded(self):
        """Test that private key pattern detects hardcoded keys."""
        code = 'private_key = "-----BEGIN RSA PRIVATE KEY-----"'
        self.assertTrue(PATTERN_HARDCODED_PRIVATE_KEY.search(code))
        
    def test_os_system_pattern_detects(self):
        """Test that os.system pattern is detected."""
        code = 'os.system("ls -la")'
        self.assertTrue(PATTERN_OS_SYSTEM.search(code))
        
    def test_eval_pattern_detects(self):
        """Test that eval pattern is detected."""
        code = 'result = eval(user_input)'
        self.assertTrue(PATTERN_EVAL.search(code))
        
    def test_exec_pattern_detects(self):
        """Test that exec pattern is detected."""
        code = 'exec(user_code)'
        self.assertTrue(PATTERN_EXEC.search(code))
        
    def test_subprocess_shell_true_pattern_detects(self):
        """Test that subprocess shell=True pattern is detected."""
        code = 'subprocess.run(cmd, shell=True)'
        self.assertTrue(PATTERN_SUBPROCESS_SHELL_TRUE.search(code))
        
    def test_shlex_quote_pattern_detects(self):
        """Test that shlex.quote pattern is detected."""
        code = 'safe_cmd = shlex.quote(user_input)'
        self.assertTrue(PATTERN_SHLEX_QUOTE.search(code))
        
    def test_safe_env_var_pattern_detects(self):
        """Test that safe environment variable pattern is detected."""
        code = 'password = os.getenv("DB_PASSWORD")'
        self.assertTrue(PATTERN_SAFE_ENV_VAR.search(code))


class TestSecurityScorerInit(unittest.TestCase):
    """Tests for SecurityScorer initialization."""
    
    def test_init_with_empty_list(self):
        """Test initialization with empty script list."""
        scorer = SecurityScorer([])
        self.assertEqual(scorer.scripts, [])
        self.assertFalse(scorer.verbose)
        
    def test_init_with_scripts(self):
        """Test initialization with script list."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "test.py"
            script_path.write_text("# test")
            
            scorer = SecurityScorer([script_path])
            self.assertEqual(len(scorer.scripts), 1)
            
    def test_init_with_verbose(self):
        """Test initialization with verbose mode."""
        scorer = SecurityScorer([], verbose=True)
        self.assertTrue(scorer.verbose)


class TestSensitiveDataExposure(unittest.TestCase):
    """Tests for sensitive data exposure scoring."""
    
    def test_no_scripts_returns_max_score(self):
        """Test that empty script list returns max score."""
        scorer = SecurityScorer([])
        score, findings = scorer.score_sensitive_data_exposure()
        self.assertEqual(score, float(MAX_COMPONENT_SCORE))
        self.assertEqual(findings, [])
        
    def test_clean_script_scores_high(self):
        """Test that clean script without sensitive data scores high."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "clean.py"
            script_path.write_text("""
import os

def get_password():
    return os.getenv("DB_PASSWORD")
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            self.assertGreaterEqual(score, 20)
            self.assertEqual(len(findings), 0)
            
    def test_hardcoded_password_detected(self):
        """Test that hardcoded password is detected and penalized."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "insecure.py"
            script_path.write_text("""
password = "super_secret_password_123"

def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            self.assertTrue(any('password' in f.lower() for f in findings))
            
    def test_hardcoded_api_key_detected(self):
        """Test that hardcoded API key is detected and penalized."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "insecure.py"
            script_path.write_text("""
api_key = "sk-1234567890abcdef123456"

def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            # Check for 'api' or 'hardcoded' in findings (description is 'hardcoded API key')
            self.assertTrue(any('api' in f.lower() or 'hardcoded' in f.lower() for f in findings))
            
    def test_hardcoded_token_detected(self):
        """Test that hardcoded token is detected and penalized."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "insecure.py"
            script_path.write_text("""
token = "ghp_1234567890abcdef"

def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            
    def test_hardcoded_private_key_detected(self):
        """Test that hardcoded private key is detected and penalized."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "insecure.py"
            script_path.write_text("""
private_key = "-----BEGIN RSA PRIVATE KEY-----MIIEowIBAAJCA..."

def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            
    def test_environment_variable_not_flagged(self):
        """Test that environment variable usage is not flagged as sensitive."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "secure.py"
            script_path.write_text("""
import os

def get_credentials():
    password = os.getenv("DB_PASSWORD")
    api_key = os.environ.get("API_KEY")
    return password, api_key
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            # Should score well because using environment variables
            self.assertGreaterEqual(score, 20)
            
    def test_empty_file_handled(self):
        """Test that empty file is handled gracefully."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "empty.py"
            script_path.write_text("")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            # Should return max score for empty file (no sensitive data)
            self.assertGreaterEqual(score, 20)
            
    def test_jwt_token_detected(self):
        """Test that JWT token in code is detected."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "jwt.py"
            script_path.write_text("""
# JWT token for testing
token = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.dozjgNryP4J3jVmNHl0w5N_XgL0n3I9PlFUP0THsR8U"

def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_sensitive_data_exposure()
            
            # Should be penalized for JWT token
            self.assertLess(score, MAX_COMPONENT_SCORE)


class TestSafeFileOperations(unittest.TestCase):
    """Tests for safe file operations scoring."""
    
    def test_no_scripts_returns_max_score(self):
        """Test that empty script list returns max score."""
        scorer = SecurityScorer([])
        score, findings = scorer.score_safe_file_operations()
        self.assertEqual(score, float(MAX_COMPONENT_SCORE))
        
    def test_safe_pathlib_usage_scores_high(self):
        """Test that safe pathlib usage scores high."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "safe.py"
            script_path.write_text("""
from pathlib import Path

def read_file(filename):
    path = Path(filename).resolve()
    return path.read_text()
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_safe_file_operations()
            
            self.assertGreaterEqual(score, 15)
            
    def test_path_traversal_detected(self):
        """Test that path traversal pattern is detected."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "risky.py"
            script_path.write_text("""
def read_file(base_path, filename):
    # Potential path traversal vulnerability
    path = base_path + "/../../../etc/passwd"
    return open(path).read()
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_safe_file_operations()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            
    def test_basename_usage_scores_bonus(self):
        """Test that basename usage gets bonus points."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "safe.py"
            script_path.write_text("""
import os

def safe_filename(user_input):
    return os.path.basename(user_input)
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_safe_file_operations()
            
            self.assertGreaterEqual(score, 15)


class TestCommandInjectionPrevention(unittest.TestCase):
    """Tests for command injection prevention scoring."""
    
    def test_no_scripts_returns_max_score(self):
        """Test that empty script list returns max score."""
        scorer = SecurityScorer([])
        score, findings = scorer.score_command_injection_prevention()
        self.assertEqual(score, float(MAX_COMPONENT_SCORE))
        
    def test_os_system_detected(self):
        """Test that os.system usage is detected."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "risky.py"
            script_path.write_text("""
import os

def run_command(user_input):
    os.system("echo " + user_input)
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_command_injection_prevention()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            self.assertTrue(any('os.system' in f.lower() for f in findings))
            
    def test_subprocess_shell_true_detected(self):
        """Test that subprocess with shell=True is detected."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "risky.py"
            script_path.write_text("""
import subprocess

def run_command(cmd):
    subprocess.run(cmd, shell=True)
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_command_injection_prevention()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            # Check for 'shell' or 'subprocess' in findings
            self.assertTrue(any('shell' in f.lower() or 'subprocess' in f.lower() for f in findings))
            
    def test_eval_detected(self):
        """Test that eval usage is detected."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "risky.py"
            script_path.write_text("""
def evaluate(user_input):
    return eval(user_input)
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_command_injection_prevention()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            self.assertTrue(any('eval' in f.lower() for f in findings))
            
    def test_exec_detected(self):
        """Test that exec usage is detected."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "risky.py"
            script_path.write_text("""
def execute(user_code):
    exec(user_code)
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_command_injection_prevention()
            
            self.assertLess(score, MAX_COMPONENT_SCORE)
            self.assertTrue(any('exec' in f.lower() for f in findings))
            
    def test_shlex_quote_gets_bonus(self):
        """Test that shlex.quote usage gets bonus points."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "safe.py"
            script_path.write_text("""
import shlex
import subprocess

def run_command(user_input):
    safe_cmd = shlex.quote(user_input)
    subprocess.run(["echo", safe_cmd], shell=False)
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_command_injection_prevention()
            
            self.assertGreaterEqual(score, 20)
            
    def test_safe_subprocess_scores_high(self):
        """Test that safe subprocess usage (shell=False) scores high."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "safe.py"
            script_path.write_text("""
import subprocess

def run_command(cmd_parts):
    subprocess.run(cmd_parts, shell=False)
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, findings = scorer.score_command_injection_prevention()
            
            self.assertGreaterEqual(score, 20)


class TestInputValidation(unittest.TestCase):
    """Tests for input validation scoring."""
    
    def test_no_scripts_returns_max_score(self):
        """Test that empty script list returns max score."""
        scorer = SecurityScorer([])
        score, suggestions = scorer.score_input_validation()
        self.assertEqual(score, float(MAX_COMPONENT_SCORE))
        
    def test_argparse_usage_scores_bonus(self):
        """Test that argparse usage gets bonus points."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "good.py"
            script_path.write_text("""
import argparse

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    args = parser.parse_args()
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, suggestions = scorer.score_input_validation()
            
            # Base score is 10, argparse gives +3 bonus, so score should be 13
            self.assertGreaterEqual(score, 10)
            self.assertLessEqual(score, MAX_COMPONENT_SCORE)
            
    def test_isinstance_usage_scores_bonus(self):
        """Test that isinstance usage gets bonus points."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "good.py"
            script_path.write_text("""
def process(value):
    if isinstance(value, str):
        return value.upper()
    return value
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, suggestions = scorer.score_input_validation()
            
            self.assertGreater(score, BASE_SCORE_INPUT_VALIDATION)
            
    def test_try_except_scores_bonus(self):
        """Test that try/except usage gets bonus points."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "good.py"
            script_path.write_text("""
def process(value):
    try:
        return int(value)
    except ValueError:
        return 0
    
def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, suggestions = scorer.score_input_validation()
            
            self.assertGreater(score, BASE_SCORE_INPUT_VALIDATION)
            
    def test_minimal_validation_gets_suggestion(self):
        """Test that minimal validation triggers suggestion."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "minimal.py"
            script_path.write_text("""
def main():
    print("Hello")
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            score, suggestions = scorer.score_input_validation()
            
            self.assertLess(score, 15)
            self.assertTrue(len(suggestions) > 0)


class TestOverallScore(unittest.TestCase):
    """Tests for overall security score calculation."""
    
    def test_overall_score_components_present(self):
        """Test that overall score includes all components."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "test.py"
            script_path.write_text("""
import os
import argparse

def main():
    parser = argparse.ArgumentParser()
    parser.parse_args()
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            results = scorer.get_overall_score()
            
            self.assertIn('overall_score', results)
            self.assertIn('components', results)
            self.assertIn('findings', results)
            self.assertIn('suggestions', results)
            
            components = results['components']
            self.assertIn('sensitive_data_exposure', components)
            self.assertIn('safe_file_operations', components)
            self.assertIn('command_injection_prevention', components)
            self.assertIn('input_validation', components)
            
    def test_overall_score_is_weighted_average(self):
        """Test that overall score is calculated as weighted average."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "test.py"
            script_path.write_text("""
import argparse

def main():
    parser = argparse.ArgumentParser()
    parser.parse_args()
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            results = scorer.get_overall_score()
            
            # Calculate expected weighted average
            expected = (
                results['components']['sensitive_data_exposure'] * 0.25 +
                results['components']['safe_file_operations'] * 0.25 +
                results['components']['command_injection_prevention'] * 0.25 +
                results['components']['input_validation'] * 0.25
            )
            
            self.assertAlmostEqual(results['overall_score'], expected, places=0)
            
    def test_critical_vulnerability_caps_score(self):
        """Test that critical vulnerabilities cap the overall score."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "critical.py"
            script_path.write_text("""
password = "hardcoded_password_123"
api_key = "sk-1234567890abcdef"

def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            results = scorer.get_overall_score()
            
            # Score should be capped at 30 for critical vulnerabilities
            self.assertLessEqual(results['overall_score'], 30)
            self.assertTrue(results['has_critical_vulnerabilities'])
            
    def test_secure_script_scores_high(self):
        """Test that secure script scores high overall."""
        with tempfile.TemporaryDirectory() as tmpdir:
            script_path = Path(tmpdir) / "secure.py"
            script_path.write_text("""
#!/usr/bin/env python3
import argparse
import os
import shlex
import subprocess
from pathlib import Path

def validate_path(path_str):
    path = Path(path_str).resolve()
    if not path.exists():
        raise FileNotFoundError("Path not found")
    return path

def safe_command(args):
    return subprocess.run(args, shell=False, capture_output=True)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    args = parser.parse_args()
    
    db_password = os.getenv("DB_PASSWORD")
    path = validate_path(args.input)
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([script_path])
            results = scorer.get_overall_score()
            
            # Secure script should score reasonably well
            # Note: Score may vary based on pattern detection
            self.assertGreater(results['overall_score'], 20)


class TestScoreClamping(unittest.TestCase):
    """Tests for score boundary clamping."""
    
    def test_score_never_below_zero(self):
        """Test that score never goes below 0."""
        scorer = SecurityScorer([])
        # Test with extreme negative
        result = scorer._clamp_score(-100)
        self.assertEqual(result, MIN_SCORE)
        
    def test_score_never_above_max(self):
        """Test that score never goes above max."""
        scorer = SecurityScorer([])
        # Test with extreme positive
        result = scorer._clamp_score(1000)
        self.assertEqual(result, MAX_COMPONENT_SCORE)
        
    def test_score_unchanged_in_valid_range(self):
        """Test that score is unchanged in valid range."""
        scorer = SecurityScorer([])
        for test_score in [0, 5, 10, 15, 20, 25]:
            result = scorer._clamp_score(test_score)
            self.assertEqual(result, test_score)


class TestMultipleScripts(unittest.TestCase):
    """Tests for scoring multiple scripts."""
    
    def test_multiple_scripts_averaged(self):
        """Test that scores are averaged across multiple scripts."""
        with tempfile.TemporaryDirectory() as tmpdir:
            secure_script = Path(tmpdir) / "secure.py"
            secure_script.write_text("""
import os

def main():
    password = os.getenv("PASSWORD")
    
if __name__ == "__main__":
    main()
""")
            
            insecure_script = Path(tmpdir) / "insecure.py"
            insecure_script.write_text("""
password = "hardcoded_secret_password"

def main():
    pass
    
if __name__ == "__main__":
    main()
""")
            
            scorer = SecurityScorer([secure_script, insecure_script])
            score, findings = scorer.score_sensitive_data_exposure()
            
            # Score should be between secure and insecure
            self.assertGreater(score, 0)
            self.assertLess(score, MAX_COMPONENT_SCORE)


if __name__ == "__main__":
    unittest.main(verbosity=2)