#!/usr/bin/env python3
"""
Security Scorer - Security dimension scoring module

This module provides comprehensive security assessment for Python scripts,
evaluating sensitive data exposure, safe file operations, command injection
prevention, and input validation quality.

Author: Claude Skills Engineering Team
Version: 2.0.0
"""

import re
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any

# =============================================================================
# CONSTANTS - Scoring thresholds and weights
# =============================================================================

# Maximum score per component (25 points each, 4 components = 100 total)
MAX_COMPONENT_SCORE: int = 25

# Minimum score floor (never go below 0)
MIN_SCORE: int = 0

# Security score thresholds for tier recommendations
SECURITY_SCORE_POWERFUL_TIER: int = 70  # Required for POWERFUL tier
SECURITY_SCORE_STANDARD_TIER: int = 50  # Required for STANDARD tier

# Scoring modifiers (magic numbers replaced with named constants)
BASE_SCORE_SENSITIVE_DATA: int = 25  # Start with full points
BASE_SCORE_FILE_OPS: int = 15  # Base score for file operations
BASE_SCORE_COMMAND_INJECTION: int = 25  # Start with full points
BASE_SCORE_INPUT_VALIDATION: int = 10  # Base score for input validation

# Penalty amounts (negative scoring)
CRITICAL_VULNERABILITY_PENALTY: int = -25  # Critical issues (hardcoded passwords, etc.)
HIGH_SEVERITY_PENALTY: int = -10  # High severity issues
MEDIUM_SEVERITY_PENALTY: int = -5  # Medium severity issues
LOW_SEVERITY_PENALTY: int = -2  # Low severity issues

# Bonus amounts (positive scoring)
SAFE_PATTERN_BONUS: int = 2  # Bonus for using safe patterns
GOOD_PRACTICE_BONUS: int = 3  # Bonus for good security practices

# =============================================================================
# PRE-COMPILED REGEX PATTERNS - Sensitive Data Detection
# =============================================================================

# Hardcoded credentials patterns (CRITICAL severity)
PATTERN_HARDCODED_PASSWORD = re.compile(
    r'password\s*=\s*["\'][^"\']{4,}["\']',
    re.IGNORECASE
)
PATTERN_HARDCODED_API_KEY = re.compile(
    r'api_key\s*=\s*["\'][^"\']{8,}["\']',
    re.IGNORECASE
)
PATTERN_HARDCODED_SECRET = re.compile(
    r'secret\s*=\s*["\'][^"\']{4,}["\']',
    re.IGNORECASE
)
PATTERN_HARDCODED_TOKEN = re.compile(
    r'token\s*=\s*["\'][^"\']{8,}["\']',
    re.IGNORECASE
)
PATTERN_HARDCODED_PRIVATE_KEY = re.compile(
    r'private_key\s*=\s*["\'][^"\']{20,}["\']',
    re.IGNORECASE
)
PATTERN_HARDCODED_AWS_KEY = re.compile(
    r'aws_access_key\s*=\s*["\'][^"\']{16,}["\']',
    re.IGNORECASE
)
PATTERN_HARDCODED_AWS_SECRET = re.compile(
    r'aws_secret\s*=\s*["\'][^"\']{20,}["\']',
    re.IGNORECASE
)

# Multi-line string patterns (CRITICAL severity)
PATTERN_MULTILINE_STRING = re.compile(
    r'["\']{3}[^"\']*?(?:password|api_key|secret|token|private_key)[^"\']*?["\']{3}',
    re.IGNORECASE | re.DOTALL
)

# F-string patterns (HIGH severity)
PATTERN_FSTRING_SENSITIVE = re.compile(
    r'f["\'].*?(?:password|api_key|secret|token)\s*=',
    re.IGNORECASE
)

# Base64 encoded secrets (MEDIUM severity)
PATTERN_BASE64_SECRET = re.compile(
    r'(?:base64|b64encode|b64decode)\s*\([^)]*(?:password|api_key|secret|token)',
    re.IGNORECASE
)

# JWT tokens (HIGH severity)
PATTERN_JWT_TOKEN = re.compile(
    r'eyJ[a-zA-Z0-9_-]*\.eyJ[a-zA-Z0-9_-]*\.[a-zA-Z0-9_-]*'
)

# Connection strings (HIGH severity)
PATTERN_CONNECTION_STRING = re.compile(
    r'(?:connection_string|conn_string|database_url)\s*=\s*["\'][^"\']*(?:password|pwd|passwd)[^"\']*["\']',
    re.IGNORECASE
)

# Safe credential patterns (environment variables are OK)
PATTERN_SAFE_ENV_VAR = re.compile(
    r'os\.(?:getenv|environ)\s*\(\s*["\'][^"\']+["\']',
    re.IGNORECASE
)

# =============================================================================
# PRE-COMPILED REGEX PATTERNS - Path Traversal Detection
# =============================================================================

# Basic path traversal patterns
PATTERN_PATH_TRAVERSAL_BASIC = re.compile(r'\.\.\/')
PATTERN_PATH_TRAVERSAL_WINDOWS = re.compile(r'\.\.\\')

# URL encoded path traversal (MEDIUM severity)
PATTERN_PATH_TRAVERSAL_URL_ENCODED = re.compile(
    r'%2e%2e%2f|%252e%252e%252f|\.\.%2f',
    re.IGNORECASE
)

# Unicode encoded path traversal (MEDIUM severity)
PATTERN_PATH_TRAVERSAL_UNICODE = re.compile(
    r'\\u002e\\u002e|\\uff0e\\uff0e|\u002e\u002e\/',
    re.IGNORECASE
)

# Null byte injection (HIGH severity)
PATTERN_NULL_BYTE = re.compile(r'%00|\\x00|\0')

# Risky file operation patterns
PATTERN_PATH_CONCAT = re.compile(
    r'open\s*\(\s*[^)]*\+',
    re.IGNORECASE
)
PATTERN_USER_INPUT_PATH = re.compile(
    r'\.join\s*\(\s*[^)]*input|os\.path\.join\s*\([^)]*request',
    re.IGNORECASE
)

# Safe file operation patterns
PATTERN_SAFE_BASENAME = re.compile(r'os\.path\.basename', re.IGNORECASE)
PATTERN_SAFE_PATHLIB = re.compile(r'pathlib\.Path\s*\(', re.IGNORECASE)
PATTERN_PATH_VALIDATION = re.compile(r'validate.*path', re.IGNORECASE)
PATTERN_PATH_RESOLVE = re.compile(r'\.resolve\s*\(', re.IGNORECASE)

# =============================================================================
# PRE-COMPILED REGEX PATTERNS - Command Injection Detection
# =============================================================================

# Dangerous patterns (CRITICAL severity)
PATTERN_OS_SYSTEM = re.compile(r'os\.system\s*\(')
PATTERN_OS_POPEN = re.compile(r'os\.popen\s*\(')
PATTERN_EVAL = re.compile(r'eval\s*\(')
PATTERN_EXEC = re.compile(r'exec\s*\(')

# Subprocess with shell=True (HIGH severity)
PATTERN_SUBPROCESS_SHELL_TRUE = re.compile(
    r'subprocess\.(?:call|run|Popen|check_output)\s*\([^)]*shell\s*=\s*True',
    re.IGNORECASE
)

# Asyncio subprocess shell (HIGH severity)
PATTERN_ASYNCIO_SHELL = re.compile(
    r'asyncio\.create_subprocess_shell\s*\(',
    re.IGNORECASE
)

# Pexpect spawn (HIGH severity)
PATTERN_PEXPECT_SPAWN = re.compile(r'pexpect\.spawn\s*\(', re.IGNORECASE)

# Safe subprocess patterns
PATTERN_SAFE_SUBPROCESS = re.compile(
    r'subprocess\.(?:run|call|Popen)\s*\([^)]*shell\s*=\s*False',
    re.IGNORECASE
)
PATTERN_SHLEX_QUOTE = re.compile(r'shlex\.quote', re.IGNORECASE)
PATTERN_SHLEX_SPLIT = re.compile(r'shlex\.split', re.IGNORECASE)

# =============================================================================
# PRE-COMPILED REGEX PATTERNS - Input Validation Detection
# =============================================================================

# Good validation patterns
PATTERN_ARGPARSE = re.compile(r'argparse')
PATTERN_TRY_EXCEPT = re.compile(r'try\s*:[\s\S]*?except\s+\w*Error')
PATTERN_INPUT_CHECK = re.compile(r'if\s+not\s+\w+\s*:')
PATTERN_ISINSTANCE = re.compile(r'isinstance\s*\(')
PATTERN_ISDIGIT = re.compile(r'\.isdigit\s*\(\)')
PATTERN_REGEX_VALIDATION = re.compile(r're\.(?:match|search|fullmatch)\s*\(')
PATTERN_VALIDATOR_CLASS = re.compile(r'Validator', re.IGNORECASE)
PATTERN_VALIDATE_FUNC = re.compile(r'validate', re.IGNORECASE)
PATTERN_SANITIZE_FUNC = re.compile(r'sanitize', re.IGNORECASE)


class SecurityScorer:
    """
    Security dimension scoring engine.
    
    This class evaluates Python scripts for security vulnerabilities and best practices
    across four components:
    1. Sensitive Data Exposure Prevention (25% of security score)
    2. Safe File Operations (25% of security score)
    3. Command Injection Prevention (25% of security score)
    4. Input Validation Quality (25% of security score)
    
    Attributes:
        scripts: List of Python script paths to evaluate
        verbose: Whether to output verbose logging
    """
    
    def __init__(self, scripts: List[Path], verbose: bool = False):
        """
        Initialize the SecurityScorer.
        
        Args:
            scripts: List of Path objects pointing to Python scripts
            verbose: Enable verbose output for debugging
        """
        self.scripts = scripts
        self.verbose = verbose
        self._findings: List[str] = []
        
    def _log_verbose(self, message: str) -> None:
        """Log verbose message if verbose mode is enabled."""
        if self.verbose:
            print(f"[SECURITY] {message}")
            
    def _get_script_content(self, script_path: Path) -> Optional[str]:
        """
        Safely read script content.
        
        Args:
            script_path: Path to the Python script
            
        Returns:
            Script content as string, or None if read fails
        """
        try:
            return script_path.read_text(encoding='utf-8')
        except Exception as e:
            self._log_verbose(f"Failed to read {script_path}: {e}")
            return None
            
    def _clamp_score(self, score: int) -> int:
        """
        Clamp score to valid range [MIN_SCORE, MAX_COMPONENT_SCORE].
        
        Args:
            score: Raw score value
            
        Returns:
            Score clamped to valid range
        """
        return max(MIN_SCORE, min(score, MAX_COMPONENT_SCORE))
        
    def _score_patterns(
        self,
        content: str,
        script_name: str,
        dangerous_patterns: List[Tuple[re.Pattern, str, int]],
        safe_patterns: List[Tuple[re.Pattern, str, int]],
        base_score: int
    ) -> Tuple[int, List[str]]:
        """
        Generic pattern scoring method.
        
        This method evaluates a script against lists of dangerous and safe patterns,
        applying penalties for dangerous patterns found and bonuses for safe patterns.
        
        Args:
            content: Script content to analyze
            script_name: Name of the script (for findings)
            dangerous_patterns: List of (pattern, description, penalty) tuples
            safe_patterns: List of (pattern, description, bonus) tuples
            base_score: Starting score before adjustments
            
        Returns:
            Tuple of (final_score, findings_list)
        """
        score = base_score
        findings = []
        
        # Check for dangerous patterns
        for pattern, description, penalty in dangerous_patterns:
            matches = pattern.findall(content)
            if matches:
                score += penalty  # Penalty is negative
                findings.append(f"{script_name}: {description} ({len(matches)} occurrence(s))")
                
        # Check for safe patterns
        for pattern, description, bonus in safe_patterns:
            if pattern.search(content):
                score += bonus
                self._log_verbose(f"Safe pattern found in {script_name}: {description}")
                
        return self._clamp_score(score), findings
        
    def score_sensitive_data_exposure(self) -> Tuple[float, List[str]]:
        """
        Score sensitive data exposure prevention.
        
        Evaluates scripts for:
        - Hardcoded passwords, API keys, secrets, tokens, private keys
        - Multi-line string credentials
        - F-string sensitive data
        - Base64 encoded secrets
        - JWT tokens
        - Connection strings with credentials
        
        Returns:
            Tuple of (average_score, findings_list)
        """
        if not self.scripts:
            return float(MAX_COMPONENT_SCORE), []
            
        scores = []
        all_findings = []
        
        # Define dangerous patterns with severity-based penalties
        dangerous_patterns = [
            (PATTERN_HARDCODED_PASSWORD, 'hardcoded password', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_HARDCODED_API_KEY, 'hardcoded API key', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_HARDCODED_SECRET, 'hardcoded secret', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_HARDCODED_TOKEN, 'hardcoded token', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_HARDCODED_PRIVATE_KEY, 'hardcoded private key', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_HARDCODED_AWS_KEY, 'hardcoded AWS key', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_HARDCODED_AWS_SECRET, 'hardcoded AWS secret', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_MULTILINE_STRING, 'multi-line string credential', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_FSTRING_SENSITIVE, 'f-string sensitive data', HIGH_SEVERITY_PENALTY),
            (PATTERN_BASE64_SECRET, 'base64 encoded secret', MEDIUM_SEVERITY_PENALTY),
            (PATTERN_JWT_TOKEN, 'JWT token in code', HIGH_SEVERITY_PENALTY),
            (PATTERN_CONNECTION_STRING, 'connection string with credentials', HIGH_SEVERITY_PENALTY),
        ]
        
        # Safe patterns get bonus points
        safe_patterns = [
            (PATTERN_SAFE_ENV_VAR, 'safe environment variable usage', SAFE_PATTERN_BONUS),
        ]
        
        for script_path in self.scripts:
            content = self._get_script_content(script_path)
            if content is None:
                continue
                
            score, findings = self._score_patterns(
                content=content,
                script_name=script_path.name,
                dangerous_patterns=dangerous_patterns,
                safe_patterns=safe_patterns,
                base_score=BASE_SCORE_SENSITIVE_DATA
            )
            
            scores.append(score)
            all_findings.extend(findings)
            
        avg_score = sum(scores) / len(scores) if scores else 0.0
        return avg_score, all_findings
        
    def score_safe_file_operations(self) -> Tuple[float, List[str]]:
        """
        Score safe file operations.
        
        Evaluates scripts for:
        - Path traversal vulnerabilities (basic, URL-encoded, Unicode, null bytes)
        - Unsafe path construction
        - Safe patterns (pathlib, basename, validation)
        
        Returns:
            Tuple of (average_score, findings_list)
        """
        if not self.scripts:
            return float(MAX_COMPONENT_SCORE), []
            
        scores = []
        all_findings = []
        
        # Dangerous patterns with severity-based penalties
        dangerous_patterns = [
            (PATTERN_PATH_TRAVERSAL_BASIC, 'basic path traversal', HIGH_SEVERITY_PENALTY),
            (PATTERN_PATH_TRAVERSAL_WINDOWS, 'Windows-style path traversal', HIGH_SEVERITY_PENALTY),
            (PATTERN_PATH_TRAVERSAL_URL_ENCODED, 'URL-encoded path traversal', HIGH_SEVERITY_PENALTY),
            (PATTERN_PATH_TRAVERSAL_UNICODE, 'Unicode-encoded path traversal', HIGH_SEVERITY_PENALTY),
            (PATTERN_NULL_BYTE, 'null byte injection', HIGH_SEVERITY_PENALTY),
            (PATTERN_PATH_CONCAT, 'potential path injection via concatenation', MEDIUM_SEVERITY_PENALTY),
            (PATTERN_USER_INPUT_PATH, 'user input in path construction', MEDIUM_SEVERITY_PENALTY),
        ]
        
        # Safe patterns get bonus points
        safe_patterns = [
            (PATTERN_SAFE_BASENAME, 'uses basename for safety', SAFE_PATTERN_BONUS),
            (PATTERN_SAFE_PATHLIB, 'uses pathlib', SAFE_PATTERN_BONUS),
            (PATTERN_PATH_VALIDATION, 'path validation', SAFE_PATTERN_BONUS),
            (PATTERN_PATH_RESOLVE, 'path resolution', SAFE_PATTERN_BONUS),
        ]
        
        for script_path in self.scripts:
            content = self._get_script_content(script_path)
            if content is None:
                continue
                
            score, findings = self._score_patterns(
                content=content,
                script_name=script_path.name,
                dangerous_patterns=dangerous_patterns,
                safe_patterns=safe_patterns,
                base_score=BASE_SCORE_FILE_OPS
            )
            
            scores.append(score)
            all_findings.extend(findings)
            
        avg_score = sum(scores) / len(scores) if scores else 0.0
        return avg_score, all_findings
        
    def score_command_injection_prevention(self) -> Tuple[float, List[str]]:
        """
        Score command injection prevention.
        
        Evaluates scripts for:
        - os.system(), os.popen() usage
        - subprocess with shell=True
        - eval(), exec() usage
        - asyncio.create_subprocess_shell()
        - pexpect.spawn()
        - Safe patterns (shlex.quote, shell=False)
        
        Returns:
            Tuple of (average_score, findings_list)
        """
        if not self.scripts:
            return float(MAX_COMPONENT_SCORE), []
            
        scores = []
        all_findings = []
        
        # Dangerous patterns with severity-based penalties
        dangerous_patterns = [
            (PATTERN_OS_SYSTEM, 'os.system usage - potential command injection', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_OS_POPEN, 'os.popen usage', HIGH_SEVERITY_PENALTY),
            (PATTERN_EVAL, 'eval usage - code injection risk', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_EXEC, 'exec usage - code injection risk', CRITICAL_VULNERABILITY_PENALTY),
            (PATTERN_SUBPROCESS_SHELL_TRUE, 'subprocess with shell=True', HIGH_SEVERITY_PENALTY),
            (PATTERN_ASYNCIO_SHELL, 'asyncio.create_subprocess_shell()', HIGH_SEVERITY_PENALTY),
            (PATTERN_PEXPECT_SPAWN, 'pexpect.spawn()', MEDIUM_SEVERITY_PENALTY),
        ]
        
        # Safe patterns get bonus points
        safe_patterns = [
            (PATTERN_SAFE_SUBPROCESS, 'safe subprocess usage (shell=False)', GOOD_PRACTICE_BONUS),
            (PATTERN_SHLEX_QUOTE, 'shell escaping with shlex.quote', GOOD_PRACTICE_BONUS),
            (PATTERN_SHLEX_SPLIT, 'safe argument splitting with shlex.split', GOOD_PRACTICE_BONUS),
        ]
        
        for script_path in self.scripts:
            content = self._get_script_content(script_path)
            if content is None:
                continue
                
            score, findings = self._score_patterns(
                content=content,
                script_name=script_path.name,
                dangerous_patterns=dangerous_patterns,
                safe_patterns=safe_patterns,
                base_score=BASE_SCORE_COMMAND_INJECTION
            )
            
            scores.append(score)
            all_findings.extend(findings)
            
        avg_score = sum(scores) / len(scores) if scores else 0.0
        return avg_score, all_findings
        
    def score_input_validation(self) -> Tuple[float, List[str]]:
        """
        Score input validation quality.
        
        Evaluates scripts for:
        - argparse usage for CLI validation
        - Error handling patterns
        - Type checking (isinstance)
        - Regex validation
        - Validation/sanitization functions
        
        Returns:
            Tuple of (average_score, suggestions_list)
        """
        if not self.scripts:
            return float(MAX_COMPONENT_SCORE), []
            
        scores = []
        suggestions = []
        
        # Good validation patterns (each gives bonus points)
        validation_patterns = [
            (PATTERN_ARGPARSE, GOOD_PRACTICE_BONUS),
            (PATTERN_TRY_EXCEPT, SAFE_PATTERN_BONUS),
            (PATTERN_INPUT_CHECK, SAFE_PATTERN_BONUS),
            (PATTERN_ISINSTANCE, SAFE_PATTERN_BONUS),
            (PATTERN_ISDIGIT, SAFE_PATTERN_BONUS),
            (PATTERN_REGEX_VALIDATION, SAFE_PATTERN_BONUS),
            (PATTERN_VALIDATOR_CLASS, GOOD_PRACTICE_BONUS),
            (PATTERN_VALIDATE_FUNC, SAFE_PATTERN_BONUS),
            (PATTERN_SANITIZE_FUNC, SAFE_PATTERN_BONUS),
        ]
        
        for script_path in self.scripts:
            content = self._get_script_content(script_path)
            if content is None:
                continue
                
            score = BASE_SCORE_INPUT_VALIDATION
            
            # Check for validation patterns
            for pattern, bonus in validation_patterns:
                if pattern.search(content):
                    score += bonus
                    
            scores.append(self._clamp_score(score))
            
        avg_score = sum(scores) / len(scores) if scores else 0.0
        
        if avg_score < 15:
            suggestions.append("Add input validation with argparse, type checking, and error handling")
            
        return avg_score, suggestions
        
    def get_overall_score(self) -> Dict[str, Any]:
        """
        Calculate overall security score and return detailed results.
        
        Returns:
            Dictionary containing:
            - overall_score: Weighted average of all components
            - components: Individual component scores
            - findings: List of security issues found
            - suggestions: Improvement suggestions
        """
        # Score each component
        sensitive_score, sensitive_findings = self.score_sensitive_data_exposure()
        file_ops_score, file_ops_findings = self.score_safe_file_operations()
        command_injection_score, command_findings = self.score_command_injection_prevention()
        input_validation_score, input_suggestions = self.score_input_validation()
        
        # Calculate overall score (equal weight: 25% each)
        overall_score = (
            sensitive_score * 0.25 +
            file_ops_score * 0.25 +
            command_injection_score * 0.25 +
            input_validation_score * 0.25
        )
        
        # Collect all findings
        all_findings = sensitive_findings + file_ops_findings + command_findings
        
        # Generate suggestions based on findings
        suggestions = input_suggestions.copy()
        if sensitive_findings:
            suggestions.append("Remove hardcoded credentials and use environment variables or secure config")
        if file_ops_findings:
            suggestions.append("Validate and sanitize file paths, use pathlib for safe path handling")
        if command_findings:
            suggestions.append("Avoid shell=True in subprocess, use shlex.quote for shell arguments")
            
        # Critical vulnerability check - if any critical issues, cap the score
        critical_patterns = [
            PATTERN_HARDCODED_PASSWORD, PATTERN_HARDCODED_API_KEY,
            PATTERN_HARDCODED_PRIVATE_KEY, PATTERN_OS_SYSTEM,
            PATTERN_EVAL, PATTERN_EXEC
        ]
        
        has_critical = False
        for script_path in self.scripts:
            content = self._get_script_content(script_path)
            if content is None:
                continue
            for pattern in critical_patterns:
                if pattern.search(content):
                    has_critical = True
                    break
            if has_critical:
                break
                
        if has_critical:
            overall_score = min(overall_score, 30)  # Cap at 30 if critical vulnerabilities exist
            
        return {
            'overall_score': round(overall_score, 1),
            'components': {
                'sensitive_data_exposure': round(sensitive_score, 1),
                'safe_file_operations': round(file_ops_score, 1),
                'command_injection_prevention': round(command_injection_score, 1),
                'input_validation': round(input_validation_score, 1),
            },
            'findings': all_findings,
            'suggestions': suggestions,
            'has_critical_vulnerabilities': has_critical,
        }