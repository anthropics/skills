#!/usr/bin/env python3
"""
Script Tester - Tests Python scripts in a skill directory

This script validates and tests Python scripts within a skill directory by checking
syntax, imports, runtime execution, argparse functionality, and output formats.
It ensures scripts meet quality standards and function correctly.

Usage:
    python script_tester.py <skill_path> [--timeout SECONDS] [--json] [--verbose]

Author: Claude Skills Engineering Team
Version: 1.0.0
Dependencies: Python Standard Library Only
"""

import argparse
import ast
import json
import os
import subprocess
import sys
import tempfile
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple, Union
import threading


class TestError(Exception):
    """Custom exception for testing errors"""
    pass


class ScriptTestResult:
    """Container for individual script test results"""
    
    def __init__(self, script_path: str):
        self.script_path = script_path
        self.script_name = Path(script_path).name
        self.timestamp = datetime.utcnow().isoformat() + "Z"
        self.tests = {}
        self.overall_status = "PENDING"
        self.execution_time = 0.0
        self.errors = []
        self.warnings = []
        
    def add_test(self, test_name: str, passed: bool, message: str = "", details: Dict = None):
        """Add a test result"""
        self.tests[test_name] = {
            "passed": passed,
            "message": message,
            "details": details or {}
        }
        
    def add_error(self, error: str):
        """Add an error message"""
        self.errors.append(error)
        
    def add_warning(self, warning: str):
        """Add a warning message"""
        self.warnings.append(warning)
        
    def calculate_status(self):
        """Calculate overall test status"""
        if not self.tests:
            self.overall_status = "NO_TESTS"
            return
            
        failed_tests = [name for name, result in self.tests.items() if not result["passed"]]
        
        if not failed_tests:
            self.overall_status = "PASS"
        elif len(failed_tests) <= len(self.tests) // 2:
            self.overall_status = "PARTIAL"
        else:
            self.overall_status = "FAIL"


class TestSuite:
    """Container for all test results"""
    
    def __init__(self, skill_path: str):
        self.skill_path = skill_path
        self.timestamp = datetime.utcnow().isoformat() + "Z"
        self.script_results = {}
        self.summary = {}
        self.global_errors = []
        
    def add_script_result(self, result: ScriptTestResult):
        """Add a script test result"""
        self.script_results[result.script_name] = result
        
    def add_global_error(self, error: str):
        """Add a global error message"""
        self.global_errors.append(error)
        
    def calculate_summary(self):
        """Calculate summary statistics"""
        if not self.script_results:
            self.summary = {
                "total_scripts": 0,
                "passed": 0,
                "partial": 0,
                "failed": 0,
                "overall_status": "NO_SCRIPTS"
            }
            return
            
        statuses = [result.overall_status for result in self.script_results.values()]
        
        self.summary = {
            "total_scripts": len(self.script_results),
            "passed": statuses.count("PASS"),
            "partial": statuses.count("PARTIAL"),
            "failed": statuses.count("FAIL"),
            "no_tests": statuses.count("NO_TESTS")
        }
        
        # Determine overall status
        if self.summary["failed"] == 0 and self.summary["no_tests"] == 0:
            self.summary["overall_status"] = "PASS"
        elif self.summary["passed"] > 0:
            self.summary["overall_status"] = "PARTIAL"
        else:
            self.summary["overall_status"] = "FAIL"


class ScriptTester:
    """Main script testing engine"""
    
    def __init__(self, skill_path: str, timeout: int = 30, verbose: bool = False):
        self.skill_path = Path(skill_path).resolve()
        self.timeout = timeout
        self.verbose = verbose
        self.test_suite = TestSuite(str(self.skill_path))
        
    def log_verbose(self, message: str):
        """Log verbose message if verbose mode enabled"""
        if self.verbose:
            print(f"[VERBOSE] {message}", file=sys.stderr)
            
    def test_all_scripts(self) -> TestSuite:
        """Main entry point - test all scripts in the skill"""
        try:
            self.log_verbose(f"Starting script testing for {self.skill_path}")
            
            # Check if skill path exists
            if not self.skill_path.exists():
                self.test_suite.add_global_error(f"Skill path does not exist: {self.skill_path}")
                return self.test_suite
                
            scripts_dir = self.skill_path / "scripts"
            if not scripts_dir.exists():
                self.test_suite.add_global_error("No scripts directory found")
                return self.test_suite
                
            # Find all Python scripts
            python_files = list(scripts_dir.glob("*.py"))
            if not python_files:
                self.test_suite.add_global_error("No Python scripts found in scripts directory")
                return self.test_suite
                
            self.log_verbose(f"Found {len(python_files)} Python scripts to test")
            
            # Test each script
            for script_path in python_files:
                try:
                    result = self.test_single_script(script_path)
                    self.test_suite.add_script_result(result)
                except Exception as e:
                    # Create a failed result for the script
                    result = ScriptTestResult(str(script_path))
                    result.add_error(f"Failed to test script: {str(e)}")
                    result.overall_status = "FAIL"
                    self.test_suite.add_script_result(result)
                    
            # Calculate summary
            self.test_suite.calculate_summary()
            
        except Exception as e:
            self.test_suite.add_global_error(f"Testing failed with exception: {str(e)}")
            
        return self.test_suite
        
    def test_single_script(self, script_path: Path) -> ScriptTestResult:
        """Test a single Python script comprehensively"""
        result = ScriptTestResult(str(script_path))
        start_time = time.time()
        
        try:
            self.log_verbose(f"Testing script: {script_path.name}")
            
            # Read script content
            try:
                content = script_path.read_text(encoding='utf-8')
            except Exception as e:
                result.add_test("file_readable", False, f"Cannot read file: {str(e)}")
                result.add_error(f"Cannot read script file: {str(e)}")
                result.overall_status = "FAIL"
                return result
                
            result.add_test("file_readable", True, "Script file is readable")
            
            # Test 1: Syntax validation
            self._test_syntax(content, result)
            
            # Test 2: Import validation  
            self._test_imports(content, result)
            
            # Test 3: Argparse validation
            self._test_argparse_implementation(content, result)
            
            # Test 4: Main guard validation
            self._test_main_guard(content, result)
            
            # Test 5: Runtime execution tests
            if result.tests.get("syntax_valid", {}).get("passed", False):
                self._test_script_execution(script_path, result)
                
            # Test 6: Help functionality
            if result.tests.get("syntax_valid", {}).get("passed", False):
                self._test_help_functionality(script_path, result)
                
            # Test 7: Sample data processing (if available)
            self._test_sample_data_processing(script_path, result)
            
            # Test 8: Output format validation
            self._test_output_formats(script_path, result)
            
        except Exception as e:
            result.add_error(f"Unexpected error during testing: {str(e)}")
            
        finally:
            result.execution_time = time.time() - start_time
            result.calculate_status()
            
        return result
        
    def _test_syntax(self, content: str, result: ScriptTestResult):
        """Test Python syntax validity"""
        self.log_verbose("Testing syntax...")
        
        try:
            ast.parse(content)
            result.add_test("syntax_valid", True, "Python syntax is valid")
        except SyntaxError as e:
            result.add_test("syntax_valid", False, f"Syntax error: {str(e)}", 
                           {"error": str(e), "line": getattr(e, 'lineno', 'unknown')})
            result.add_error(f"Syntax error: {str(e)}")
            
    def _test_imports(self, content: str, result: ScriptTestResult):
        """Test import statements for external dependencies"""
        self.log_verbose("Testing imports...")
        
        try:
            tree = ast.parse(content)
            external_imports = self._find_external_imports(tree)
            
            if not external_imports:
                result.add_test("imports_valid", True, "Uses only standard library imports")
            else:
                result.add_test("imports_valid", False, 
                               f"Uses external imports: {', '.join(external_imports)}",
                               {"external_imports": external_imports})
                result.add_error(f"External imports detected: {', '.join(external_imports)}")
                
        except Exception as e:
            result.add_test("imports_valid", False, f"Error analyzing imports: {str(e)}")
            
    def _find_external_imports(self, tree: ast.AST) -> List[str]:
        """Find external (non-stdlib) imports"""
        # Comprehensive standard library module list
        stdlib_modules = {
            # Built-in modules
            'argparse', 'ast', 'json', 'os', 'sys', 'pathlib', 'datetime', 'typing',
            'collections', 're', 'math', 'random', 'itertools', 'functools', 'operator',
            'csv', 'sqlite3', 'urllib', 'http', 'html', 'xml', 'email', 'base64',
            'hashlib', 'hmac', 'secrets', 'tempfile', 'shutil', 'glob', 'fnmatch',
            'subprocess', 'threading', 'multiprocessing', 'queue', 'time', 'calendar',
            'locale', 'gettext', 'logging', 'warnings', 'unittest', 'doctest',
            'pickle', 'copy', 'pprint', 'reprlib', 'enum', 'dataclasses',
            'contextlib', 'abc', 'atexit', 'traceback', 'gc', 'weakref', 'types',
            'decimal', 'fractions', 'statistics', 'cmath', 'platform', 'errno',
            'io', 'codecs', 'unicodedata', 'stringprep', 'textwrap', 'string',
            'struct', 'difflib', 'heapq', 'bisect', 'array', 'uuid', 'mmap',
            'ctypes', 'winreg', 'msvcrt', 'winsound', 'posix', 'pwd', 'grp',
            'crypt', 'termios', 'tty', 'pty', 'fcntl', 'resource', 'nis',
            'syslog', 'signal', 'socket', 'ssl', 'select', 'selectors',
            'asyncio', 'asynchat', 'asyncore', 'netrc', 'xdrlib', 'plistlib',
            'mailbox', 'mimetypes', 'encodings', 'pkgutil', 'modulefinder',
            'runpy', 'importlib', 'imp', 'zipimport', 'zipfile', 'tarfile',
            'gzip', 'bz2', 'lzma', 'zlib', 'binascii', 'quopri', 'uu',
            'configparser', 'netrc', 'xdrlib', 'plistlib', 'token', 'tokenize',
            'keyword', 'heapq', 'bisect', 'array', 'weakref', 'types',
            'copyreg', 'shelve', 'marshal', 'dbm', 'sqlite3', 'zoneinfo'
        }
        
        external_imports = []
        
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    module_name = alias.name.split('.')[0]
                    if module_name not in stdlib_modules and not module_name.startswith('_'):
                        external_imports.append(alias.name)
                        
            elif isinstance(node, ast.ImportFrom) and node.module:
                module_name = node.module.split('.')[0]
                if module_name not in stdlib_modules and not module_name.startswith('_'):
                    external_imports.append(node.module)
                    
        return list(set(external_imports))
        
    def _test_argparse_implementation(self, content: str, result: ScriptTestResult):
        """Test argparse implementation"""
        self.log_verbose("Testing argparse implementation...")
        
        try:
            tree = ast.parse(content)
            
            # Check for argparse import
            has_argparse_import = False
            has_parser_creation = False
            has_parse_args = False
            
            for node in ast.walk(tree):
                if isinstance(node, (ast.Import, ast.ImportFrom)):
                    if (isinstance(node, ast.Import) and 
                        any(alias.name == 'argparse' for alias in node.names)):
                        has_argparse_import = True
                    elif (isinstance(node, ast.ImportFrom) and 
                          node.module == 'argparse'):
                        has_argparse_import = True
                        
                elif isinstance(node, ast.Call):
                    # Check for ArgumentParser creation
                    if (isinstance(node.func, ast.Attribute) and
                        isinstance(node.func.value, ast.Name) and
                        node.func.value.id == 'argparse' and
                        node.func.attr == 'ArgumentParser'):
                        has_parser_creation = True
                        
                    # Check for parse_args call
                    if (isinstance(node.func, ast.Attribute) and
                        node.func.attr == 'parse_args'):
                        has_parse_args = True
                        
            argparse_score = sum([has_argparse_import, has_parser_creation, has_parse_args])
            
            if argparse_score == 3:
                result.add_test("argparse_implementation", True, "Complete argparse implementation found")
            elif argparse_score > 0:
                result.add_test("argparse_implementation", False, 
                               "Partial argparse implementation", 
                               {"missing_components": [
                                   comp for comp, present in [
                                       ("import", has_argparse_import),
                                       ("parser_creation", has_parser_creation),
                                       ("parse_args", has_parse_args)
                                   ] if not present
                               ]})
                result.add_warning("Incomplete argparse implementation")
            else:
                result.add_test("argparse_implementation", False, "No argparse implementation found")
                result.add_error("Script should use argparse for command-line arguments")
                
        except Exception as e:
            result.add_test("argparse_implementation", False, f"Error analyzing argparse: {str(e)}")
            
    def _test_main_guard(self, content: str, result: ScriptTestResult):
        """Test for if __name__ == '__main__' guard"""
        self.log_verbose("Testing main guard...")
        
        has_main_guard = 'if __name__ == "__main__"' in content or "if __name__ == '__main__'" in content
        
        if has_main_guard:
            result.add_test("main_guard", True, "Has proper main guard")
        else:
            result.add_test("main_guard", False, "Missing main guard")
            result.add_error("Script should have 'if __name__ == \"__main__\"' guard")
            
    def _test_script_execution(self, script_path: Path, result: ScriptTestResult):
        """Test basic script execution"""
        self.log_verbose("Testing script execution...")
        
        try:
            # Try to run the script with no arguments (should not crash immediately)
            process = subprocess.run(
                [sys.executable, str(script_path)],
                capture_output=True,
                text=True,
                timeout=self.timeout,
                cwd=script_path.parent
            )
            
            # Script might exit with error code if no args provided, but shouldn't crash
            if process.returncode in (0, 1, 2):  # 0=success, 1=general error, 2=misuse
                result.add_test("basic_execution", True, 
                               f"Script runs without crashing (exit code: {process.returncode})")
            else:
                result.add_test("basic_execution", False,
                               f"Script crashed with exit code {process.returncode}",
                               {"stdout": process.stdout, "stderr": process.stderr})
                               
        except subprocess.TimeoutExpired:
            result.add_test("basic_execution", False, 
                           f"Script execution timed out after {self.timeout} seconds")
            result.add_error(f"Script execution timeout ({self.timeout}s)")
            
        except Exception as e:
            result.add_test("basic_execution", False, f"Execution error: {str(e)}")
            result.add_error(f"Script execution failed: {str(e)}")
            
    def _test_help_functionality(self, script_path: Path, result: ScriptTestResult):
        """Test --help functionality"""
        self.log_verbose("Testing help functionality...")
        
        try:
            # Test --help flag
            process = subprocess.run(
                [sys.executable, str(script_path), '--help'],
                capture_output=True,
                text=True,
                timeout=self.timeout,
                cwd=script_path.parent
            )
            
            if process.returncode == 0:
                help_output = process.stdout
                
                # Check for reasonable help content
                help_indicators = ['usage:', 'positional arguments:', 'optional arguments:', 
                                 'options:', 'description:', 'help']
                has_help_content = any(indicator in help_output.lower() for indicator in help_indicators)
                
                if has_help_content and len(help_output.strip()) > 50:
                    result.add_test("help_functionality", True, "Provides comprehensive help text")
                else:
                    result.add_test("help_functionality", False, 
                                   "Help text is too brief or missing key sections",
                                   {"help_output": help_output})
                    result.add_warning("Help text could be more comprehensive")
                    
            else:
                result.add_test("help_functionality", False, 
                               f"Help command failed with exit code {process.returncode}",
                               {"stderr": process.stderr})
                result.add_error("--help flag does not work properly")
                
        except subprocess.TimeoutExpired:
            result.add_test("help_functionality", False, "Help command timed out")
            
        except Exception as e:
            result.add_test("help_functionality", False, f"Help test error: {str(e)}")
            
    def _test_sample_data_processing(self, script_path: Path, result: ScriptTestResult):
        """Test script against sample data if available"""
        self.log_verbose("Testing sample data processing...")
        
        assets_dir = self.skill_path / "assets"
        if not assets_dir.exists():
            result.add_test("sample_data_processing", True, "No sample data to test (assets dir missing)")
            return
            
        # Look for sample input files
        sample_files = list(assets_dir.rglob("*sample*")) + list(assets_dir.rglob("*test*"))
        sample_files = [f for f in sample_files if f.is_file() and not f.name.startswith('.')]
        
        if not sample_files:
            result.add_test("sample_data_processing", True, "No sample data files found to test")
            return
            
        tested_files = 0
        successful_tests = 0
        
        for sample_file in sample_files[:3]:  # Test up to 3 sample files
            try:
                self.log_verbose(f"Testing with sample file: {sample_file.name}")
                
                # Try to run script with the sample file as input
                process = subprocess.run(
                    [sys.executable, str(script_path), str(sample_file)],
                    capture_output=True,
                    text=True,
                    timeout=self.timeout,
                    cwd=script_path.parent
                )
                
                tested_files += 1
                
                if process.returncode == 0:
                    successful_tests += 1
                else:
                    self.log_verbose(f"Sample test failed for {sample_file.name}: {process.stderr}")
                    
            except subprocess.TimeoutExpired:
                tested_files += 1
                result.add_warning(f"Sample data test timed out for {sample_file.name}")
            except Exception as e:
                tested_files += 1
                self.log_verbose(f"Sample test error for {sample_file.name}: {str(e)}")
                
        if tested_files == 0:
            result.add_test("sample_data_processing", True, "No testable sample data found")
        elif successful_tests == tested_files:
            result.add_test("sample_data_processing", True, 
                           f"Successfully processed all {tested_files} sample files")
        elif successful_tests > 0:
            result.add_test("sample_data_processing", False,
                           f"Processed {successful_tests}/{tested_files} sample files",
                           {"success_rate": successful_tests / tested_files})
            result.add_warning("Some sample data processing failed")
        else:
            result.add_test("sample_data_processing", False, 
                           "Failed to process any sample data files")
            result.add_error("Script cannot process sample data")
            
    def _test_output_formats(self, script_path: Path, result: ScriptTestResult):
        """Test output format compliance"""
        self.log_verbose("Testing output formats...")
        
        # Test if script supports JSON output
        json_support = False
        human_readable_support = False
        
        try:
            # Read script content to check for output format indicators
            content = script_path.read_text(encoding='utf-8')
            
            # Look for JSON-related code
            if any(indicator in content.lower() for indicator in ['json.dump', 'json.load', '"json"', '--json']):
                json_support = True
                
            # Look for human-readable output indicators
            if any(indicator in content for indicator in ['print(', 'format(', 'f"', "f'"]):
                human_readable_support = True
                
            # Try running with --json flag if it looks like it supports it
            if '--json' in content:
                try:
                    process = subprocess.run(
                        [sys.executable, str(script_path), '--json', '--help'],
                        capture_output=True,
                        text=True,
                        timeout=10,
                        cwd=script_path.parent
                    )
                    if process.returncode == 0:
                        json_support = True
                except:
                    pass
                    
            # Evaluate dual output support
            if json_support and human_readable_support:
                result.add_test("output_formats", True, "Supports both JSON and human-readable output")
            elif json_support or human_readable_support:
                format_type = "JSON" if json_support else "human-readable"
                result.add_test("output_formats", False,
                               f"Supports only {format_type} output",
                               {"json_support": json_support, "human_readable_support": human_readable_support})
                result.add_warning("Consider adding dual output format support")
            else:
                result.add_test("output_formats", False, "No clear output format support detected")
                result.add_warning("Output format support is unclear")
                
        except Exception as e:
            result.add_test("output_formats", False, f"Error testing output formats: {str(e)}")


class TestReportFormatter:
    """Formats test reports for output"""
    
    @staticmethod
    def format_json(test_suite: TestSuite) -> str:
        """Format test suite as JSON"""
        return json.dumps({
            "skill_path": test_suite.skill_path,
            "timestamp": test_suite.timestamp,
            "summary": test_suite.summary,
            "global_errors": test_suite.global_errors,
            "script_results": {
                name: {
                    "script_path": result.script_path,
                    "timestamp": result.timestamp,
                    "overall_status": result.overall_status,
                    "execution_time": round(result.execution_time, 2),
                    "tests": result.tests,
                    "errors": result.errors,
                    "warnings": result.warnings
                }
                for name, result in test_suite.script_results.items()
            }
        }, indent=2)
        
    @staticmethod
    def format_human_readable(test_suite: TestSuite) -> str:
        """Format test suite as human-readable text"""
        lines = []
        lines.append("=" * 60)
        lines.append("SCRIPT TESTING REPORT")
        lines.append("=" * 60)
        lines.append(f"Skill: {test_suite.skill_path}")
        lines.append(f"Timestamp: {test_suite.timestamp}")
        lines.append("")
        
        # Summary
        if test_suite.summary:
            lines.append("SUMMARY:")
            lines.append(f"  Total Scripts: {test_suite.summary['total_scripts']}")
            lines.append(f"  Passed: {test_suite.summary['passed']}")
            lines.append(f"  Partial: {test_suite.summary['partial']}")
            lines.append(f"  Failed: {test_suite.summary['failed']}")
            lines.append(f"  Overall Status: {test_suite.summary['overall_status']}")
            lines.append("")
            
        # Global errors
        if test_suite.global_errors:
            lines.append("GLOBAL ERRORS:")
            for error in test_suite.global_errors:
                lines.append(f"  • {error}")
            lines.append("")
            
        # Individual script results
        for script_name, result in test_suite.script_results.items():
            lines.append(f"SCRIPT: {script_name}")
            lines.append(f"  Status: {result.overall_status}")
            lines.append(f"  Execution Time: {result.execution_time:.2f}s")
            lines.append("")
            
            # Tests
            if result.tests:
                lines.append("  TESTS:")
                for test_name, test_result in result.tests.items():
                    status = "✓ PASS" if test_result["passed"] else "✗ FAIL"
                    lines.append(f"    {status}: {test_result['message']}")
                lines.append("")
                
            # Errors
            if result.errors:
                lines.append("  ERRORS:")
                for error in result.errors:
                    lines.append(f"    • {error}")
                lines.append("")
                
            # Warnings
            if result.warnings:
                lines.append("  WARNINGS:")
                for warning in result.warnings:
                    lines.append(f"    • {warning}")
                lines.append("")
                
            lines.append("-" * 40)
            lines.append("")
            
        return "\n".join(lines)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Test Python scripts in a skill directory",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python script_tester.py engineering/my-skill
  python script_tester.py engineering/my-skill --timeout 60 --json
  python script_tester.py engineering/my-skill --verbose

Test Categories:
  - Syntax validation (AST parsing)
  - Import validation (stdlib only)
  - Argparse implementation
  - Main guard presence
  - Basic execution testing
  - Help functionality
  - Sample data processing
  - Output format compliance
        """
    )
    
    parser.add_argument("skill_path",
                       help="Path to the skill directory containing scripts to test")
    parser.add_argument("--timeout",
                       type=int,
                       default=30,
                       help="Timeout for script execution tests in seconds (default: 30)")
    parser.add_argument("--json",
                       action="store_true",
                       help="Output results in JSON format")
    parser.add_argument("--verbose",
                       action="store_true", 
                       help="Enable verbose logging")
                       
    args = parser.parse_args()
    
    try:
        # Create tester and run tests
        tester = ScriptTester(args.skill_path, args.timeout, args.verbose)
        test_suite = tester.test_all_scripts()
        
        # Format and output results
        if args.json:
            print(TestReportFormatter.format_json(test_suite))
        else:
            print(TestReportFormatter.format_human_readable(test_suite))
            
        # Exit with appropriate code
        if test_suite.global_errors:
            sys.exit(1)
        elif test_suite.summary.get("overall_status") == "FAIL":
            sys.exit(1)
        elif test_suite.summary.get("overall_status") == "PARTIAL":
            sys.exit(2)  # Partial success
        else:
            sys.exit(0)  # Success
            
    except KeyboardInterrupt:
        print("\nTesting interrupted by user", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"Testing failed: {str(e)}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()