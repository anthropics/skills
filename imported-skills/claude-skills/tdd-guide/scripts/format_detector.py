"""
Format detection module.

Automatically detects programming language, testing framework, and file formats.
"""

from typing import Dict, List, Any, Optional, Tuple
import re


class FormatDetector:
    """Detect language, framework, and file formats automatically."""

    def __init__(self):
        """Initialize format detector."""
        self.detected_language = None
        self.detected_framework = None

    def detect_language(self, code: str) -> str:
        """
        Detect programming language from code.

        Args:
            code: Source code

        Returns:
            Detected language (typescript, javascript, python, java, unknown)
        """
        # TypeScript patterns
        if self._is_typescript(code):
            self.detected_language = "typescript"
            return "typescript"

        # JavaScript patterns
        if self._is_javascript(code):
            self.detected_language = "javascript"
            return "javascript"

        # Python patterns
        if self._is_python(code):
            self.detected_language = "python"
            return "python"

        # Java patterns
        if self._is_java(code):
            self.detected_language = "java"
            return "java"

        self.detected_language = "unknown"
        return "unknown"

    def _is_typescript(self, code: str) -> bool:
        """Check if code is TypeScript."""
        ts_patterns = [
            r'\binterface\s+\w+',  # interface definitions
            r':\s*\w+\s*[=;]',  # type annotations
            r'\btype\s+\w+\s*=',  # type aliases
            r'<\w+>',  # generic types
            r'import.*from.*[\'"]',  # ES6 imports with types
        ]

        # Must have multiple TypeScript-specific patterns
        matches = sum(1 for pattern in ts_patterns if re.search(pattern, code))
        return matches >= 2

    def _is_javascript(self, code: str) -> bool:
        """Check if code is JavaScript."""
        js_patterns = [
            r'\bconst\s+\w+',  # const declarations
            r'\blet\s+\w+',  # let declarations
            r'=>',  # arrow functions
            r'function\s+\w+',  # function declarations
            r'require\([\'"]',  # CommonJS require
        ]

        matches = sum(1 for pattern in js_patterns if re.search(pattern, code))
        return matches >= 2

    def _is_python(self, code: str) -> bool:
        """Check if code is Python."""
        py_patterns = [
            r'\bdef\s+\w+',  # function definitions
            r'\bclass\s+\w+',  # class definitions
            r'import\s+\w+',  # import statements
            r'from\s+\w+\s+import',  # from imports
            r'^\s*#.*$',  # Python comments
            r':\s*$',  # Python colons
        ]

        matches = sum(1 for pattern in py_patterns if re.search(pattern, code, re.MULTILINE))
        return matches >= 3

    def _is_java(self, code: str) -> bool:
        """Check if code is Java."""
        java_patterns = [
            r'\bpublic\s+class',  # public class
            r'\bprivate\s+\w+',  # private members
            r'\bpublic\s+\w+\s+\w+\s*\(',  # public methods
            r'import\s+java\.',  # Java imports
            r'\bvoid\s+\w+\s*\(',  # void methods
        ]

        matches = sum(1 for pattern in java_patterns if re.search(pattern, code))
        return matches >= 2

    def detect_test_framework(self, code: str) -> str:
        """
        Detect testing framework from test code.

        Args:
            code: Test code

        Returns:
            Detected framework (jest, vitest, pytest, junit, mocha, unknown)
        """
        # Jest patterns
        if 'from \'@jest/globals\'' in code or '@jest/' in code:
            self.detected_framework = "jest"
            return "jest"

        # Vitest patterns
        if 'from \'vitest\'' in code or 'import { vi }' in code:
            self.detected_framework = "vitest"
            return "vitest"

        # Pytest patterns
        if 'import pytest' in code or 'def test_' in code:
            self.detected_framework = "pytest"
            return "pytest"

        # Unittest patterns
        if 'import unittest' in code and 'unittest.TestCase' in code:
            self.detected_framework = "unittest"
            return "unittest"

        # JUnit patterns
        if '@Test' in code and 'import org.junit' in code:
            self.detected_framework = "junit"
            return "junit"

        # Mocha patterns
        if 'describe(' in code and 'it(' in code:
            self.detected_framework = "mocha"
            return "mocha"

        self.detected_framework = "unknown"
        return "unknown"

    def detect_coverage_format(self, content: str) -> str:
        """
        Detect coverage report format.

        Args:
            content: Coverage report content

        Returns:
            Format type (lcov, json, xml, unknown)
        """
        content_stripped = content.strip()

        # LCOV format
        if content_stripped.startswith('TN:') or 'SF:' in content_stripped[:200]:
            return "lcov"

        # JSON format
        if content_stripped.startswith('{'):
            try:
                import json
                json.loads(content_stripped)
                return "json"
            except:
                pass

        # XML format
        if content_stripped.startswith('<?xml') or content_stripped.startswith('<coverage'):
            return "xml"

        return "unknown"

    def detect_input_format(self, input_data: str) -> Dict[str, Any]:
        """
        Detect input format and extract relevant information.

        Args:
            input_data: Input data (could be code, coverage report, etc.)

        Returns:
            Detection results with format, language, framework
        """
        result = {
            'format': 'unknown',
            'language': 'unknown',
            'framework': 'unknown',
            'content_type': 'unknown'
        }

        # Detect if it's a coverage report
        coverage_format = self.detect_coverage_format(input_data)
        if coverage_format != "unknown":
            result['format'] = coverage_format
            result['content_type'] = 'coverage_report'
            return result

        # Detect if it's source code
        language = self.detect_language(input_data)
        if language != "unknown":
            result['language'] = language
            result['content_type'] = 'source_code'

        # Detect if it's test code
        framework = self.detect_test_framework(input_data)
        if framework != "unknown":
            result['framework'] = framework
            result['content_type'] = 'test_code'

        return result

    def extract_file_info(self, file_path: str) -> Dict[str, str]:
        """
        Extract information from file path.

        Args:
            file_path: Path to file

        Returns:
            File information (extension, likely language, likely purpose)
        """
        import os

        file_name = os.path.basename(file_path)
        file_ext = os.path.splitext(file_name)[1].lower()

        # Extension to language mapping
        ext_to_lang = {
            '.ts': 'typescript',
            '.tsx': 'typescript',
            '.js': 'javascript',
            '.jsx': 'javascript',
            '.py': 'python',
            '.java': 'java',
            '.kt': 'kotlin',
            '.go': 'go',
            '.rs': 'rust',
        }

        # Test file patterns
        is_test = any(pattern in file_name.lower()
                     for pattern in ['test', 'spec', '_test.', '.test.'])

        return {
            'file_name': file_name,
            'extension': file_ext,
            'language': ext_to_lang.get(file_ext, 'unknown'),
            'is_test': is_test,
            'purpose': 'test' if is_test else 'source'
        }

    def suggest_test_file_name(self, source_file: str, framework: str) -> str:
        """
        Suggest test file name for source file.

        Args:
            source_file: Source file path
            framework: Testing framework

        Returns:
            Suggested test file name
        """
        import os

        base_name = os.path.splitext(os.path.basename(source_file))[0]
        ext = os.path.splitext(source_file)[1]

        if framework in ['jest', 'vitest', 'mocha']:
            return f"{base_name}.test{ext}"
        elif framework in ['pytest', 'unittest']:
            return f"test_{base_name}.py"
        elif framework in ['junit', 'testng']:
            return f"{base_name.capitalize()}Test.java"
        else:
            return f"{base_name}_test{ext}"

    def identify_test_patterns(self, code: str) -> List[str]:
        """
        Identify test patterns in code.

        Args:
            code: Test code

        Returns:
            List of identified patterns (AAA, Given-When-Then, etc.)
        """
        patterns = []

        # Arrange-Act-Assert pattern
        if any(comment in code.lower() for comment in ['// arrange', '# arrange', '// act', '# act']):
            patterns.append('AAA (Arrange-Act-Assert)')

        # Given-When-Then pattern
        if any(comment in code.lower() for comment in ['given', 'when', 'then']):
            patterns.append('Given-When-Then')

        # Setup/Teardown pattern
        if any(keyword in code for keyword in ['beforeEach', 'afterEach', 'setUp', 'tearDown']):
            patterns.append('Setup-Teardown')

        # Mocking pattern
        if any(keyword in code.lower() for keyword in ['mock', 'stub', 'spy']):
            patterns.append('Mocking/Stubbing')

        # Parameterized tests
        if any(keyword in code for keyword in ['@pytest.mark.parametrize', 'test.each', '@ParameterizedTest']):
            patterns.append('Parameterized Tests')

        return patterns if patterns else ['No specific pattern detected']

    def analyze_project_structure(self, file_paths: List[str]) -> Dict[str, Any]:
        """
        Analyze project structure from file paths.

        Args:
            file_paths: List of file paths in project

        Returns:
            Project structure analysis
        """
        languages = {}
        test_frameworks = []
        source_files = []
        test_files = []

        for file_path in file_paths:
            file_info = self.extract_file_info(file_path)

            # Count languages
            lang = file_info['language']
            if lang != 'unknown':
                languages[lang] = languages.get(lang, 0) + 1

            # Categorize files
            if file_info['is_test']:
                test_files.append(file_path)
            else:
                source_files.append(file_path)

        # Determine primary language
        primary_language = max(languages.items(), key=lambda x: x[1])[0] if languages else 'unknown'

        return {
            'primary_language': primary_language,
            'languages': languages,
            'source_file_count': len(source_files),
            'test_file_count': len(test_files),
            'test_ratio': len(test_files) / len(source_files) if source_files else 0,
            'suggested_framework': self._suggest_framework(primary_language)
        }

    def _suggest_framework(self, language: str) -> str:
        """Suggest testing framework based on language."""
        framework_map = {
            'typescript': 'jest or vitest',
            'javascript': 'jest or mocha',
            'python': 'pytest',
            'java': 'junit',
            'kotlin': 'junit',
            'go': 'testing package',
            'rust': 'cargo test',
        }

        return framework_map.get(language, 'unknown')

    def detect_environment(self) -> Dict[str, str]:
        """
        Detect execution environment (CLI, Desktop, API).

        Returns:
            Environment information
        """
        # This is a placeholder - actual detection would use environment variables
        # or other runtime checks
        return {
            'environment': 'cli',  # Could be 'desktop', 'api'
            'output_preference': 'terminal-friendly'  # Could be 'rich-markdown', 'json'
        }
