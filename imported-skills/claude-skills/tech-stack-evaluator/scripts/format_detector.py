"""
Input Format Detector.

Automatically detects input format (text, YAML, JSON, URLs) and parses
accordingly for technology stack evaluation requests.
"""

from typing import Dict, Any, Optional, Tuple
import json
import re


class FormatDetector:
    """Detect and parse various input formats for stack evaluation."""

    def __init__(self, input_data: str):
        """
        Initialize format detector with raw input.

        Args:
            input_data: Raw input string from user
        """
        self.raw_input = input_data.strip()
        self.detected_format = None
        self.parsed_data = None

    def detect_format(self) -> str:
        """
        Detect the input format.

        Returns:
            Format type: 'json', 'yaml', 'url', 'text'
        """
        # Try JSON first
        if self._is_json():
            self.detected_format = 'json'
            return 'json'

        # Try YAML
        if self._is_yaml():
            self.detected_format = 'yaml'
            return 'yaml'

        # Check for URLs
        if self._contains_urls():
            self.detected_format = 'url'
            return 'url'

        # Default to conversational text
        self.detected_format = 'text'
        return 'text'

    def _is_json(self) -> bool:
        """Check if input is valid JSON."""
        try:
            json.loads(self.raw_input)
            return True
        except (json.JSONDecodeError, ValueError):
            return False

    def _is_yaml(self) -> bool:
        """
        Check if input looks like YAML.

        Returns:
            True if input appears to be YAML format
        """
        # YAML indicators
        yaml_patterns = [
            r'^\s*[\w\-]+\s*:',  # Key-value pairs
            r'^\s*-\s+',  # List items
            r':\s*$',  # Trailing colons
        ]

        # Must not be JSON
        if self._is_json():
            return False

        # Check for YAML patterns
        lines = self.raw_input.split('\n')
        yaml_line_count = 0

        for line in lines:
            for pattern in yaml_patterns:
                if re.match(pattern, line):
                    yaml_line_count += 1
                    break

        # If >50% of lines match YAML patterns, consider it YAML
        if len(lines) > 0 and yaml_line_count / len(lines) > 0.5:
            return True

        return False

    def _contains_urls(self) -> bool:
        """Check if input contains URLs."""
        url_pattern = r'https?://[^\s]+'
        return bool(re.search(url_pattern, self.raw_input))

    def parse(self) -> Dict[str, Any]:
        """
        Parse input based on detected format.

        Returns:
            Parsed data dictionary
        """
        if self.detected_format is None:
            self.detect_format()

        if self.detected_format == 'json':
            self.parsed_data = self._parse_json()
        elif self.detected_format == 'yaml':
            self.parsed_data = self._parse_yaml()
        elif self.detected_format == 'url':
            self.parsed_data = self._parse_urls()
        else:  # text
            self.parsed_data = self._parse_text()

        return self.parsed_data

    def _parse_json(self) -> Dict[str, Any]:
        """Parse JSON input."""
        try:
            data = json.loads(self.raw_input)
            return self._normalize_structure(data)
        except json.JSONDecodeError:
            return {'error': 'Invalid JSON', 'raw': self.raw_input}

    def _parse_yaml(self) -> Dict[str, Any]:
        """
        Parse YAML-like input (simplified, no external dependencies).

        Returns:
            Parsed dictionary
        """
        result = {}
        current_section = None
        current_list = None

        lines = self.raw_input.split('\n')

        for line in lines:
            stripped = line.strip()
            if not stripped or stripped.startswith('#'):
                continue

            # Key-value pair
            if ':' in stripped:
                key, value = stripped.split(':', 1)
                key = key.strip()
                value = value.strip()

                # Empty value might indicate nested structure
                if not value:
                    current_section = key
                    result[current_section] = {}
                    current_list = None
                else:
                    if current_section:
                        result[current_section][key] = self._parse_value(value)
                    else:
                        result[key] = self._parse_value(value)

            # List item
            elif stripped.startswith('-'):
                item = stripped[1:].strip()
                if current_section:
                    if current_list is None:
                        current_list = []
                        result[current_section] = current_list
                    current_list.append(self._parse_value(item))

        return self._normalize_structure(result)

    def _parse_value(self, value: str) -> Any:
        """
        Parse a value string to appropriate type.

        Args:
            value: Value string

        Returns:
            Parsed value (str, int, float, bool)
        """
        value = value.strip()

        # Boolean
        if value.lower() in ['true', 'yes']:
            return True
        if value.lower() in ['false', 'no']:
            return False

        # Number
        try:
            if '.' in value:
                return float(value)
            else:
                return int(value)
        except ValueError:
            pass

        # String (remove quotes if present)
        if value.startswith('"') and value.endswith('"'):
            return value[1:-1]
        if value.startswith("'") and value.endswith("'"):
            return value[1:-1]

        return value

    def _parse_urls(self) -> Dict[str, Any]:
        """Parse URLs from input."""
        url_pattern = r'https?://[^\s]+'
        urls = re.findall(url_pattern, self.raw_input)

        # Categorize URLs
        github_urls = [u for u in urls if 'github.com' in u]
        npm_urls = [u for u in urls if 'npmjs.com' in u or 'npm.io' in u]
        other_urls = [u for u in urls if u not in github_urls and u not in npm_urls]

        # Also extract any text context
        text_without_urls = re.sub(url_pattern, '', self.raw_input).strip()

        result = {
            'format': 'url',
            'urls': {
                'github': github_urls,
                'npm': npm_urls,
                'other': other_urls
            },
            'context': text_without_urls
        }

        return self._normalize_structure(result)

    def _parse_text(self) -> Dict[str, Any]:
        """Parse conversational text input."""
        text = self.raw_input.lower()

        # Extract technologies being compared
        technologies = self._extract_technologies(text)

        # Extract use case
        use_case = self._extract_use_case(text)

        # Extract priorities
        priorities = self._extract_priorities(text)

        # Detect analysis type
        analysis_type = self._detect_analysis_type(text)

        result = {
            'format': 'text',
            'technologies': technologies,
            'use_case': use_case,
            'priorities': priorities,
            'analysis_type': analysis_type,
            'raw_text': self.raw_input
        }

        return self._normalize_structure(result)

    def _extract_technologies(self, text: str) -> list:
        """
        Extract technology names from text.

        Args:
            text: Lowercase text

        Returns:
            List of identified technologies
        """
        # Common technologies pattern
        tech_keywords = [
            'react', 'vue', 'angular', 'svelte', 'next.js', 'nuxt.js',
            'node.js', 'python', 'java', 'go', 'rust', 'ruby',
            'postgresql', 'postgres', 'mysql', 'mongodb', 'redis',
            'aws', 'azure', 'gcp', 'google cloud',
            'docker', 'kubernetes', 'k8s',
            'express', 'fastapi', 'django', 'flask', 'spring boot'
        ]

        found = []
        for tech in tech_keywords:
            if tech in text:
                # Normalize names
                normalized = {
                    'postgres': 'PostgreSQL',
                    'next.js': 'Next.js',
                    'nuxt.js': 'Nuxt.js',
                    'node.js': 'Node.js',
                    'k8s': 'Kubernetes',
                    'gcp': 'Google Cloud Platform'
                }.get(tech, tech.title())

                if normalized not in found:
                    found.append(normalized)

        return found if found else ['Unknown']

    def _extract_use_case(self, text: str) -> str:
        """
        Extract use case description from text.

        Args:
            text: Lowercase text

        Returns:
            Use case description
        """
        use_case_keywords = {
            'real-time': 'Real-time application',
            'collaboration': 'Collaboration platform',
            'saas': 'SaaS application',
            'dashboard': 'Dashboard application',
            'api': 'API-heavy application',
            'data-intensive': 'Data-intensive application',
            'e-commerce': 'E-commerce platform',
            'enterprise': 'Enterprise application'
        }

        for keyword, description in use_case_keywords.items():
            if keyword in text:
                return description

        return 'General purpose application'

    def _extract_priorities(self, text: str) -> list:
        """
        Extract priority criteria from text.

        Args:
            text: Lowercase text

        Returns:
            List of priorities
        """
        priority_keywords = {
            'performance': 'Performance',
            'scalability': 'Scalability',
            'developer experience': 'Developer experience',
            'ecosystem': 'Ecosystem',
            'learning curve': 'Learning curve',
            'cost': 'Cost',
            'security': 'Security',
            'compliance': 'Compliance'
        }

        priorities = []
        for keyword, priority in priority_keywords.items():
            if keyword in text:
                priorities.append(priority)

        return priorities if priorities else ['Developer experience', 'Performance']

    def _detect_analysis_type(self, text: str) -> str:
        """
        Detect type of analysis requested.

        Args:
            text: Lowercase text

        Returns:
            Analysis type
        """
        type_keywords = {
            'migration': 'migration_analysis',
            'migrate': 'migration_analysis',
            'tco': 'tco_analysis',
            'total cost': 'tco_analysis',
            'security': 'security_analysis',
            'compliance': 'security_analysis',
            'compare': 'comparison',
            'vs': 'comparison',
            'evaluate': 'evaluation'
        }

        for keyword, analysis_type in type_keywords.items():
            if keyword in text:
                return analysis_type

        return 'comparison'  # Default

    def _normalize_structure(self, data: Dict[str, Any]) -> Dict[str, Any]:
        """
        Normalize parsed data to standard structure.

        Args:
            data: Parsed data dictionary

        Returns:
            Normalized data structure
        """
        # Ensure standard keys exist
        standard_keys = [
            'technologies',
            'use_case',
            'priorities',
            'analysis_type',
            'format'
        ]

        normalized = data.copy()

        for key in standard_keys:
            if key not in normalized:
                # Set defaults
                defaults = {
                    'technologies': [],
                    'use_case': 'general',
                    'priorities': [],
                    'analysis_type': 'comparison',
                    'format': self.detected_format or 'unknown'
                }
                normalized[key] = defaults.get(key)

        return normalized

    def get_format_info(self) -> Dict[str, Any]:
        """
        Get information about detected format.

        Returns:
            Format detection metadata
        """
        return {
            'detected_format': self.detected_format,
            'input_length': len(self.raw_input),
            'line_count': len(self.raw_input.split('\n')),
            'parsing_successful': self.parsed_data is not None
        }
