#!/usr/bin/env python3
"""
Skill Validator - Validates skill directories against quality standards

This script validates a skill directory structure, documentation, and Python scripts
against the claude-skills ecosystem standards. It checks for required files, proper
formatting, and compliance with tier-specific requirements.

Usage:
    python skill_validator.py <skill_path> [--tier TIER] [--json] [--verbose]

Author: Claude Skills Engineering Team
Version: 1.0.0
Dependencies: Python Standard Library Only
"""

import argparse
import ast
import json
import re
import sys
try:
    import yaml
except ImportError:
    # Minimal YAML subset: parse simple key: value frontmatter without pyyaml
    class _YamlStub:
        class YAMLError(Exception):
            pass
        @staticmethod
        def safe_load(text):
            result = {}
            for line in text.strip().splitlines():
                if ':' in line:
                    key, _, value = line.partition(':')
                    result[key.strip()] = value.strip()
            return result if result else None
    yaml = _YamlStub()
import datetime as dt
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple


class ValidationError(Exception):
    """Custom exception for validation errors"""
    pass


class ValidationReport:
    """Container for validation results"""
    
    def __init__(self, skill_path: str):
        self.skill_path = skill_path
        self.timestamp = dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")
        self.checks = {}
        self.warnings = []
        self.errors = []
        self.suggestions = []
        self.overall_score = 0.0
        self.compliance_level = "FAIL"
        
    def add_check(self, check_name: str, passed: bool, message: str = "", score: float = 0.0):
        """Add a validation check result"""
        self.checks[check_name] = {
            "passed": passed,
            "message": message,
            "score": score
        }
        
    def add_warning(self, message: str):
        """Add a warning message"""
        self.warnings.append(message)
        
    def add_error(self, message: str):
        """Add an error message"""
        self.errors.append(message)
        
    def add_suggestion(self, message: str):
        """Add an improvement suggestion"""
        self.suggestions.append(message)
        
    def calculate_overall_score(self):
        """Calculate overall compliance score"""
        if not self.checks:
            self.overall_score = 0.0
            return
            
        total_score = sum(check["score"] for check in self.checks.values())
        max_score = len(self.checks) * 1.0
        self.overall_score = (total_score / max_score) * 100 if max_score > 0 else 0.0
        
        # Determine compliance level
        if self.overall_score >= 90:
            self.compliance_level = "EXCELLENT"
        elif self.overall_score >= 75:
            self.compliance_level = "GOOD"
        elif self.overall_score >= 60:
            self.compliance_level = "ACCEPTABLE"
        elif self.overall_score >= 40:
            self.compliance_level = "NEEDS_IMPROVEMENT"
        else:
            self.compliance_level = "POOR"


class SkillValidator:
    """Main skill validation engine"""
    
    # Tier requirements
    TIER_REQUIREMENTS = {
        "BASIC": {
            "min_skill_md_lines": 100,
            "min_scripts": 1,
            "script_size_range": (100, 300),
            "required_dirs": ["scripts"],
            "optional_dirs": ["assets", "references", "expected_outputs"],
            "features_required": ["argparse", "main_guard"]
        },
        "STANDARD": {
            "min_skill_md_lines": 200,
            "min_scripts": 1,
            "script_size_range": (300, 500),
            "required_dirs": ["scripts", "assets", "references"],
            "optional_dirs": ["expected_outputs"],
            "features_required": ["argparse", "main_guard", "json_output", "help_text"]
        },
        "POWERFUL": {
            "min_skill_md_lines": 300,
            "min_scripts": 2,
            "script_size_range": (500, 800),
            "required_dirs": ["scripts", "assets", "references", "expected_outputs"],
            "optional_dirs": [],
            "features_required": ["argparse", "main_guard", "json_output", "help_text", "error_handling"]
        }
    }
    
    REQUIRED_SKILL_MD_SECTIONS = [
        "Name", "Description", "Features", "Usage", "Examples"
    ]
    
    FRONTMATTER_REQUIRED_FIELDS = [
        "Name", "Tier", "Category", "Dependencies", "Author", "Version"
    ]
    
    def __init__(self, skill_path: str, target_tier: Optional[str] = None, verbose: bool = False):
        self.skill_path = Path(skill_path).resolve()
        self.target_tier = target_tier
        self.verbose = verbose
        self.report = ValidationReport(str(self.skill_path))
        
    def log_verbose(self, message: str):
        """Log verbose message if verbose mode enabled"""
        if self.verbose:
            print(f"[VERBOSE] {message}", file=sys.stderr)
            
    def validate_skill_structure(self) -> ValidationReport:
        """Main validation entry point"""
        try:
            self.log_verbose(f"Starting validation of {self.skill_path}")
            
            # Check if path exists
            if not self.skill_path.exists():
                self.report.add_error(f"Skill path does not exist: {self.skill_path}")
                return self.report
                
            if not self.skill_path.is_dir():
                self.report.add_error(f"Skill path is not a directory: {self.skill_path}")
                return self.report
                
            # Run all validation checks
            self._validate_required_files()
            self._validate_skill_md()
            self._validate_readme()
            self._validate_directory_structure()
            self._validate_python_scripts()
            self._validate_tier_compliance()
            
            # Calculate overall score
            self.report.calculate_overall_score()
            
            self.log_verbose(f"Validation completed. Score: {self.report.overall_score:.1f}")
            
        except Exception as e:
            self.report.add_error(f"Validation failed with exception: {str(e)}")
            
        return self.report
        
    def _validate_required_files(self):
        """Validate presence of required files"""
        self.log_verbose("Checking required files...")
        
        # Check SKILL.md
        skill_md_path = self.skill_path / "SKILL.md"
        if skill_md_path.exists():
            self.report.add_check("skill_md_exists", True, "SKILL.md found", 1.0)
        else:
            self.report.add_check("skill_md_exists", False, "SKILL.md missing", 0.0)
            self.report.add_error("SKILL.md is required but missing")
            
        # Check README.md
        readme_path = self.skill_path / "README.md"
        if readme_path.exists():
            self.report.add_check("readme_exists", True, "README.md found", 1.0)
        else:
            self.report.add_check("readme_exists", False, "README.md missing", 0.0)
            self.report.add_warning("README.md is recommended but missing")
            self.report.add_suggestion("Add README.md with usage instructions and examples")
            
    def _validate_skill_md(self):
        """Validate SKILL.md content and format"""
        self.log_verbose("Validating SKILL.md...")
        
        skill_md_path = self.skill_path / "SKILL.md"
        if not skill_md_path.exists():
            return
            
        try:
            content = skill_md_path.read_text(encoding='utf-8')
            lines = content.split('\n')
            line_count = len([line for line in lines if line.strip()])
            
            # Check line count
            min_lines = self._get_tier_requirement("min_skill_md_lines", 100)
            if line_count >= min_lines:
                self.report.add_check("skill_md_length", True, 
                                     f"SKILL.md has {line_count} lines (≥{min_lines})", 1.0)
            else:
                self.report.add_check("skill_md_length", False,
                                     f"SKILL.md has {line_count} lines (<{min_lines})", 0.0)
                self.report.add_error(f"SKILL.md too short: {line_count} lines, minimum {min_lines}")
                
            # Validate frontmatter
            self._validate_frontmatter(content)
            
            # Check required sections
            self._validate_required_sections(content)
            
        except Exception as e:
            self.report.add_check("skill_md_readable", False, f"Error reading SKILL.md: {str(e)}", 0.0)
            self.report.add_error(f"Cannot read SKILL.md: {str(e)}")
            
    def _validate_frontmatter(self, content: str):
        """Validate SKILL.md frontmatter"""
        self.log_verbose("Validating frontmatter...")
        
        # Extract frontmatter
        if content.startswith('---'):
            try:
                end_marker = content.find('---', 3)
                if end_marker == -1:
                    self.report.add_check("frontmatter_format", False, 
                                         "Frontmatter closing marker not found", 0.0)
                    return
                    
                frontmatter_text = content[3:end_marker].strip()
                frontmatter = yaml.safe_load(frontmatter_text)
                
                if not isinstance(frontmatter, dict):
                    self.report.add_check("frontmatter_format", False, 
                                         "Frontmatter is not a valid dictionary", 0.0)
                    return
                    
                # Check required fields
                missing_fields = []
                for field in self.FRONTMATTER_REQUIRED_FIELDS:
                    if field not in frontmatter:
                        missing_fields.append(field)
                        
                if not missing_fields:
                    self.report.add_check("frontmatter_complete", True, 
                                         "All required frontmatter fields present", 1.0)
                else:
                    self.report.add_check("frontmatter_complete", False,
                                         f"Missing fields: {', '.join(missing_fields)}", 0.0)
                    self.report.add_error(f"Missing frontmatter fields: {', '.join(missing_fields)}")
                    
            except yaml.YAMLError as e:
                self.report.add_check("frontmatter_format", False, 
                                     f"Invalid YAML frontmatter: {str(e)}", 0.0)
                self.report.add_error(f"Invalid YAML frontmatter: {str(e)}")
                
        else:
            self.report.add_check("frontmatter_exists", False, 
                                 "No frontmatter found", 0.0)
            self.report.add_error("SKILL.md must start with YAML frontmatter")
            
    def _validate_required_sections(self, content: str):
        """Validate required sections in SKILL.md"""
        self.log_verbose("Checking required sections...")
        
        missing_sections = []
        for section in self.REQUIRED_SKILL_MD_SECTIONS:
            pattern = rf'^#+\s*{re.escape(section)}\s*$'
            if not re.search(pattern, content, re.MULTILINE | re.IGNORECASE):
                missing_sections.append(section)
                
        if not missing_sections:
            self.report.add_check("required_sections", True,
                                 "All required sections present", 1.0)
        else:
            self.report.add_check("required_sections", False,
                                 f"Missing sections: {', '.join(missing_sections)}", 0.0)
            self.report.add_error(f"Missing required sections: {', '.join(missing_sections)}")
            
    def _validate_readme(self):
        """Validate README.md content"""
        self.log_verbose("Validating README.md...")
        
        readme_path = self.skill_path / "README.md"
        if not readme_path.exists():
            return
            
        try:
            content = readme_path.read_text(encoding='utf-8')
            
            # Check minimum content length
            if len(content.strip()) >= 200:
                self.report.add_check("readme_substantial", True,
                                     "README.md has substantial content", 1.0)
            else:
                self.report.add_check("readme_substantial", False,
                                     "README.md content is too brief", 0.5)
                self.report.add_suggestion("Expand README.md with more detailed usage instructions")
                
        except Exception as e:
            self.report.add_check("readme_readable", False,
                                 f"Error reading README.md: {str(e)}", 0.0)
            
    def _validate_directory_structure(self):
        """Validate directory structure against tier requirements"""
        self.log_verbose("Validating directory structure...")
        
        required_dirs = self._get_tier_requirement("required_dirs", ["scripts"])
        optional_dirs = self._get_tier_requirement("optional_dirs", [])
        
        # Check required directories
        missing_required = []
        for dir_name in required_dirs:
            dir_path = self.skill_path / dir_name
            if dir_path.exists() and dir_path.is_dir():
                self.report.add_check(f"dir_{dir_name}_exists", True,
                                     f"{dir_name}/ directory found", 1.0)
            else:
                missing_required.append(dir_name)
                self.report.add_check(f"dir_{dir_name}_exists", False,
                                     f"{dir_name}/ directory missing", 0.0)
                
        if missing_required:
            self.report.add_error(f"Missing required directories: {', '.join(missing_required)}")
            
        # Check optional directories and provide suggestions
        missing_optional = []
        for dir_name in optional_dirs:
            dir_path = self.skill_path / dir_name
            if not (dir_path.exists() and dir_path.is_dir()):
                missing_optional.append(dir_name)
                
        if missing_optional:
            self.report.add_suggestion(f"Consider adding optional directories: {', '.join(missing_optional)}")
            
    def _validate_python_scripts(self):
        """Validate Python scripts in the scripts directory"""
        self.log_verbose("Validating Python scripts...")
        
        scripts_dir = self.skill_path / "scripts"
        if not scripts_dir.exists():
            return
            
        python_files = list(scripts_dir.glob("*.py"))
        min_scripts = self._get_tier_requirement("min_scripts", 1)
        
        # Check minimum number of scripts
        if len(python_files) >= min_scripts:
            self.report.add_check("min_scripts_count", True,
                                 f"Found {len(python_files)} Python scripts (≥{min_scripts})", 1.0)
        else:
            self.report.add_check("min_scripts_count", False,
                                 f"Found {len(python_files)} Python scripts (<{min_scripts})", 0.0)
            self.report.add_error(f"Insufficient scripts: {len(python_files)}, minimum {min_scripts}")
            
        # Validate each script
        for script_path in python_files:
            self._validate_single_script(script_path)
            
    def _validate_single_script(self, script_path: Path):
        """Validate a single Python script"""
        script_name = script_path.name
        self.log_verbose(f"Validating script: {script_name}")
        
        try:
            content = script_path.read_text(encoding='utf-8')
            
            # Count lines of code (excluding empty lines and comments)
            lines = content.split('\n')
            loc = len([line for line in lines if line.strip() and not line.strip().startswith('#')])
            
            # Check script size against tier requirements
            size_range = self._get_tier_requirement("script_size_range", (100, 1000))
            min_size, max_size = size_range
            
            if min_size <= loc <= max_size:
                self.report.add_check(f"script_size_{script_name}", True,
                                     f"{script_name} has {loc} LOC (within {min_size}-{max_size})", 1.0)
            else:
                self.report.add_check(f"script_size_{script_name}", False,
                                     f"{script_name} has {loc} LOC (outside {min_size}-{max_size})", 0.5)
                if loc < min_size:
                    self.report.add_suggestion(f"Consider expanding {script_name} (currently {loc} LOC)")
                else:
                    self.report.add_suggestion(f"Consider refactoring {script_name} (currently {loc} LOC)")
                    
            # Parse and validate Python syntax
            try:
                tree = ast.parse(content)
                self.report.add_check(f"script_syntax_{script_name}", True,
                                     f"{script_name} has valid Python syntax", 1.0)
                                     
                # Check for required features
                self._validate_script_features(tree, script_name, content)
                
            except SyntaxError as e:
                self.report.add_check(f"script_syntax_{script_name}", False,
                                     f"{script_name} has syntax error: {str(e)}", 0.0)
                self.report.add_error(f"Syntax error in {script_name}: {str(e)}")
                
        except Exception as e:
            self.report.add_check(f"script_readable_{script_name}", False,
                                 f"Cannot read {script_name}: {str(e)}", 0.0)
            self.report.add_error(f"Cannot read {script_name}: {str(e)}")
            
    def _validate_script_features(self, tree: ast.AST, script_name: str, content: str):
        """Validate required script features"""
        required_features = self._get_tier_requirement("features_required", ["argparse", "main_guard"])
        
        # Check for argparse usage
        if "argparse" in required_features:
            has_argparse = self._check_argparse_usage(tree)
            self.report.add_check(f"script_argparse_{script_name}", has_argparse,
                                 f"{'Uses' if has_argparse else 'Missing'} argparse in {script_name}", 1.0 if has_argparse else 0.0)
            if not has_argparse:
                self.report.add_error(f"{script_name} must use argparse for command-line arguments")
                
        # Check for main guard
        if "main_guard" in required_features:
            has_main_guard = 'if __name__ == "__main__"' in content
            self.report.add_check(f"script_main_guard_{script_name}", has_main_guard,
                                 f"{'Has' if has_main_guard else 'Missing'} main guard in {script_name}", 1.0 if has_main_guard else 0.0)
            if not has_main_guard:
                self.report.add_error(f"{script_name} must have 'if __name__ == \"__main__\"' guard")
                
        # Check for external imports (should only use stdlib)
        external_imports = self._check_external_imports(tree)
        if not external_imports:
            self.report.add_check(f"script_imports_{script_name}", True,
                                 f"{script_name} uses only standard library", 1.0)
        else:
            self.report.add_check(f"script_imports_{script_name}", False,
                                 f"{script_name} uses external imports: {', '.join(external_imports)}", 0.0)
            self.report.add_error(f"{script_name} uses external imports: {', '.join(external_imports)}")
            
    def _check_argparse_usage(self, tree: ast.AST) -> bool:
        """Check if the script uses argparse"""
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name == 'argparse':
                        return True
            elif isinstance(node, ast.ImportFrom):
                if node.module == 'argparse':
                    return True
        return False
        
    def _check_external_imports(self, tree: ast.AST) -> List[str]:
        """Check for external (non-stdlib) imports"""
        # Simplified check - a more comprehensive solution would use a stdlib module list
        stdlib_modules = {
            'argparse', 'ast', 'json', 'os', 'sys', 'pathlib', 'datetime', 'typing',
            'collections', 're', 'math', 'random', 'itertools', 'functools', 'operator',
            'csv', 'sqlite3', 'urllib', 'http', 'html', 'xml', 'email', 'base64',
            'hashlib', 'hmac', 'secrets', 'tempfile', 'shutil', 'glob', 'fnmatch',
            'subprocess', 'threading', 'multiprocessing', 'queue', 'time', 'calendar',
            'zoneinfo', 'locale', 'gettext', 'logging', 'warnings', 'unittest',
            'doctest', 'pickle', 'copy', 'pprint', 'reprlib', 'enum', 'dataclasses',
            'contextlib', 'abc', 'atexit', 'traceback', 'gc', 'weakref', 'types',
            'copy', 'pprint', 'reprlib', 'enum', 'decimal', 'fractions', 'statistics',
            'cmath', 'platform', 'errno', 'io', 'codecs', 'unicodedata', 'stringprep',
            'textwrap', 'string', 'struct', 'difflib', 'heapq', 'bisect', 'array',
            'weakref', 'types', 'copyreg', 'uuid', 'mmap', 'ctypes'
        }
        
        external_imports = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    module_name = alias.name.split('.')[0]
                    if module_name not in stdlib_modules:
                        external_imports.append(alias.name)
            elif isinstance(node, ast.ImportFrom) and node.module:
                module_name = node.module.split('.')[0]
                if module_name not in stdlib_modules:
                    external_imports.append(node.module)
                    
        return list(set(external_imports))
        
    def _validate_tier_compliance(self):
        """Validate overall tier compliance"""
        if not self.target_tier:
            return
            
        self.log_verbose(f"Validating {self.target_tier} tier compliance...")
        
        # This is a summary check - individual checks are done in other methods
        critical_checks = ["skill_md_exists", "min_scripts_count", "skill_md_length"]
        failed_critical = [check for check in critical_checks 
                          if check in self.report.checks and not self.report.checks[check]["passed"]]
                          
        if not failed_critical:
            self.report.add_check("tier_compliance", True,
                                 f"Meets {self.target_tier} tier requirements", 1.0)
        else:
            self.report.add_check("tier_compliance", False,
                                 f"Does not meet {self.target_tier} tier requirements", 0.0)
            self.report.add_error(f"Failed critical checks for {self.target_tier} tier: {', '.join(failed_critical)}")
            
    def _get_tier_requirement(self, requirement: str, default: Any) -> Any:
        """Get tier-specific requirement value"""
        if self.target_tier and self.target_tier in self.TIER_REQUIREMENTS:
            return self.TIER_REQUIREMENTS[self.target_tier].get(requirement, default)
        return default


class ReportFormatter:
    """Formats validation reports for output"""
    
    @staticmethod
    def format_json(report: ValidationReport) -> str:
        """Format report as JSON"""
        return json.dumps({
            "skill_path": report.skill_path,
            "timestamp": report.timestamp,
            "overall_score": round(report.overall_score, 1),
            "compliance_level": report.compliance_level,
            "checks": report.checks,
            "warnings": report.warnings,
            "errors": report.errors,
            "suggestions": report.suggestions
        }, indent=2)
        
    @staticmethod
    def format_human_readable(report: ValidationReport) -> str:
        """Format report as human-readable text"""
        lines = []
        lines.append("=" * 60)
        lines.append("SKILL VALIDATION REPORT")
        lines.append("=" * 60)
        lines.append(f"Skill: {report.skill_path}")
        lines.append(f"Timestamp: {report.timestamp}")
        lines.append(f"Overall Score: {report.overall_score:.1f}/100 ({report.compliance_level})")
        lines.append("")
        
        # Group checks by category
        structure_checks = {k: v for k, v in report.checks.items() if k.startswith(('skill_md', 'readme', 'dir_'))}
        script_checks = {k: v for k, v in report.checks.items() if k.startswith('script_')}
        other_checks = {k: v for k, v in report.checks.items() if k not in structure_checks and k not in script_checks}
        
        if structure_checks:
            lines.append("STRUCTURE VALIDATION:")
            for check_name, result in structure_checks.items():
                status = "✓ PASS" if result["passed"] else "✗ FAIL"
                lines.append(f"  {status}: {result['message']}")
            lines.append("")
            
        if script_checks:
            lines.append("SCRIPT VALIDATION:")
            for check_name, result in script_checks.items():
                status = "✓ PASS" if result["passed"] else "✗ FAIL"
                lines.append(f"  {status}: {result['message']}")
            lines.append("")
            
        if other_checks:
            lines.append("OTHER CHECKS:")
            for check_name, result in other_checks.items():
                status = "✓ PASS" if result["passed"] else "✗ FAIL"
                lines.append(f"  {status}: {result['message']}")
            lines.append("")
            
        if report.errors:
            lines.append("ERRORS:")
            for error in report.errors:
                lines.append(f"  • {error}")
            lines.append("")
            
        if report.warnings:
            lines.append("WARNINGS:")
            for warning in report.warnings:
                lines.append(f"  • {warning}")
            lines.append("")
            
        if report.suggestions:
            lines.append("SUGGESTIONS:")
            for suggestion in report.suggestions:
                lines.append(f"  • {suggestion}")
            lines.append("")
            
        return "\n".join(lines)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Validate skill directories against quality standards",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python skill_validator.py engineering/my-skill
  python skill_validator.py engineering/my-skill --tier POWERFUL --json
  python skill_validator.py engineering/my-skill --verbose

Tier Options:
  BASIC     - Basic skill requirements (100+ lines SKILL.md, 1+ script)
  STANDARD  - Standard skill requirements (200+ lines, advanced features)
  POWERFUL  - Powerful skill requirements (300+ lines, comprehensive features)
        """
    )
    
    parser.add_argument("skill_path", 
                       help="Path to the skill directory to validate")
    parser.add_argument("--tier", 
                       choices=["BASIC", "STANDARD", "POWERFUL"],
                       help="Target tier for validation (optional)")
    parser.add_argument("--json", 
                       action="store_true",
                       help="Output results in JSON format")
    parser.add_argument("--verbose", 
                       action="store_true",
                       help="Enable verbose logging")
    
    args = parser.parse_args()
    
    try:
        # Create validator and run validation
        validator = SkillValidator(args.skill_path, args.tier, args.verbose)
        report = validator.validate_skill_structure()
        
        # Format and output report
        if args.json:
            print(ReportFormatter.format_json(report))
        else:
            print(ReportFormatter.format_human_readable(report))
            
        # Exit with error code if validation failed
        if report.errors or report.overall_score < 60:
            sys.exit(1)
        else:
            sys.exit(0)
            
    except KeyboardInterrupt:
        print("\nValidation interrupted by user", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"Validation failed: {str(e)}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
