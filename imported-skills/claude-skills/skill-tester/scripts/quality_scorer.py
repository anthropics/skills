#!/usr/bin/env python3
"""
Quality Scorer - Scores skills across multiple quality dimensions

This script provides comprehensive quality assessment for skills in the claude-skills
ecosystem by evaluating documentation, code quality, completeness, security, and usability.
Generates letter grades, tier recommendations, and improvement roadmaps.

Usage:
    python quality_scorer.py <skill_path> [--detailed] [--minimum-score SCORE] [--json]

Author: Claude Skills Engineering Team
Version: 2.0.0
Dependencies: Python Standard Library Only
Changelog:
  v2.0.0 - Added Security dimension (opt-in via --include-security flag)
           Default: 4 dimensions × 25% (backward compatible)
           With --include-security: 5 dimensions × 20%
  v1.0.0 - Initial release with 4 dimensions (25% each)
"""

import argparse
import ast
import json
import os
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple

# Import Security Scorer module
from security_scorer import SecurityScorer
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


class QualityDimension:
    """Represents a quality scoring dimension"""
    
    def __init__(self, name: str, weight: float, description: str):
        self.name = name
        self.weight = weight
        self.description = description
        self.score = 0.0
        self.max_score = 100.0
        self.details = {}
        self.suggestions = []
        
    def add_score(self, component: str, score: float, max_score: float, details: str = ""):
        """Add a component score"""
        self.details[component] = {
            "score": score,
            "max_score": max_score,
            "percentage": (score / max_score * 100) if max_score > 0 else 0,
            "details": details
        }
        
    def calculate_final_score(self):
        """Calculate the final weighted score for this dimension"""
        if not self.details:
            self.score = 0.0
            return
            
        total_score = sum(detail["score"] for detail in self.details.values())
        total_max = sum(detail["max_score"] for detail in self.details.values())
        
        self.score = (total_score / total_max * 100) if total_max > 0 else 0.0
        
    def add_suggestion(self, suggestion: str):
        """Add an improvement suggestion"""
        self.suggestions.append(suggestion)


class QualityReport:
    """Container for quality assessment results"""
    
    def __init__(self, skill_path: str):
        self.skill_path = skill_path
        self.timestamp = datetime.utcnow().isoformat() + "Z"
        self.dimensions = {}
        self.overall_score = 0.0
        self.letter_grade = "F"
        self.tier_recommendation = "BASIC"
        self.improvement_roadmap = []
        self.summary_stats = {}
        
    def add_dimension(self, dimension: QualityDimension):
        """Add a quality dimension"""
        self.dimensions[dimension.name] = dimension
        
    def calculate_overall_score(self):
        """Calculate overall weighted score"""
        if not self.dimensions:
            return
            
        total_weighted_score = 0.0
        total_weight = 0.0
        
        for dimension in self.dimensions.values():
            total_weighted_score += dimension.score * dimension.weight
            total_weight += dimension.weight
            
        self.overall_score = total_weighted_score / total_weight if total_weight > 0 else 0.0
        
        # Calculate letter grade
        if self.overall_score >= 95:
            self.letter_grade = "A+"
        elif self.overall_score >= 90:
            self.letter_grade = "A"
        elif self.overall_score >= 85:
            self.letter_grade = "A-"
        elif self.overall_score >= 80:
            self.letter_grade = "B+"
        elif self.overall_score >= 75:
            self.letter_grade = "B"
        elif self.overall_score >= 70:
            self.letter_grade = "B-"
        elif self.overall_score >= 65:
            self.letter_grade = "C+"
        elif self.overall_score >= 60:
            self.letter_grade = "C"
        elif self.overall_score >= 55:
            self.letter_grade = "C-"
        elif self.overall_score >= 50:
            self.letter_grade = "D"
        else:
            self.letter_grade = "F"
            
        # Recommend tier based on overall score and specific criteria
        self._calculate_tier_recommendation()
        
        # Generate improvement roadmap
        self._generate_improvement_roadmap()
        
        # Calculate summary statistics
        self._calculate_summary_stats()
        
    def _calculate_tier_recommendation(self):
        """Calculate recommended tier based on quality scores"""
        doc_score = self.dimensions.get("Documentation", QualityDimension("", 0, "")).score
        code_score = self.dimensions.get("Code Quality", QualityDimension("", 0, "")).score
        completeness_score = self.dimensions.get("Completeness", QualityDimension("", 0, "")).score
        usability_score = self.dimensions.get("Usability", QualityDimension("", 0, "")).score
        security_score = self.dimensions.get("Security", QualityDimension("", 0, "")).score
        
        # Check if Security dimension is included
        has_security = "Security" in self.dimensions
        
        # POWERFUL tier requirements
        if has_security:
            # With Security: all 5 dimensions must be strong
            if (self.overall_score >= 80 and 
                all(score >= 75 for score in [doc_score, code_score, completeness_score, usability_score]) and
                security_score >= 70):
                self.tier_recommendation = "POWERFUL"
                
            # STANDARD tier requirements (with Security)
            elif (self.overall_score >= 70 and 
                  sum(1 for score in [doc_score, code_score, completeness_score, usability_score, security_score] if score >= 65) >= 4 and
                  security_score >= 50):
                self.tier_recommendation = "STANDARD"
        else:
            # Without Security: 4 dimensions must be strong
            if (self.overall_score >= 80 and 
                all(score >= 75 for score in [doc_score, code_score, completeness_score, usability_score])):
                self.tier_recommendation = "POWERFUL"
                
            # STANDARD tier requirements (without Security)
            elif (self.overall_score >= 70 and 
                  sum(1 for score in [doc_score, code_score, completeness_score, usability_score] if score >= 65) >= 3):
                self.tier_recommendation = "STANDARD"
                
        # BASIC tier (minimum viable quality)
        # Falls through to BASIC if no other tier matched
            
    def _generate_improvement_roadmap(self):
        """Generate prioritized improvement suggestions"""
        all_suggestions = []
        
        # Collect suggestions from all dimensions with scores
        for dim_name, dimension in self.dimensions.items():
            for suggestion in dimension.suggestions:
                priority = "HIGH" if dimension.score < 60 else "MEDIUM" if dimension.score < 75 else "LOW"
                all_suggestions.append({
                    "priority": priority,
                    "dimension": dim_name,
                    "suggestion": suggestion,
                    "current_score": dimension.score
                })
                
        # Sort by priority and score
        priority_order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2}
        all_suggestions.sort(key=lambda x: (priority_order[x["priority"]], x["current_score"]))
        
        self.improvement_roadmap = all_suggestions[:10]  # Top 10 suggestions
        
    def _calculate_summary_stats(self):
        """Calculate summary statistics"""
        scores = [dim.score for dim in self.dimensions.values()]
        
        self.summary_stats = {
            "highest_dimension": max(self.dimensions.items(), key=lambda x: x[1].score)[0] if scores else "None",
            "lowest_dimension": min(self.dimensions.items(), key=lambda x: x[1].score)[0] if scores else "None",
            "score_variance": sum((score - self.overall_score) ** 2 for score in scores) / len(scores) if scores else 0,
            "dimensions_above_70": sum(1 for score in scores if score >= 70),
            "dimensions_below_50": sum(1 for score in scores if score < 50)
        }


class QualityScorer:
    """Main quality scoring engine"""
    
    def __init__(self, skill_path: str, detailed: bool = False, verbose: bool = False, include_security: bool = False):
        self.skill_path = Path(skill_path).resolve()
        self.detailed = detailed
        self.verbose = verbose
        self.include_security = include_security
        self.report = QualityReport(str(self.skill_path))
        
    def log_verbose(self, message: str):
        """Log verbose message if verbose mode enabled"""
        if self.verbose:
            print(f"[VERBOSE] {message}", file=sys.stderr)
            
    def assess_quality(self) -> QualityReport:
        """Main quality assessment entry point"""
        try:
            self.log_verbose(f"Starting quality assessment for {self.skill_path}")
            
            # Check if skill path exists
            if not self.skill_path.exists():
                raise ValueError(f"Skill path does not exist: {self.skill_path}")
                
            # Score each dimension
            # Default: 4 dimensions at 25% each (backward compatible)
            # With --include-security: 5 dimensions at 20% each
            weight = 0.20 if self.include_security else 0.25
            
            self._score_documentation(weight)
            self._score_code_quality(weight)
            self._score_completeness(weight)
            
            if self.include_security:
                self._score_security(0.20)
                self._score_usability(0.20)
            else:
                self._score_usability(0.25)
            
            # Calculate overall metrics
            self.report.calculate_overall_score()
            
            self.log_verbose(f"Quality assessment completed. Overall score: {self.report.overall_score:.1f}")
            
        except Exception as e:
            print(f"Quality assessment failed: {str(e)}", file=sys.stderr)
            raise
            
        return self.report
        
    def _score_documentation(self, weight: float = 0.25):
        """Score documentation quality"""
        self.log_verbose("Scoring documentation quality...")
        
        dimension = QualityDimension("Documentation", weight, "Quality of documentation and written materials")
        
        # Score SKILL.md
        self._score_skill_md(dimension)
        
        # Score README.md
        self._score_readme(dimension)
        
        # Score reference documentation
        self._score_references(dimension)
        
        # Score examples and usage clarity
        self._score_examples(dimension)
        
        dimension.calculate_final_score()
        self.report.add_dimension(dimension)
        
    def _score_skill_md(self, dimension: QualityDimension):
        """Score SKILL.md quality"""
        skill_md_path = self.skill_path / "SKILL.md"
        
        if not skill_md_path.exists():
            dimension.add_score("skill_md_existence", 0, 25, "SKILL.md does not exist")
            dimension.add_suggestion("Create comprehensive SKILL.md file")
            return
            
        try:
            content = skill_md_path.read_text(encoding='utf-8')
            lines = [line for line in content.split('\n') if line.strip()]
            
            # Score based on length and depth
            line_count = len(lines)
            if line_count >= 400:
                length_score = 25
            elif line_count >= 300:
                length_score = 20
            elif line_count >= 200:
                length_score = 15
            elif line_count >= 100:
                length_score = 10
            else:
                length_score = 5
                
            dimension.add_score("skill_md_length", length_score, 25, 
                               f"SKILL.md has {line_count} lines")
                               
            if line_count < 300:
                dimension.add_suggestion("Expand SKILL.md with more detailed sections")
                
            # Score frontmatter quality
            frontmatter_score = self._score_frontmatter(content)
            dimension.add_score("skill_md_frontmatter", frontmatter_score, 25, 
                               "Frontmatter completeness and accuracy")
                               
            # Score section completeness
            section_score = self._score_sections(content)
            dimension.add_score("skill_md_sections", section_score, 25,
                               "Required and recommended section coverage")
                               
            # Score content depth
            depth_score = self._score_content_depth(content)
            dimension.add_score("skill_md_depth", depth_score, 25,
                               "Content depth and technical detail")
                               
        except Exception as e:
            dimension.add_score("skill_md_readable", 0, 25, f"Error reading SKILL.md: {str(e)}")
            dimension.add_suggestion("Fix SKILL.md file encoding or format issues")
            
    def _score_frontmatter(self, content: str) -> float:
        """Score SKILL.md frontmatter quality"""
        required_fields = ["Name", "Tier", "Category", "Dependencies", "Author", "Version"]
        recommended_fields = ["Last Updated", "Description"]
        
        try:
            if not content.startswith('---'):
                return 5  # Partial credit for having some structure
                
            end_marker = content.find('---', 3)
            if end_marker == -1:
                return 5
                
            frontmatter_text = content[3:end_marker].strip()
            frontmatter = yaml.safe_load(frontmatter_text)
            
            if not isinstance(frontmatter, dict):
                return 5
                
            score = 0
            
            # Required fields (15 points)
            present_required = sum(1 for field in required_fields if field in frontmatter)
            score += (present_required / len(required_fields)) * 15
            
            # Recommended fields (5 points)
            present_recommended = sum(1 for field in recommended_fields if field in frontmatter)
            score += (present_recommended / len(recommended_fields)) * 5
            
            # Quality of field values (5 points)
            quality_bonus = 0
            for field, value in frontmatter.items():
                if isinstance(value, str) and len(value.strip()) > 3:
                    quality_bonus += 0.5
                    
            score += min(quality_bonus, 5)
            
            return min(score, 25)
            
        except yaml.YAMLError:
            return 5  # Some credit for attempting frontmatter
            
    def _score_sections(self, content: str) -> float:
        """Score section completeness"""
        required_sections = ["Description", "Features", "Usage", "Examples"]
        recommended_sections = ["Architecture", "Installation", "Troubleshooting", "Contributing"]
        
        score = 0
        
        # Required sections (15 points)
        present_required = 0
        for section in required_sections:
            if re.search(rf'^#+\s*{re.escape(section)}\s*$', content, re.MULTILINE | re.IGNORECASE):
                present_required += 1
                
        score += (present_required / len(required_sections)) * 15
        
        # Recommended sections (10 points)
        present_recommended = 0
        for section in recommended_sections:
            if re.search(rf'^#+\s*{re.escape(section)}\s*$', content, re.MULTILINE | re.IGNORECASE):
                present_recommended += 1
                
        score += (present_recommended / len(recommended_sections)) * 10
        
        return score
        
    def _score_content_depth(self, content: str) -> float:
        """Score content depth and technical detail"""
        score = 0
        
        # Code examples (8 points)
        code_blocks = len(re.findall(r'```[\w]*\n.*?\n```', content, re.DOTALL))
        score += min(code_blocks * 2, 8)
        
        # Technical depth indicators (8 points)
        depth_indicators = ['API', 'algorithm', 'architecture', 'implementation', 'performance', 
                           'scalability', 'security', 'integration', 'configuration', 'parameters']
        depth_score = sum(1 for indicator in depth_indicators if indicator.lower() in content.lower())
        score += min(depth_score * 0.8, 8)
        
        # Usage examples (9 points)
        example_patterns = [r'Example:', r'Usage:', r'```bash', r'```python', r'```yaml']
        example_count = sum(len(re.findall(pattern, content, re.IGNORECASE)) for pattern in example_patterns)
        score += min(example_count * 1.5, 9)
        
        return score
        
    def _score_readme(self, dimension: QualityDimension):
        """Score README.md quality"""
        readme_path = self.skill_path / "README.md"
        
        if not readme_path.exists():
            dimension.add_score("readme_existence", 10, 25, "README.md exists (partial credit)")
            dimension.add_suggestion("Create README.md with usage instructions")
            return
            
        try:
            content = readme_path.read_text(encoding='utf-8')
            
            # Length and substance
            if len(content.strip()) >= 1000:
                length_score = 25
            elif len(content.strip()) >= 500:
                length_score = 20
            elif len(content.strip()) >= 200:
                length_score = 15
            else:
                length_score = 10
                
            dimension.add_score("readme_quality", length_score, 25,
                               f"README.md content quality ({len(content)} characters)")
                               
            if len(content.strip()) < 500:
                dimension.add_suggestion("Expand README.md with more detailed usage examples")
                
        except Exception:
            dimension.add_score("readme_readable", 5, 25, "README.md exists but has issues")
            
    def _score_references(self, dimension: QualityDimension):
        """Score reference documentation quality"""
        references_dir = self.skill_path / "references"
        
        if not references_dir.exists():
            dimension.add_score("references_existence", 0, 25, "No references directory")
            dimension.add_suggestion("Add references directory with documentation")
            return
            
        ref_files = list(references_dir.glob("*.md")) + list(references_dir.glob("*.txt"))
        
        if not ref_files:
            dimension.add_score("references_content", 5, 25, "References directory empty")
            dimension.add_suggestion("Add reference documentation files")
            return
            
        # Score based on number and quality of reference files
        score = min(len(ref_files) * 5, 20)  # Up to 20 points for multiple files
        
        # Bonus for substantial content
        total_content = 0
        for ref_file in ref_files:
            try:
                content = ref_file.read_text(encoding='utf-8')
                total_content += len(content.strip())
            except:
                continue
                
        if total_content >= 2000:
            score += 5  # Bonus for substantial reference content
            
        dimension.add_score("references_quality", score, 25, 
                           f"References: {len(ref_files)} files, {total_content} chars")
                           
    def _score_examples(self, dimension: QualityDimension):
        """Score examples and usage clarity"""
        score = 0
        
        # Look for example files in various locations
        example_locations = ["examples", "assets", "scripts"]
        example_files = []
        
        for location in example_locations:
            location_path = self.skill_path / location
            if location_path.exists():
                example_files.extend(location_path.glob("*example*"))
                example_files.extend(location_path.glob("*sample*"))
                example_files.extend(location_path.glob("*demo*"))
                
        # Score based on example availability
        if len(example_files) >= 3:
            score = 25
        elif len(example_files) >= 2:
            score = 20
        elif len(example_files) >= 1:
            score = 15
        else:
            score = 10
            dimension.add_suggestion("Add more usage examples and sample files")
            
        dimension.add_score("examples_availability", score, 25,
                           f"Found {len(example_files)} example/sample files")
                           
    def _score_code_quality(self, weight: float = 0.25):
        """Score code quality"""
        self.log_verbose("Scoring code quality...")
        
        dimension = QualityDimension("Code Quality", weight, "Quality of Python scripts and implementation")
        
        scripts_dir = self.skill_path / "scripts"
        if not scripts_dir.exists():
            dimension.add_score("scripts_existence", 0, 100, "No scripts directory")
            dimension.add_suggestion("Create scripts directory with Python files")
            dimension.calculate_final_score()
            self.report.add_dimension(dimension)
            return
            
        python_files = list(scripts_dir.glob("*.py"))
        if not python_files:
            dimension.add_score("python_scripts", 0, 100, "No Python scripts found")
            dimension.add_suggestion("Add Python scripts to scripts directory")
            dimension.calculate_final_score()
            self.report.add_dimension(dimension)
            return
            
        # Score script complexity and quality
        self._score_script_complexity(python_files, dimension)
        
        # Score error handling
        self._score_error_handling(python_files, dimension)
        
        # Score code structure
        self._score_code_structure(python_files, dimension)
        
        # Score output format support
        self._score_output_support(python_files, dimension)
        
        dimension.calculate_final_score()
        self.report.add_dimension(dimension)
        
    def _score_script_complexity(self, python_files: List[Path], dimension: QualityDimension):
        """Score script complexity and sophistication"""
        total_complexity = 0
        script_count = len(python_files)
        
        for script_path in python_files:
            try:
                content = script_path.read_text(encoding='utf-8')
                
                # Count lines of code (excluding empty lines and comments)
                lines = content.split('\n')
                loc = len([line for line in lines if line.strip() and not line.strip().startswith('#')])
                
                # Score based on LOC
                if loc >= 800:
                    complexity_score = 25
                elif loc >= 500:
                    complexity_score = 20
                elif loc >= 300:
                    complexity_score = 15
                elif loc >= 100:
                    complexity_score = 10
                else:
                    complexity_score = 5
                    
                total_complexity += complexity_score
                
            except Exception:
                continue
                
        avg_complexity = total_complexity / script_count if script_count > 0 else 0
        dimension.add_score("script_complexity", avg_complexity, 25,
                           f"Average script complexity across {script_count} scripts")
                           
        if avg_complexity < 15:
            dimension.add_suggestion("Consider expanding scripts with more functionality")
            
    def _score_error_handling(self, python_files: List[Path], dimension: QualityDimension):
        """Score error handling quality"""
        total_error_score = 0
        script_count = len(python_files)
        
        for script_path in python_files:
            try:
                content = script_path.read_text(encoding='utf-8')
                error_score = 0
                
                # Check for try/except blocks
                try_count = content.count('try:')
                error_score += min(try_count * 5, 15)  # Up to 15 points for try/except
                
                # Check for specific exception handling
                exception_types = ['Exception', 'ValueError', 'FileNotFoundError', 'KeyError', 'TypeError']
                for exc_type in exception_types:
                    if exc_type in content:
                        error_score += 2  # 2 points per specific exception type
                        
                # Check for logging or error reporting
                if any(indicator in content for indicator in ['print(', 'logging.', 'sys.stderr']):
                    error_score += 5  # 5 points for error reporting
                    
                total_error_score += min(error_score, 25)  # Cap at 25 per script
                
            except Exception:
                continue
                
        avg_error_score = total_error_score / script_count if script_count > 0 else 0
        dimension.add_score("error_handling", avg_error_score, 25,
                           f"Error handling quality across {script_count} scripts")
                           
        if avg_error_score < 15:
            dimension.add_suggestion("Improve error handling with try/except blocks and meaningful error messages")
            
    def _score_code_structure(self, python_files: List[Path], dimension: QualityDimension):
        """Score code structure and organization"""
        total_structure_score = 0
        script_count = len(python_files)
        
        for script_path in python_files:
            try:
                content = script_path.read_text(encoding='utf-8')
                structure_score = 0
                
                # Check for functions and classes
                function_count = content.count('def ')
                class_count = content.count('class ')
                
                structure_score += min(function_count * 2, 10)  # Up to 10 points for functions
                structure_score += min(class_count * 3, 9)     # Up to 9 points for classes
                
                # Check for docstrings
                docstring_patterns = ['"""', "'''", 'def.*:\n.*"""', 'class.*:\n.*"""']
                for pattern in docstring_patterns:
                    if re.search(pattern, content):
                        structure_score += 1  # 1 point per docstring indicator
                        
                # Check for if __name__ == "__main__"
                if 'if __name__ == "__main__"' in content:
                    structure_score += 3
                    
                # Check for imports organization
                if content.lstrip().startswith(('import ', 'from ')):
                    structure_score += 2  # Imports at top
                    
                total_structure_score += min(structure_score, 25)
                
            except Exception:
                continue
                
        avg_structure_score = total_structure_score / script_count if script_count > 0 else 0
        dimension.add_score("code_structure", avg_structure_score, 25,
                           f"Code structure quality across {script_count} scripts")
                           
        if avg_structure_score < 15:
            dimension.add_suggestion("Improve code structure with more functions, classes, and documentation")
            
    def _score_output_support(self, python_files: List[Path], dimension: QualityDimension):
        """Score output format support"""
        total_output_score = 0
        script_count = len(python_files)
        
        for script_path in python_files:
            try:
                content = script_path.read_text(encoding='utf-8')
                output_score = 0
                
                # Check for JSON support
                if any(indicator in content for indicator in ['json.dump', 'json.load', '--json']):
                    output_score += 12  # JSON support
                    
                # Check for formatted output
                if any(indicator in content for indicator in ['print(f"', 'print("', '.format(', 'f"']):
                    output_score += 8  # Human-readable output
                    
                # Check for argparse help
                if '--help' in content or 'add_help=' in content:
                    output_score += 5  # Help functionality
                    
                total_output_score += min(output_score, 25)
                
            except Exception:
                continue
                
        avg_output_score = total_output_score / script_count if script_count > 0 else 0
        dimension.add_score("output_support", avg_output_score, 25,
                           f"Output format support across {script_count} scripts")
                           
        if avg_output_score < 15:
            dimension.add_suggestion("Add support for both JSON and human-readable output formats")
            
    def _score_completeness(self, weight: float = 0.25):
        """Score completeness"""
        self.log_verbose("Scoring completeness...")
        
        dimension = QualityDimension("Completeness", weight, "Completeness of required components and assets")
        
        # Score directory structure
        self._score_directory_structure(dimension)
        
        # Score asset availability
        self._score_assets(dimension)
        
        # Score expected outputs
        self._score_expected_outputs(dimension)
        
        # Score test coverage
        self._score_test_coverage(dimension)
        
        dimension.calculate_final_score()
        self.report.add_dimension(dimension)
        
    def _score_directory_structure(self, dimension: QualityDimension):
        """Score directory structure completeness"""
        required_dirs = ["scripts"]
        recommended_dirs = ["assets", "references", "expected_outputs"]
        
        score = 0
        
        # Required directories (15 points)
        for dir_name in required_dirs:
            if (self.skill_path / dir_name).exists():
                score += 15 / len(required_dirs)
                
        # Recommended directories (10 points)
        present_recommended = 0
        for dir_name in recommended_dirs:
            if (self.skill_path / dir_name).exists():
                present_recommended += 1
                
        score += (present_recommended / len(recommended_dirs)) * 10
        
        dimension.add_score("directory_structure", score, 25,
                           f"Directory structure completeness")
                           
        missing_recommended = [d for d in recommended_dirs if not (self.skill_path / d).exists()]
        if missing_recommended:
            dimension.add_suggestion(f"Add recommended directories: {', '.join(missing_recommended)}")
            
    def _score_assets(self, dimension: QualityDimension):
        """Score asset availability and quality"""
        assets_dir = self.skill_path / "assets"
        
        if not assets_dir.exists():
            dimension.add_score("assets_existence", 5, 25, "Assets directory missing")
            dimension.add_suggestion("Create assets directory with sample data")
            return
            
        asset_files = [f for f in assets_dir.rglob("*") if f.is_file()]
        
        if not asset_files:
            dimension.add_score("assets_content", 10, 25, "Assets directory empty")
            dimension.add_suggestion("Add sample data files to assets directory")
            return
            
        # Score based on number and diversity of assets
        score = min(len(asset_files) * 3, 20)  # Up to 20 points for multiple assets
        
        # Bonus for diverse file types
        extensions = set(f.suffix.lower() for f in asset_files if f.suffix)
        if len(extensions) >= 3:
            score += 5  # Bonus for file type diversity
            
        dimension.add_score("assets_quality", score, 25,
                           f"Assets: {len(asset_files)} files, {len(extensions)} types")
                           
    def _score_expected_outputs(self, dimension: QualityDimension):
        """Score expected outputs availability"""
        expected_dir = self.skill_path / "expected_outputs"
        
        if not expected_dir.exists():
            dimension.add_score("expected_outputs", 10, 25, "Expected outputs directory missing")
            dimension.add_suggestion("Add expected_outputs directory with sample results")
            return
            
        output_files = [f for f in expected_dir.rglob("*") if f.is_file()]
        
        if len(output_files) >= 3:
            score = 25
        elif len(output_files) >= 2:
            score = 20
        elif len(output_files) >= 1:
            score = 15
        else:
            score = 10
            dimension.add_suggestion("Add expected output files for testing")
            
        dimension.add_score("expected_outputs", score, 25,
                           f"Expected outputs: {len(output_files)} files")
                           
    def _score_test_coverage(self, dimension: QualityDimension):
        """Score test coverage and validation"""
        # This is a simplified scoring - in a more sophisticated system,
        # this would integrate with actual test runners
        
        score = 15  # Base score for having a structure
        
        # Check for test-related files
        test_indicators = ["test", "spec", "check"]
        test_files = []
        
        for indicator in test_indicators:
            test_files.extend(self.skill_path.rglob(f"*{indicator}*"))
            
        if test_files:
            score += 10  # Bonus for test files
            
        dimension.add_score("test_coverage", score, 25,
                           f"Test coverage indicators: {len(test_files)} files")
                           
        if not test_files:
            dimension.add_suggestion("Add test files or validation scripts")
            
    def _score_usability(self, weight: float = 0.25):
        """Score usability"""
        self.log_verbose("Scoring usability...")
        
        dimension = QualityDimension("Usability", weight, "Ease of use and user experience")
        
        # Score installation simplicity
        self._score_installation(dimension)
        
        # Score usage clarity
        self._score_usage_clarity(dimension)
        
        # Score help and documentation accessibility
        self._score_help_accessibility(dimension)
        
        # Score practical examples
        self._score_practical_examples(dimension)
        
        dimension.calculate_final_score()
        self.report.add_dimension(dimension)
        
    def _score_installation(self, dimension: QualityDimension):
        """Score installation simplicity"""
        # Check for installation complexity indicators
        score = 25  # Start with full points for standard library only approach
        
        # Check for requirements.txt or setup.py (would reduce score)
        if (self.skill_path / "requirements.txt").exists():
            score -= 5  # Minor penalty for external dependencies
            dimension.add_suggestion("Consider removing external dependencies for easier installation")
            
        if (self.skill_path / "setup.py").exists():
            score -= 3  # Minor penalty for complex setup
            
        dimension.add_score("installation_simplicity", max(score, 15), 25,
                           "Installation complexity assessment")
                           
    def _score_usage_clarity(self, dimension: QualityDimension):
        """Score usage clarity"""
        score = 0
        
        # Check README for usage instructions
        readme_path = self.skill_path / "README.md"
        if readme_path.exists():
            try:
                content = readme_path.read_text(encoding='utf-8').lower()
                if 'usage' in content or 'how to' in content:
                    score += 10
                if 'example' in content:
                    score += 5
            except:
                pass
                
        # Check scripts for help text quality
        scripts_dir = self.skill_path / "scripts"
        if scripts_dir.exists():
            python_files = list(scripts_dir.glob("*.py"))
            help_quality = 0
            
            for script_path in python_files:
                try:
                    content = script_path.read_text(encoding='utf-8')
                    if 'argparse' in content and 'help=' in content:
                        help_quality += 2
                except:
                    continue
                    
            score += min(help_quality, 10)  # Up to 10 points for help text
            
        dimension.add_score("usage_clarity", score, 25, "Usage instructions and help quality")
        
        if score < 15:
            dimension.add_suggestion("Improve usage documentation and help text")
            
    def _score_help_accessibility(self, dimension: QualityDimension):
        """Score help and documentation accessibility"""
        score = 0
        
        # Check for comprehensive help in scripts
        scripts_dir = self.skill_path / "scripts"
        if scripts_dir.exists():
            python_files = list(scripts_dir.glob("*.py"))
            
            for script_path in python_files:
                try:
                    content = script_path.read_text(encoding='utf-8')
                    
                    # Check for detailed help text
                    if 'epilog=' in content or 'description=' in content:
                        score += 5  # Detailed help
                        
                    # Check for examples in help
                    if 'examples:' in content.lower() or 'example:' in content.lower():
                        score += 3  # Examples in help
                        
                except:
                    continue
                    
        # Check for documentation files
        doc_files = list(self.skill_path.glob("*.md"))
        if len(doc_files) >= 2:
            score += 5  # Multiple documentation files
            
        dimension.add_score("help_accessibility", min(score, 25), 25,
                           "Help and documentation accessibility")
                           
        if score < 15:
            dimension.add_suggestion("Add more comprehensive help text and documentation")
            
    def _score_practical_examples(self, dimension: QualityDimension):
        """Score practical examples quality"""
        score = 0
        
        # Look for example files
        example_patterns = ["*example*", "*sample*", "*demo*", "*tutorial*"]
        example_files = []
        
        for pattern in example_patterns:
            example_files.extend(self.skill_path.rglob(pattern))
            
        # Score based on example availability and quality
        if len(example_files) >= 5:
            score = 25
        elif len(example_files) >= 3:
            score = 20
        elif len(example_files) >= 2:
            score = 15
        elif len(example_files) >= 1:
            score = 10
        else:
            score = 5
            dimension.add_suggestion("Add more practical examples and sample files")
            
        dimension.add_score("practical_examples", score, 25,
                           f"Practical examples: {len(example_files)} files")

    def _score_security(self, weight: float = 0.20):
        """Score security quality"""
        self.log_verbose("Scoring security quality...")
        
        dimension = QualityDimension("Security", weight, "Security practices and vulnerability prevention")
        
        # Find Python scripts
        python_files = list(self.skill_path.rglob("*.py"))
        
        # Filter out test files and __pycache__
        python_files = [f for f in python_files 
                       if "__pycache__" not in str(f) and "test_" not in f.name]
        
        if not python_files:
            dimension.add_score("scripts_existence", 25, 25, 
                               "No scripts directory - no script security concerns")
            dimension.calculate_final_score()
            self.report.add_dimension(dimension)
            return
        
        # Use SecurityScorer module
        try:
            scorer = SecurityScorer(python_files, verbose=self.verbose)
            result = scorer.get_overall_score()
            
            # Extract scores from SecurityScorer result
            sensitive_data_score = result.get("sensitive_data_exposure", {}).get("score", 0)
            file_ops_score = result.get("safe_file_operations", {}).get("score", 0)
            command_injection_score = result.get("command_injection_prevention", {}).get("score", 0)
            input_validation_score = result.get("input_validation", {}).get("score", 0)
            
            dimension.add_score("sensitive_data_exposure", sensitive_data_score, 25,
                               "Detection and prevention of hardcoded credentials")
            dimension.add_score("safe_file_operations", file_ops_score, 25,
                               "Prevention of path traversal vulnerabilities")
            dimension.add_score("command_injection_prevention", command_injection_score, 25,
                               "Prevention of command injection vulnerabilities")
            dimension.add_score("input_validation", input_validation_score, 25,
                               "Quality of input validation and error handling")
            
            # Add suggestions from SecurityScorer
            for issue in result.get("issues", []):
                dimension.add_suggestion(issue)
                
        except Exception as e:
            self.log_verbose(f"Security scoring failed: {str(e)}")
            dimension.add_score("security_error", 0, 100, f"Security scoring failed: {str(e)}")
            dimension.add_suggestion("Fix security scoring module integration")
        
        dimension.calculate_final_score()
        self.report.add_dimension(dimension)


class QualityReportFormatter:
    """Formats quality reports for output"""
    
    @staticmethod
    def format_json(report: QualityReport) -> str:
        """Format report as JSON"""
        return json.dumps({
            "skill_path": report.skill_path,
            "timestamp": report.timestamp,
            "overall_score": round(report.overall_score, 1),
            "letter_grade": report.letter_grade,
            "tier_recommendation": report.tier_recommendation,
            "summary_stats": report.summary_stats,
            "dimensions": {
                name: {
                    "name": dim.name,
                    "weight": dim.weight,
                    "score": round(dim.score, 1),
                    "description": dim.description,
                    "details": dim.details,
                    "suggestions": dim.suggestions
                }
                for name, dim in report.dimensions.items()
            },
            "improvement_roadmap": report.improvement_roadmap
        }, indent=2)
        
    @staticmethod
    def format_human_readable(report: QualityReport, detailed: bool = False) -> str:
        """Format report as human-readable text"""
        lines = []
        lines.append("=" * 70)
        lines.append("SKILL QUALITY ASSESSMENT REPORT")
        lines.append("=" * 70)
        lines.append(f"Skill: {report.skill_path}")
        lines.append(f"Timestamp: {report.timestamp}")
        lines.append(f"Overall Score: {report.overall_score:.1f}/100 ({report.letter_grade})")
        lines.append(f"Recommended Tier: {report.tier_recommendation}")
        lines.append("")
        
        # Dimension scores
        lines.append("QUALITY DIMENSIONS:")
        for name, dimension in report.dimensions.items():
            lines.append(f"  {name}: {dimension.score:.1f}/100 ({dimension.weight * 100:.0f}% weight)")
            if detailed and dimension.details:
                for component, details in dimension.details.items():
                    lines.append(f"    • {component}: {details['score']:.1f}/{details['max_score']} - {details['details']}")
            lines.append("")
            
        # Summary statistics
        if report.summary_stats:
            lines.append("SUMMARY STATISTICS:")
            lines.append(f"  Highest Dimension: {report.summary_stats['highest_dimension']}")
            lines.append(f"  Lowest Dimension: {report.summary_stats['lowest_dimension']}")
            lines.append(f"  Dimensions Above 70%: {report.summary_stats['dimensions_above_70']}")
            lines.append(f"  Dimensions Below 50%: {report.summary_stats['dimensions_below_50']}")
            lines.append("")
            
        # Improvement roadmap
        if report.improvement_roadmap:
            lines.append("IMPROVEMENT ROADMAP:")
            for i, item in enumerate(report.improvement_roadmap[:5], 1):
                priority_symbol = "🔴" if item["priority"] == "HIGH" else "🟡" if item["priority"] == "MEDIUM" else "🟢"
                lines.append(f"  {i}. {priority_symbol} [{item['dimension']}] {item['suggestion']}")
            lines.append("")
            
        return "\n".join(lines)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Score skill quality across multiple dimensions",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python quality_scorer.py engineering/my-skill
  python quality_scorer.py engineering/my-skill --detailed --json
  python quality_scorer.py engineering/my-skill --minimum-score 75
  python quality_scorer.py engineering/my-skill --include-security

Quality Dimensions (default: 4 dimensions × 25%):
  Documentation - SKILL.md quality, README, references, examples
  Code Quality   - Script complexity, error handling, structure, output
  Completeness   - Directory structure, assets, expected outputs, tests
  Usability      - Installation simplicity, usage clarity, help accessibility

With --include-security (5 dimensions × 20%):
  Security       - Sensitive data exposure, command injection, input validation

Letter Grades: A+ (95+), A (90+), A- (85+), B+ (80+), B (75+), B- (70+), C+ (65+), C (60+), C- (55+), D (50+), F (<50)
        """
    )
    
    parser.add_argument("skill_path",
                       help="Path to the skill directory to assess")
    parser.add_argument("--detailed",
                       action="store_true",
                       help="Show detailed component scores")
    parser.add_argument("--minimum-score",
                       type=float,
                       default=0,
                       help="Minimum acceptable score (exit with error if below)")
    parser.add_argument("--json",
                       action="store_true",
                       help="Output results in JSON format")
    parser.add_argument("--verbose",
                       action="store_true",
                       help="Enable verbose logging")
    parser.add_argument("--include-security",
                       action="store_true",
                       help="Include Security dimension (switches to 5 dimensions × 20%% each)")
                       
    args = parser.parse_args()
    
    try:
        # Create scorer and assess quality
        scorer = QualityScorer(args.skill_path, args.detailed, args.verbose, args.include_security)
        report = scorer.assess_quality()
        
        # Format and output report
        if args.json:
            print(QualityReportFormatter.format_json(report))
        else:
            print(QualityReportFormatter.format_human_readable(report, args.detailed))
            
        # Check minimum score requirement
        if report.overall_score < args.minimum_score:
            print(f"\nERROR: Quality score {report.overall_score:.1f} is below minimum {args.minimum_score}", file=sys.stderr)
            sys.exit(1)
            
        # Exit with different codes based on grade
        if report.letter_grade in ["A+", "A", "A-"]:
            sys.exit(0)  # Excellent
        elif report.letter_grade in ["B+", "B", "B-"]:
            sys.exit(0)  # Good
        elif report.letter_grade in ["C+", "C", "C-"]:
            sys.exit(0)  # Acceptable
        elif report.letter_grade == "D":
            sys.exit(2)  # Needs improvement
        else:  # F
            sys.exit(1)  # Poor quality
            
    except KeyboardInterrupt:
        print("\nQuality assessment interrupted by user", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"Quality assessment failed: {str(e)}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()