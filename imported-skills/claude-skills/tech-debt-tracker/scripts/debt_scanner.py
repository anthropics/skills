#!/usr/bin/env python3
"""
Tech Debt Scanner

Scans a codebase directory for tech debt signals using AST parsing (Python) and 
regex patterns (any language). Detects various forms of technical debt and generates
both JSON inventory and human-readable reports.

Usage:
    python debt_scanner.py /path/to/codebase
    python debt_scanner.py /path/to/codebase --config config.json
    python debt_scanner.py /path/to/codebase --output report.json --format both
"""

import ast
import json
import argparse
import os
import re
import sys
from collections import defaultdict, Counter
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional, Set, Tuple


class DebtScanner:
    """Main scanner class for detecting technical debt in codebases."""
    
    def __init__(self, config: Optional[Dict[str, Any]] = None):
        self.config = self._load_default_config()
        if config:
            self.config.update(config)
        
        self.debt_items = []
        self.stats = defaultdict(int)
        self.file_stats = {}
        
        # Compile regex patterns for performance
        self._compile_patterns()
    
    def _load_default_config(self) -> Dict[str, Any]:
        """Load default configuration for debt detection."""
        return {
            "max_function_length": 50,
            "max_complexity": 10,
            "max_nesting_depth": 4,
            "max_file_size_lines": 500,
            "min_duplicate_lines": 3,
            "ignore_patterns": [
                "*.pyc", "__pycache__", ".git", ".svn", "node_modules",
                "build", "dist", "*.min.js", "*.map"
            ],
            "file_extensions": {
                "python": [".py"],
                "javascript": [".js", ".jsx", ".ts", ".tsx"],
                "java": [".java"],
                "csharp": [".cs"],
                "cpp": [".cpp", ".cc", ".cxx", ".c", ".h", ".hpp"],
                "ruby": [".rb"],
                "php": [".php"],
                "go": [".go"],
                "rust": [".rs"],
                "kotlin": [".kt"]
            },
            "comment_patterns": {
                "todo": r"(?i)(TODO|FIXME|HACK|XXX|BUG)[\s:]*(.+)",
                "commented_code": r"^\s*#.*[=(){}\[\];].*",
                "magic_numbers": r"\b\d{2,}\b",
                "long_strings": r'["\'](.{100,})["\']'
            },
            "severity_weights": {
                "critical": 10,
                "high": 7,
                "medium": 5,
                "low": 2,
                "info": 1
            }
        }
    
    def _compile_patterns(self):
        """Compile regex patterns for better performance."""
        self.comment_regexes = {}
        for name, pattern in self.config["comment_patterns"].items():
            self.comment_regexes[name] = re.compile(pattern)
        
        # Common code smells patterns
        self.smell_patterns = {
            "empty_catch": re.compile(r"except[^:]*:\s*pass\s*$", re.MULTILINE),
            "print_debug": re.compile(r"print\s*\([^)]*debug[^)]*\)", re.IGNORECASE),
            "hardcoded_paths": re.compile(r'["\'][/\\][^"\']*[/\\][^"\']*["\']'),
            "sql_injection_risk": re.compile(r'["\'].*%s.*["\'].*execute', re.IGNORECASE),
        }
    
    def scan_directory(self, directory: str) -> Dict[str, Any]:
        """
        Scan a directory for tech debt.
        
        Args:
            directory: Path to the directory to scan
            
        Returns:
            Dictionary containing debt inventory and statistics
        """
        directory_path = Path(directory)
        if not directory_path.exists():
            raise ValueError(f"Directory does not exist: {directory}")
        
        print(f"Scanning directory: {directory}")
        print("=" * 50)
        
        # Reset state
        self.debt_items = []
        self.stats = defaultdict(int)
        self.file_stats = {}
        
        # Walk through directory
        for root, dirs, files in os.walk(directory):
            # Filter out ignored directories
            dirs[:] = [d for d in dirs if not self._should_ignore(d)]
            
            for file in files:
                if self._should_ignore(file):
                    continue
                
                file_path = os.path.join(root, file)
                relative_path = os.path.relpath(file_path, directory)
                
                try:
                    self._scan_file(file_path, relative_path)
                except Exception as e:
                    print(f"Error scanning {relative_path}: {e}")
                    self.stats["scan_errors"] += 1
        
        # Post-process results
        self._detect_duplicates(directory)
        self._calculate_priorities()
        
        return self._generate_report(directory)
    
    def _should_ignore(self, name: str) -> bool:
        """Check if file/directory should be ignored."""
        for pattern in self.config["ignore_patterns"]:
            if "*" in pattern:
                if re.match(pattern.replace("*", ".*"), name):
                    return True
            elif pattern in name:
                return True
        return False
    
    def _scan_file(self, file_path: str, relative_path: str):
        """Scan a single file for tech debt."""
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                lines = content.splitlines()
        except Exception as e:
            print(f"Cannot read {relative_path}: {e}")
            return
        
        file_ext = Path(file_path).suffix.lower()
        file_info = {
            "path": relative_path,
            "lines": len(lines),
            "size_kb": os.path.getsize(file_path) / 1024,
            "language": self._detect_language(file_ext),
            "debt_count": 0
        }
        
        self.stats["files_scanned"] += 1
        self.stats["total_lines"] += len(lines)
        
        # File size debt
        if len(lines) > self.config["max_file_size_lines"]:
            self._add_debt_item(
                "large_file",
                f"File is too large: {len(lines)} lines",
                relative_path,
                "medium",
                {"lines": len(lines), "recommended_max": self.config["max_file_size_lines"]}
            )
            file_info["debt_count"] += 1
        
        # Language-specific analysis
        if file_info["language"] == "python" and file_ext == ".py":
            self._scan_python_file(relative_path, content, lines)
        else:
            self._scan_generic_file(relative_path, content, lines, file_info["language"])
        
        # Common patterns for all languages
        self._scan_common_patterns(relative_path, content, lines)
        
        self.file_stats[relative_path] = file_info
    
    def _detect_language(self, file_ext: str) -> str:
        """Detect programming language from file extension."""
        for lang, extensions in self.config["file_extensions"].items():
            if file_ext in extensions:
                return lang
        return "unknown"
    
    def _scan_python_file(self, file_path: str, content: str, lines: List[str]):
        """Scan Python files using AST parsing."""
        try:
            tree = ast.parse(content)
            analyzer = PythonASTAnalyzer(self.config)
            debt_items = analyzer.analyze(tree, file_path, lines)
            self.debt_items.extend(debt_items)
            self.stats["python_files"] += 1
        except SyntaxError as e:
            self._add_debt_item(
                "syntax_error",
                f"Python syntax error: {e}",
                file_path,
                "high",
                {"line": e.lineno, "error": str(e)}
            )
    
    def _scan_generic_file(self, file_path: str, content: str, lines: List[str], language: str):
        """Scan non-Python files using pattern matching."""
        # Detect long lines
        for i, line in enumerate(lines):
            if len(line) > 120:
                self._add_debt_item(
                    "long_line",
                    f"Line too long: {len(line)} characters",
                    file_path,
                    "low",
                    {"line_number": i + 1, "length": len(line)}
                )
        
        # Detect deep nesting (approximate)
        for i, line in enumerate(lines):
            indent_level = len(line) - len(line.lstrip())
            if language in ["python"]:
                indent_level = indent_level // 4  # Python uses 4-space indents
            elif language in ["javascript", "java", "csharp", "cpp"]:
                # Count braces for brace-based languages
                brace_level = content[:content.find('\n'.join(lines[:i+1]))].count('{') - content[:content.find('\n'.join(lines[:i+1]))].count('}')
                if brace_level > self.config["max_nesting_depth"]:
                    self._add_debt_item(
                        "deep_nesting",
                        f"Deep nesting detected: {brace_level} levels",
                        file_path,
                        "medium",
                        {"line_number": i + 1, "nesting_level": brace_level}
                    )
    
    def _scan_common_patterns(self, file_path: str, content: str, lines: List[str]):
        """Scan for common patterns across all file types."""
        # TODO/FIXME comments
        for i, line in enumerate(lines):
            for pattern_name, regex in self.comment_regexes.items():
                match = regex.search(line)
                if match:
                    if pattern_name == "todo":
                        self._add_debt_item(
                            "todo_comment",
                            f"TODO/FIXME comment: {match.group(0)}",
                            file_path,
                            "low",
                            {"line_number": i + 1, "comment": match.group(0).strip()}
                        )
        
        # Code smells
        for smell_name, pattern in self.smell_patterns.items():
            matches = pattern.finditer(content)
            for match in matches:
                line_num = content[:match.start()].count('\n') + 1
                self._add_debt_item(
                    smell_name,
                    f"Code smell detected: {smell_name}",
                    file_path,
                    "medium",
                    {"line_number": line_num, "pattern": match.group(0)[:100]}
                )
    
    def _detect_duplicates(self, directory: str):
        """Detect duplicate code blocks across files."""
        # Simple duplicate detection based on exact line matches
        line_hashes = defaultdict(list)
        
        for file_path, file_info in self.file_stats.items():
            try:
                full_path = os.path.join(directory, file_path)
                with open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
                    lines = f.readlines()
                
                for i in range(len(lines) - self.config["min_duplicate_lines"] + 1):
                    block = ''.join(lines[i:i + self.config["min_duplicate_lines"]])
                    block_hash = hash(block.strip())
                    if len(block.strip()) > 50:  # Only consider substantial blocks
                        line_hashes[block_hash].append((file_path, i + 1, block))
            except Exception:
                continue
        
        # Report duplicates
        for block_hash, occurrences in line_hashes.items():
            if len(occurrences) > 1:
                for file_path, line_num, block in occurrences:
                    self._add_debt_item(
                        "duplicate_code",
                        f"Duplicate code block found in {len(occurrences)} files",
                        file_path,
                        "medium",
                        {
                            "line_number": line_num,
                            "duplicate_count": len(occurrences),
                            "other_files": [f[0] for f in occurrences if f[0] != file_path]
                        }
                    )
    
    def _calculate_priorities(self):
        """Calculate priority scores for debt items."""
        severity_weights = self.config["severity_weights"]
        
        for item in self.debt_items:
            base_score = severity_weights.get(item["severity"], 1)
            
            # Adjust based on debt type
            type_multipliers = {
                "syntax_error": 2.0,
                "security_risk": 1.8,
                "large_function": 1.5,
                "high_complexity": 1.4,
                "duplicate_code": 1.3,
                "todo_comment": 0.5
            }
            
            multiplier = type_multipliers.get(item["type"], 1.0)
            item["priority_score"] = int(base_score * multiplier)
            
            # Set priority category
            if item["priority_score"] >= 15:
                item["priority"] = "critical"
            elif item["priority_score"] >= 10:
                item["priority"] = "high"
            elif item["priority_score"] >= 5:
                item["priority"] = "medium"
            else:
                item["priority"] = "low"
    
    def _add_debt_item(self, debt_type: str, description: str, file_path: str, 
                      severity: str, metadata: Dict[str, Any]):
        """Add a debt item to the inventory."""
        item = {
            "id": f"DEBT-{len(self.debt_items) + 1:04d}",
            "type": debt_type,
            "description": description,
            "file_path": file_path,
            "severity": severity,
            "metadata": metadata,
            "detected_date": datetime.now().isoformat(),
            "status": "identified"
        }
        
        self.debt_items.append(item)
        self.stats[f"debt_{debt_type}"] += 1
        self.stats["total_debt_items"] += 1
        
        if file_path in self.file_stats:
            self.file_stats[file_path]["debt_count"] += 1
    
    def _generate_report(self, directory: str) -> Dict[str, Any]:
        """Generate the final debt report."""
        # Sort debt items by priority score
        self.debt_items.sort(key=lambda x: x.get("priority_score", 0), reverse=True)
        
        # Calculate summary statistics
        priority_counts = Counter(item["priority"] for item in self.debt_items)
        type_counts = Counter(item["type"] for item in self.debt_items)
        
        # Calculate health score (0-100, higher is better)
        total_files = self.stats.get("files_scanned", 1)
        debt_density = len(self.debt_items) / total_files
        health_score = max(0, 100 - (debt_density * 10))
        
        report = {
            "scan_metadata": {
                "directory": directory,
                "scan_date": datetime.now().isoformat(),
                "scanner_version": "1.0.0",
                "config": self.config
            },
            "summary": {
                "total_files_scanned": self.stats.get("files_scanned", 0),
                "total_lines_scanned": self.stats.get("total_lines", 0),
                "total_debt_items": len(self.debt_items),
                "health_score": round(health_score, 1),
                "debt_density": round(debt_density, 2),
                "priority_breakdown": dict(priority_counts),
                "type_breakdown": dict(type_counts)
            },
            "debt_items": self.debt_items,
            "file_statistics": self.file_stats,
            "recommendations": self._generate_recommendations()
        }
        
        return report
    
    def _generate_recommendations(self) -> List[str]:
        """Generate actionable recommendations based on findings."""
        recommendations = []
        
        # Priority-based recommendations
        high_priority_count = len([item for item in self.debt_items 
                                  if item.get("priority") in ["critical", "high"]])
        
        if high_priority_count > 10:
            recommendations.append(
                f"Address {high_priority_count} high-priority debt items immediately - "
                "they pose significant risk to code quality and maintainability."
            )
        
        # Type-specific recommendations
        type_counts = Counter(item["type"] for item in self.debt_items)
        
        if type_counts.get("large_function", 0) > 5:
            recommendations.append(
                "Consider refactoring large functions into smaller, more focused units. "
                "This will improve readability and testability."
            )
        
        if type_counts.get("duplicate_code", 0) > 3:
            recommendations.append(
                "Extract duplicate code into reusable functions or modules. "
                "This reduces maintenance burden and potential for inconsistent changes."
            )
        
        if type_counts.get("todo_comment", 0) > 20:
            recommendations.append(
                "Review and address TODO/FIXME comments. Consider creating proper "
                "tickets for substantial work items."
            )
        
        # General recommendations
        total_files = self.stats.get("files_scanned", 1)
        if len(self.debt_items) / total_files > 2:
            recommendations.append(
                "High debt density detected. Consider establishing coding standards "
                "and regular code review processes to prevent debt accumulation."
            )
        
        if not recommendations:
            recommendations.append("Code quality looks good! Continue current practices.")
        
        return recommendations


class PythonASTAnalyzer(ast.NodeVisitor):
    """AST analyzer for Python-specific debt detection."""
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.debt_items = []
        self.current_file = ""
        self.lines = []
        self.function_stack = []
    
    def analyze(self, tree: ast.AST, file_path: str, lines: List[str]) -> List[Dict[str, Any]]:
        """Analyze Python AST for tech debt."""
        self.debt_items = []
        self.current_file = file_path
        self.lines = lines
        self.function_stack = []
        
        self.visit(tree)
        return self.debt_items
    
    def visit_FunctionDef(self, node: ast.FunctionDef):
        """Analyze function definitions."""
        self.function_stack.append(node.name)
        
        # Calculate function length
        func_length = node.end_lineno - node.lineno + 1
        if func_length > self.config["max_function_length"]:
            self._add_debt(
                "large_function",
                f"Function '{node.name}' is too long: {func_length} lines",
                node.lineno,
                "medium",
                {"function_name": node.name, "length": func_length}
            )
        
        # Check for missing docstring
        if not ast.get_docstring(node):
            self._add_debt(
                "missing_docstring",
                f"Function '{node.name}' missing docstring",
                node.lineno,
                "low",
                {"function_name": node.name}
            )
        
        # Calculate cyclomatic complexity
        complexity = self._calculate_complexity(node)
        if complexity > self.config["max_complexity"]:
            self._add_debt(
                "high_complexity",
                f"Function '{node.name}' has high complexity: {complexity}",
                node.lineno,
                "high",
                {"function_name": node.name, "complexity": complexity}
            )
        
        # Check parameter count
        param_count = len(node.args.args)
        if param_count > 5:
            self._add_debt(
                "too_many_parameters",
                f"Function '{node.name}' has too many parameters: {param_count}",
                node.lineno,
                "medium",
                {"function_name": node.name, "parameter_count": param_count}
            )
        
        self.generic_visit(node)
        self.function_stack.pop()
    
    def visit_ClassDef(self, node: ast.ClassDef):
        """Analyze class definitions."""
        # Check for missing docstring
        if not ast.get_docstring(node):
            self._add_debt(
                "missing_docstring",
                f"Class '{node.name}' missing docstring",
                node.lineno,
                "low",
                {"class_name": node.name}
            )
        
        # Check for too many methods
        methods = [n for n in node.body if isinstance(n, ast.FunctionDef)]
        if len(methods) > 20:
            self._add_debt(
                "large_class",
                f"Class '{node.name}' has too many methods: {len(methods)}",
                node.lineno,
                "medium",
                {"class_name": node.name, "method_count": len(methods)}
            )
        
        self.generic_visit(node)
    
    def _calculate_complexity(self, node: ast.FunctionDef) -> int:
        """Calculate cyclomatic complexity of a function."""
        complexity = 1  # Base complexity
        
        for child in ast.walk(node):
            if isinstance(child, (ast.If, ast.While, ast.For, ast.AsyncFor)):
                complexity += 1
            elif isinstance(child, ast.ExceptHandler):
                complexity += 1
            elif isinstance(child, ast.BoolOp):
                complexity += len(child.values) - 1
        
        return complexity
    
    def _add_debt(self, debt_type: str, description: str, line_number: int,
                 severity: str, metadata: Dict[str, Any]):
        """Add a debt item to the collection."""
        item = {
            "id": f"DEBT-{len(self.debt_items) + 1:04d}",
            "type": debt_type,
            "description": description,
            "file_path": self.current_file,
            "line_number": line_number,
            "severity": severity,
            "metadata": metadata,
            "detected_date": datetime.now().isoformat(),
            "status": "identified"
        }
        self.debt_items.append(item)


def format_human_readable_report(report: Dict[str, Any]) -> str:
    """Format the report in human-readable format."""
    output = []
    
    # Header
    output.append("=" * 60)
    output.append("TECHNICAL DEBT SCAN REPORT")
    output.append("=" * 60)
    output.append(f"Directory: {report['scan_metadata']['directory']}")
    output.append(f"Scan Date: {report['scan_metadata']['scan_date']}")
    output.append(f"Scanner Version: {report['scan_metadata']['scanner_version']}")
    output.append("")
    
    # Summary
    summary = report["summary"]
    output.append("SUMMARY")
    output.append("-" * 30)
    output.append(f"Files Scanned: {summary['total_files_scanned']}")
    output.append(f"Lines Scanned: {summary['total_lines_scanned']:,}")
    output.append(f"Total Debt Items: {summary['total_debt_items']}")
    output.append(f"Health Score: {summary['health_score']}/100")
    output.append(f"Debt Density: {summary['debt_density']} items/file")
    output.append("")
    
    # Priority breakdown
    output.append("PRIORITY BREAKDOWN")
    output.append("-" * 30)
    for priority, count in summary["priority_breakdown"].items():
        output.append(f"{priority.capitalize()}: {count}")
    output.append("")
    
    # Top debt items
    output.append("TOP DEBT ITEMS")
    output.append("-" * 30)
    top_items = report["debt_items"][:10]
    for i, item in enumerate(top_items, 1):
        output.append(f"{i}. [{item['priority'].upper()}] {item['description']}")
        output.append(f"   File: {item['file_path']}")
        if 'line_number' in item:
            output.append(f"   Line: {item['line_number']}")
        output.append("")
    
    # Recommendations
    output.append("RECOMMENDATIONS")
    output.append("-" * 30)
    for i, rec in enumerate(report["recommendations"], 1):
        output.append(f"{i}. {rec}")
        output.append("")
    
    return "\n".join(output)


def main():
    """Main entry point for the debt scanner."""
    parser = argparse.ArgumentParser(description="Scan codebase for technical debt")
    parser.add_argument("directory", help="Directory to scan")
    parser.add_argument("--config", help="Configuration file (JSON)")
    parser.add_argument("--output", help="Output file path")
    parser.add_argument("--format", choices=["json", "text", "both"], 
                       default="both", help="Output format")
    
    args = parser.parse_args()
    
    # Load configuration
    config = None
    if args.config:
        try:
            with open(args.config, 'r') as f:
                config = json.load(f)
        except Exception as e:
            print(f"Error loading config: {e}")
            sys.exit(1)
    
    # Run scan
    scanner = DebtScanner(config)
    try:
        report = scanner.scan_directory(args.directory)
    except Exception as e:
        print(f"Scan failed: {e}")
        sys.exit(1)
    
    # Output results
    if args.format in ["json", "both"]:
        json_output = json.dumps(report, indent=2, default=str)
        if args.output:
            output_path = args.output if args.output.endswith('.json') else f"{args.output}.json"
            with open(output_path, 'w') as f:
                f.write(json_output)
            print(f"JSON report written to: {output_path}")
        else:
            print("\nJSON REPORT:")
            print("=" * 50)
            print(json_output)
    
    if args.format in ["text", "both"]:
        text_output = format_human_readable_report(report)
        if args.output:
            output_path = args.output if args.output.endswith('.txt') else f"{args.output}.txt"
            with open(output_path, 'w') as f:
                f.write(text_output)
            print(f"Text report written to: {output_path}")
        else:
            print("\nTEXT REPORT:")
            print("=" * 50)
            print(text_output)


if __name__ == "__main__":
    main()