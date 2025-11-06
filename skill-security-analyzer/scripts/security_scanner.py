#!/usr/bin/env python3
"""
Enhanced Security Scanner for Claude Code Skills v2.0
Addresses bypass techniques with advanced pattern detection and semantic analysis
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Set
from datetime import datetime
import yaml

class EnhancedSecurityScanner:
    """Enhanced security scanner with advanced detection capabilities"""

    # Severity levels
    CRITICAL = "CRITICAL"
    HIGH = "HIGH"
    MEDIUM = "MEDIUM"
    LOW = "LOW"

    def __init__(self, skill_path: str, verbose: bool = False):
        self.skill_path = Path(skill_path)
        self.verbose = verbose
        self.findings = []
        self.all_imports = set()  # Track all imports across files

    def scan(self) -> Dict:
        """Run comprehensive security scan"""
        print(f"[*] Scanning skill at: {self.skill_path}", file=sys.stderr)

        if not self.skill_path.exists():
            raise ValueError(f"Skill path does not exist: {self.skill_path}")

        # Phase 1: Structural analysis
        self._check_skill_structure()
        
        # Phase 2: Content scanning
        self._scan_yaml_frontmatter_enhanced()
        self._scan_all_files()  # Changed to scan ALL files
        
        # Phase 3: Cross-file analysis
        self._analyze_imports()
        self._check_network_operations()
        self._check_file_operations()
        
        # Phase 4: Advanced patterns
        self._cross_file_analysis()

        # Generate report
        report = self._generate_report()
        return report

    def _check_skill_structure(self):
        """Verify skill has expected structure"""
        skill_md = self.skill_path / "SKILL.md"

        if not skill_md.exists():
            self.findings.append({
                "severity": self.CRITICAL,
                "category": "Structure",
                "title": "Missing SKILL.md",
                "description": "Required SKILL.md file not found",
                "location": str(self.skill_path),
                "impact": "Skill cannot function without SKILL.md"
            })

    def _scan_yaml_frontmatter_enhanced(self):
        """Enhanced YAML frontmatter analysis with actual parsing"""
        skill_md = self.skill_path / "SKILL.md"

        if not skill_md.exists():
            return

        content = skill_md.read_text(encoding='utf-8')

        # Extract frontmatter
        frontmatter_match = re.match(r'^---\n(.*?)\n---', content, re.DOTALL)

        if not frontmatter_match:
            self.findings.append({
                "severity": self.HIGH,
                "category": "YAML",
                "title": "Missing YAML frontmatter",
                "description": "SKILL.md missing required YAML frontmatter",
                "location": "SKILL.md:1",
                "impact": "Skill metadata cannot be parsed"
            })
            return

        frontmatter_text = frontmatter_match.group(1)

        # First: Regex patterns for quick detection
        dangerous_patterns = [
            (r'!\s*<', "YAML tag directive (potential code execution)"),
            (r'__proto__', "Prototype pollution attempt"),
            (r'!!python', "Python object deserialization"),
            (r'eval\(', "Eval function call in YAML"),
            (r'exec\(', "Exec function call in YAML"),
        ]

        for pattern, desc in dangerous_patterns:
            if re.search(pattern, frontmatter_text, re.IGNORECASE):
                self.findings.append({
                    "severity": self.CRITICAL,
                    "category": "YAML Injection",
                    "title": f"Dangerous YAML pattern: {desc}",
                    "description": f"YAML frontmatter contains '{pattern}' which could execute code",
                    "location": "SKILL.md frontmatter",
                    "impact": "Arbitrary code execution during skill parsing"
                })

        # Second: Actually parse YAML safely
        try:
            parsed = yaml.safe_load(frontmatter_text)
            
            # Check for suspicious keys recursively
            if isinstance(parsed, dict):
                self._check_yaml_keys_recursive(parsed, "SKILL.md frontmatter")
                
        except yaml.constructor.ConstructorError as e:
            self.findings.append({
                "severity": self.CRITICAL,
                "category": "YAML Injection",
                "title": "YAML attempts to construct Python objects",
                "description": f"Error: {str(e)}",
                "location": "SKILL.md frontmatter",
                "impact": "Arbitrary code execution via YAML deserialization"
            })
        except yaml.YAMLError as e:
            self.findings.append({
                "severity": self.HIGH,
                "category": "YAML",
                "title": "Malformed YAML frontmatter",
                "description": f"Parse error: {str(e)}",
                "location": "SKILL.md frontmatter",
                "impact": "Skill may fail to load or contains obfuscated content"
            })

    def _check_yaml_keys_recursive(self, data, location: str):
        """Recursively check YAML structure for dangerous keys"""
        suspicious_keys = ['__proto__', 'constructor', 'prototype', 
                          'exec', 'eval', 'system', '__class__', '__init__']
        
        if isinstance(data, dict):
            for key in data.keys():
                if key in suspicious_keys:
                    self.findings.append({
                        "severity": self.CRITICAL,
                        "category": "YAML Injection",
                        "title": f"Suspicious YAML key: {key}",
                        "location": location,
                        "impact": "Potential prototype pollution or code execution"
                    })
                
                # Recurse into values
                self._check_yaml_keys_recursive(data[key], location)
        
        elif isinstance(data, list):
            for item in data:
                self._check_yaml_keys_recursive(item, location)

    def _is_text_file(self, path: Path) -> bool:
        """Heuristic to detect if file is text"""
        try:
            # Exclude obvious binaries by extension
            binary_exts = {'.pyc', '.so', '.dll', '.exe', '.bin', '.dat', 
                          '.png', '.jpg', '.jpeg', '.gif', '.ico', '.zip', '.tar', '.gz'}
            if path.suffix.lower() in binary_exts:
                return False
            
            # Read first 8KB
            with open(path, 'rb') as f:
                chunk = f.read(8192)
            
            # Check for null bytes (binary indicator)
            if b'\x00' in chunk:
                return False
            
            # Try to decode as UTF-8
            try:
                chunk.decode('utf-8')
                return True
            except UnicodeDecodeError:
                return False
        except Exception:
            return False

    def _scan_all_files(self):
        """Scan ALL text files, not just known extensions"""
        # Scan scripts directory with ALL files
        scripts_dir = self.skill_path / "scripts"
        if scripts_dir.exists():
            for file_path in scripts_dir.rglob("*"):
                if file_path.is_file() and self._is_text_file(file_path):
                    self._analyze_script(file_path)
        
        # Scan references for hidden code
        refs_dir = self.skill_path / "references"
        if refs_dir.exists():
            for file_path in refs_dir.rglob("*"):
                if file_path.is_file() and self._is_text_file(file_path):
                    self._scan_reference_file(file_path)
        
        # Scan SKILL.md for embedded code
        self._scan_markdown_for_code()
        
        # Scan assets for polyglots
        self._scan_assets_enhanced()

    def _analyze_script(self, script_path: Path):
        """Analyze individual script for vulnerabilities"""
        try:
            content = script_path.read_text(encoding='utf-8')
        except Exception as e:
            self.findings.append({
                "severity": self.MEDIUM,
                "category": "File Access",
                "title": f"Cannot read file: {script_path.name}",
                "description": f"Error: {e}",
                "location": str(script_path),
                "impact": "Unable to analyze for security issues"
            })
            return

        relative_path = script_path.relative_to(self.skill_path)

        # Original checks
        self._check_command_injection(content, relative_path)
        self._check_data_exfiltration(content, relative_path)
        self._check_credential_theft(content, relative_path)
        self._check_obfuscation(content, relative_path)
        self._check_hardcoded_secrets(content, relative_path)
        
        # NEW: Enhanced checks
        self._check_indirect_execution(content, relative_path)
        self._check_advanced_obfuscation(content, relative_path)
        self._check_shell_injection(content, relative_path)
        self._check_time_bombs(content, relative_path)
        self._check_environment_manipulation(content, relative_path)

    def _check_indirect_execution(self, content: str, file_path: Path):
        """Detect indirect code execution via getattr, __import__, etc."""
        
        patterns = [
            # getattr patterns
            (r'getattr\s*\([^,]+,\s*[\'"][^\'"]*(?:system|exec|eval|compile|open)[^\'"]*[\'"]', 
             self.CRITICAL, "getattr accessing dangerous function names"),
            
            # String concatenation to build function names
            (r'getattr\s*\([^,]+,\s*[^)]*\+[^)]*\)',
             self.CRITICAL, "Dynamic function name via string concatenation"),
            
            # __builtins__ manipulation
            (r'__builtins__\s*\[|getattr\s*\(__builtins__',
             self.CRITICAL, "__builtins__ manipulation"),
            
            # Class traversal (sandbox escape)
            (r'__class__\.__base__\.__subclasses__',
             self.CRITICAL, "Class hierarchy traversal (sandbox escape pattern)"),
            
            # Dictionary-based execution
            (r'\{[^}]*[\'"](?:exec|eval|system)[\'"][^}]*\}\[',
             self.CRITICAL, "Dictionary-based function call obfuscation"),
            
            # Lambda with dangerous functions
            (r'lambda[^:]*:\s*(?:exec|eval|__import__|getattr)',
             self.HIGH, "Lambda wrapping dangerous operations"),
            
            # importlib with concatenation
            (r'importlib\.import_module\s*\([^)]*\+[^)]*\)',
             self.CRITICAL, "Dynamic module import with string manipulation"),
        ]
        
        for pattern, severity, desc in patterns:
            for match in re.finditer(pattern, content, re.IGNORECASE):
                line_num = content[:match.start()].count('\n') + 1
                self.findings.append({
                    "severity": severity,
                    "category": "Obfuscated Execution",
                    "title": desc,
                    "location": f"{file_path}:{line_num}",
                    "evidence": self._get_code_context(content, match.start()),
                    "impact": "Code execution via obfuscation/indirection"
                })

    def _check_advanced_obfuscation(self, content: str, file_path: Path):
        """Detect multiple encoding/obfuscation schemes"""
        
        patterns = [
            # Compression
            (r'zlib\.decompress|gzip\.decompress|bz2\.decompress',
             self.HIGH, "Compressed payload detected"),
            
            # URL encoding
            (r'urllib\.parse\.unquote|quote_plus\(',
             self.MEDIUM, "URL-encoded content"),
            
            # ROT13/Caesar cipher
            (r'codecs\.decode\([^,]+,\s*[\'"]rot',
             self.HIGH, "ROT cipher encoding"),
            
            # XOR encoding
            (r'chr\s*\(\s*ord\([^)]+\)\s*\^',
             self.HIGH, "XOR encoding pattern"),
            
            # Hex to bytes
            (r'bytes\.fromhex\(|bytearray\.fromhex\(',
             self.MEDIUM, "Hex-to-bytes conversion"),
            
            # AST manipulation
            (r'ast\.parse\([^)]+\).*?ast\.\w+\s*=',
             self.HIGH, "AST manipulation (code rewriting)"),
            
            # Deserialization
            (r'marshal\.loads|pickle\.loads|yaml\.(?:load|unsafe_load)\(',
             self.CRITICAL, "Unsafe deserialization"),
        ]
        
        for pattern, severity, desc in patterns:
            for match in re.finditer(pattern, content, re.IGNORECASE):
                line_num = content[:match.start()].count('\n') + 1
                
                # Check if exec/eval nearby (within 5 lines)
                context = self._get_code_context(content, match.start(), 0, 5)
                if re.search(r'exec|eval', context):
                    severity = self.CRITICAL
                
                self.findings.append({
                    "severity": severity,
                    "category": "Code Obfuscation",
                    "title": desc,
                    "location": f"{file_path}:{line_num}",
                    "evidence": self._get_code_context(content, match.start()),
                    "impact": "Obfuscated code hiding potential payload"
                })

    def _check_shell_injection(self, content: str, file_path: Path):
        """Detect shell injection even without shell=True"""
        
        shell_patterns = [
            r'subprocess\.\w+\s*\(\s*\[\s*[\'"](?:/bin/)?(?:bash|sh|zsh|ksh)[\'"]',
            r'subprocess\.\w+\s*\(\s*\[\s*[\'"](?:python|python3)[\'"],\s*[\'"]-c[\'"]',
            r'subprocess\.\w+\s*\(\s*\[\s*[\'"]perl[\'"],\s*[\'"]-e[\'"]',
            r'subprocess\.\w+\s*\(\s*\[\s*[\'"]ruby[\'"],\s*[\'"]-e[\'"]',
            r'subprocess\.\w+\s*\(\s*\[\s*[\'"]awk[\'"].*system',
            r'subprocess\.\w+\s*\(\s*\[\s*[\'"]jq[\'"].*@sh',
            r'subprocess\.\w+\s*\(\s*\[\s*[\'"]sed[\'"].*e[\'"]',
        ]
        
        for pattern in shell_patterns:
            for match in re.finditer(pattern, content, re.IGNORECASE):
                line_num = content[:match.start()].count('\n') + 1
                
                self.findings.append({
                    "severity": self.CRITICAL,
                    "category": "Shell Injection",
                    "title": "Shell/interpreter invocation with injection risk",
                    "location": f"{file_path}:{line_num}",
                    "evidence": self._get_code_context(content, match.start()),
                    "impact": "Shell spawned; command injection if user input reaches arguments"
                })

    def _check_time_bombs(self, content: str, file_path: Path):
        """Detect time-based conditional execution"""
        
        time_patterns = [
            r'datetime\..*\.(?:day|month|year|hour|minute)',
            r'time\.time\(\)\s*[><=]',
            r'if\s+.*datetime\.',
            r'time\.sleep\([^)]*\).*(?:os\.system|subprocess|exec|eval)',
        ]
        
        for pattern in time_patterns:
            for match in re.finditer(pattern, content):
                # Get surrounding context
                context = self._get_code_context(content, match.start(), 2, 10)
                
                # Check if dangerous operations appear nearby
                if re.search(r'os\.system|subprocess|exec|eval|requests\.(post|get)|urllib|socket', 
                            context, re.IGNORECASE):
                    line_num = content[:match.start()].count('\n') + 1
                    
                    self.findings.append({
                        "severity": self.HIGH,
                        "category": "Time Bomb",
                        "title": "Time-based conditional near dangerous operation",
                        "location": f"{file_path}:{line_num}",
                        "evidence": context,
                        "impact": "Code may activate at specific time (time bomb pattern)"
                    })
                    break  # Only report once per time pattern

    def _check_environment_manipulation(self, content: str, file_path: Path):
        """Detect dangerous environment variable manipulation"""
        
        dangerous_env_patterns = [
            (r'os\.environ\[[\'"](?:LD_PRELOAD|LD_LIBRARY_PATH)[\'"]',
             "LD_PRELOAD/LD_LIBRARY_PATH manipulation (library hijacking)"),
            (r'os\.environ\[[\'"]PATH[\'"]',
             "PATH manipulation (command hijacking)"),
            (r'os\.environ\[[\'"]PYTHONPATH[\'"]',
             "PYTHONPATH manipulation (module hijacking)"),
            (r'os\.putenv\(',
             "Direct environment modification via putenv"),
        ]
        
        for pattern, desc in dangerous_env_patterns:
            for match in re.finditer(pattern, content, re.IGNORECASE):
                line_num = content[:match.start()].count('\n') + 1
                
                self.findings.append({
                    "severity": self.HIGH,
                    "category": "Environment Manipulation",
                    "title": desc,
                    "location": f"{file_path}:{line_num}",
                    "evidence": self._get_code_context(content, match.start()),
                    "impact": "Can hijack library/command loading mechanisms"
                })

    def _analyze_imports(self):
        """Analyze all imports for typosquatting"""
        
        # Common legitimate packages
        legit_packages = {
            'requests', 'urllib', 'beautifulsoup4', 'bs4', 'lxml',
            'numpy', 'pandas', 'matplotlib', 'scipy', 'sklearn',
            'flask', 'django', 'fastapi', 'sqlalchemy',
            'pytest', 'unittest', 'mock', 'click', 'pyyaml',
        }
        
        # Known typosquats
        typosquat_map = {
            'request': 'requests',
            'urlib': 'urllib',
            'numppy': 'numpy',
            'beatifulsoup': 'beautifulsoup4',
            'scikit-learn': 'sklearn',
        }
        
        for imp in self.all_imports:
            base_module = imp.split('.')[0]
            
            # Check known typosquats
            if base_module in typosquat_map:
                self.findings.append({
                    "severity": self.CRITICAL,
                    "category": "Supply Chain",
                    "title": f"Known typosquat detected: {base_module}",
                    "description": f"Did you mean '{typosquat_map[base_module]}'?",
                    "location": "Imports",
                    "impact": "Malicious package impersonating legitimate library"
                })

    def _scan_reference_file(self, file_path: Path):
        """Scan reference documentation for hidden code"""
        try:
            content = file_path.read_text(encoding='utf-8', errors='ignore')
            
            # Check for code in HTML comments
            html_comment_code = re.search(r'<!--.*?(?:exec|eval|os\.system|import os).*?-->', 
                                         content, re.DOTALL | re.IGNORECASE)
            if html_comment_code:
                self.findings.append({
                    "severity": self.HIGH,
                    "category": "Hidden Code",
                    "title": "Executable code in HTML comment",
                    "location": str(file_path.relative_to(self.skill_path)),
                    "evidence": html_comment_code.group()[:200],
                    "impact": "Code hidden in documentation comments"
                })
            
            # Check for code in markdown code blocks
            if file_path.suffix == '.md':
                code_blocks = re.findall(r'```(?:python|bash|sh)\n(.*?)```', content, re.DOTALL)
                for block in code_blocks:
                    if re.search(r'exec\(|eval\(|os\.system\(|subprocess\..*shell\s*=\s*True', block):
                        self.findings.append({
                            "severity": self.MEDIUM,
                            "category": "Documentation",
                            "title": "Dangerous code in documentation example",
                            "location": str(file_path.relative_to(self.skill_path)),
                            "impact": "Verify this is example code, not executable"
                        })
        except Exception:
            pass

    def _scan_markdown_for_code(self):
        """Scan SKILL.md for hidden executable code"""
        skill_md = self.skill_path / "SKILL.md"
        if not skill_md.exists():
            return
        
        content = skill_md.read_text(encoding='utf-8')
        
        # Skip frontmatter
        content = re.sub(r'^---\n.*?\n---\n', '', content, flags=re.DOTALL)
        
        # Check for suspicious code blocks
        code_blocks = re.findall(r'```.*?\n(.*?)```', content, re.DOTALL)
        for block in code_blocks:
            if re.search(r'exec\(|eval\(|__import__|getattr.*system', block):
                self.findings.append({
                    "severity": self.HIGH,
                    "category": "Documentation",
                    "title": "Dangerous code pattern in SKILL.md",
                    "location": "SKILL.md",
                    "impact": "Verify this is documentation, not executable instruction"
                })

    def _scan_assets_enhanced(self):
        """Enhanced asset scanning for polyglots and hidden executables"""
        assets_dir = self.skill_path / "assets"
        
        if not assets_dir.exists():
            return
        
        for asset_file in assets_dir.rglob("*"):
            if not asset_file.is_file():
                continue
            
            # Check executable headers
            try:
                with open(asset_file, 'rb') as f:
                    header = f.read(4)
                
                # Executable signatures
                if header in [b'\x7fELF', b'MZ\x90\x00', b'\xca\xfe\xba\xbe']:
                    self.findings.append({
                        "severity": self.CRITICAL,
                        "category": "Assets",
                        "title": f"Executable file: {asset_file.name}",
                        "location": str(asset_file.relative_to(self.skill_path)),
                        "impact": "Binary executable in assets directory"
                    })
            except Exception:
                pass

    def _cross_file_analysis(self):
        """Analyze patterns across multiple files"""
        # Track if user input exists in one file and dangerous ops in another
        files_with_input = []
        files_with_sinks = []
        
        for script_file in self.skill_path.rglob("*.py"):
            try:
                content = script_file.read_text(encoding='utf-8')
                
                # Check for input sources
                if re.search(r'input\(|sys\.argv|os\.environ|request\.(args|form|json)', content):
                    files_with_input.append(script_file.name)
                
                # Check for dangerous sinks
                if re.search(r'os\.system|subprocess\.|exec\(|eval\(', content):
                    files_with_sinks.append(script_file.name)
            except:
                pass
        
        if files_with_input and files_with_sinks:
            self.findings.append({
                "severity": self.HIGH,
                "category": "Data Flow",
                "title": "User input and dangerous operations in skill",
                "description": f"Input in: {files_with_input}, Sinks in: {files_with_sinks}",
                "location": "Multiple files",
                "impact": "Verify input validation before dangerous operations"
            })

    # [Include original helper methods: _check_command_injection, _check_data_exfiltration, 
    #  _check_credential_theft, _check_obfuscation, _check_hardcoded_secrets,
    #  _check_network_operations, _check_file_operations, _get_code_context, _generate_report]
    
    # Placeholder - keep originals from the base scanner
    def _check_command_injection(self, content: str, file_path: Path):
        # Original implementation
        pass
    
    def _check_data_exfiltration(self, content: str, file_path: Path):
        # Original implementation  
        pass
    
    def _check_credential_theft(self, content: str, file_path: Path):
        # Original implementation
        pass
    
    def _check_obfuscation(self, content: str, file_path: Path):
        # Original implementation
        pass
    
    def _check_hardcoded_secrets(self, content: str, file_path: Path):
        # Original implementation
        pass
    
    def _check_network_operations(self):
        # Original implementation
        pass
    
    def _check_file_operations(self):
        # Original implementation
        pass
    
    def _get_code_context(self, content: str, position: int, lines_before=1, lines_after=1) -> str:
        """Get code context around a position"""
        line_start = position
        for _ in range(lines_before):
            prev_newline = content.rfind('\n', 0, line_start)
            if prev_newline != -1:
                line_start = prev_newline

        line_end = position
        for _ in range(lines_after):
            next_newline = content.find('\n', line_end + 1)
            if next_newline != -1:
                line_end = next_newline
            else:
                break

        context = content[line_start:line_end].strip()
        return context[:200] + '...' if len(context) > 200 else context

    def _generate_report(self) -> Dict:
        """Generate security report"""
        severity_counts = {
            self.CRITICAL: 0,
            self.HIGH: 0,
            self.MEDIUM: 0,
            self.LOW: 0
        }

        for finding in self.findings:
            severity_counts[finding['severity']] += 1

        # Determine overall risk
        if severity_counts[self.CRITICAL] > 0:
            overall_risk = self.CRITICAL
            recommendation = "REJECT"
        elif severity_counts[self.HIGH] > 3:
            overall_risk = self.HIGH
            recommendation = "REVIEW"
        elif severity_counts[self.HIGH] > 0:
            overall_risk = "MEDIUM-HIGH"
            recommendation = "REVIEW"
        elif severity_counts[self.MEDIUM] > 5:
            overall_risk = self.MEDIUM
            recommendation = "REVIEW"
        else:
            overall_risk = "LOW"
            recommendation = "APPROVE"

        report = {
            "skill": self.skill_path.name,
            "location": str(self.skill_path),
            "timestamp": datetime.utcnow().isoformat() + 'Z',
            "scanner_version": "2.0-enhanced",
            "summary": {
                "overall_risk": overall_risk,
                "total_findings": len(self.findings),
                "critical": severity_counts[self.CRITICAL],
                "high": severity_counts[self.HIGH],
                "medium": severity_counts[self.MEDIUM],
                "low": severity_counts[self.LOW],
                "recommendation": recommendation
            },
            "findings": self.findings
        }

        return report


def main():
    parser = argparse.ArgumentParser(
        description='Enhanced security scanner for Claude Code skills v2.0'
    )
    parser.add_argument('skill_path', help='Path to skill directory')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    parser.add_argument('--output', '-o', help='Output JSON file')
    parser.add_argument('--recursive', '-r', action='store_true', help='Scan all skills in directory')

    args = parser.parse_args()

    if args.recursive:
        skill_paths = [d for d in Path(args.skill_path).iterdir() if d.is_dir()]
    else:
        skill_paths = [Path(args.skill_path)]

    all_reports = []

    for skill_path in skill_paths:
        try:
            scanner = EnhancedSecurityScanner(skill_path, verbose=args.verbose)
            report = scanner.scan()
            all_reports.append(report)

            print(f"\n{'='*60}", file=sys.stderr)
            print(f"Skill: {report['skill']}", file=sys.stderr)
            print(f"Overall Risk: {report['summary']['overall_risk']}", file=sys.stderr)
            print(f"Recommendation: {report['summary']['recommendation']}", file=sys.stderr)
            print(f"Findings: {report['summary']['total_findings']}", file=sys.stderr)
            print(f"{'='*60}", file=sys.stderr)

        except Exception as e:
            print(f"Error scanning {skill_path}: {e}", file=sys.stderr)
            continue

    output_data = {"scans": all_reports} if args.recursive else (all_reports[0] if all_reports else {})

    if args.output:
        with open(args.output, 'w') as f:
            json.dump(output_data, f, indent=2)
        print(f"\nReport written to: {args.output}", file=sys.stderr)
    else:
        print(json.dumps(output_data, indent=2))


if __name__ == '__main__':
    main()
