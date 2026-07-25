#!/usr/bin/env python3
"""
License Checker - Dependency license compliance and conflict analysis tool.

This script analyzes dependency licenses from package metadata, classifies them
into risk categories, detects license conflicts, and generates compliance
reports with actionable recommendations for legal risk management.

Author: Claude Skills Engineering Team
License: MIT
"""

import json
import os
import sys
import argparse
from typing import Dict, List, Set, Any, Optional, Tuple
from pathlib import Path
from dataclasses import dataclass, asdict
from datetime import datetime
import re
from enum import Enum

class LicenseType(Enum):
    """License classification types."""
    PERMISSIVE = "permissive"
    COPYLEFT_STRONG = "copyleft_strong"
    COPYLEFT_WEAK = "copyleft_weak"
    PROPRIETARY = "proprietary"
    DUAL = "dual"
    UNKNOWN = "unknown"

class RiskLevel(Enum):
    """Risk assessment levels."""
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    CRITICAL = "critical"

@dataclass
class LicenseInfo:
    """Represents license information for a dependency."""
    name: str
    spdx_id: Optional[str]
    license_type: LicenseType
    risk_level: RiskLevel
    description: str
    restrictions: List[str]
    obligations: List[str]
    compatibility: Dict[str, bool]

@dataclass
class DependencyLicense:
    """Represents a dependency with its license information."""
    name: str
    version: str
    ecosystem: str
    direct: bool
    license_declared: Optional[str]
    license_detected: Optional[LicenseInfo]
    license_files: List[str]
    confidence: float

@dataclass
class LicenseConflict:
    """Represents a license compatibility conflict."""
    dependency1: str
    license1: str
    dependency2: str
    license2: str
    conflict_type: str
    severity: RiskLevel
    description: str
    resolution_options: List[str]

class LicenseChecker:
    """Main license checking and compliance analysis class."""
    
    def __init__(self):
        self.license_database = self._build_license_database()
        self.compatibility_matrix = self._build_compatibility_matrix()
        self.license_patterns = self._build_license_patterns()
    
    def _build_license_database(self) -> Dict[str, LicenseInfo]:
        """Build comprehensive license database with risk classifications."""
        return {
            # Permissive Licenses (Low Risk)
            'MIT': LicenseInfo(
                name='MIT License',
                spdx_id='MIT',
                license_type=LicenseType.PERMISSIVE,
                risk_level=RiskLevel.LOW,
                description='Very permissive license with minimal restrictions',
                restrictions=['Include copyright notice', 'Include license text'],
                obligations=['Attribution'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': False
                }
            ),
            
            'Apache-2.0': LicenseInfo(
                name='Apache License 2.0',
                spdx_id='Apache-2.0',
                license_type=LicenseType.PERMISSIVE,
                risk_level=RiskLevel.LOW,
                description='Permissive license with patent protection',
                restrictions=['Include copyright notice', 'Include license text', 
                             'State changes', 'Include NOTICE file'],
                obligations=['Attribution', 'Patent grant'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': True
                }
            ),
            
            'BSD-3-Clause': LicenseInfo(
                name='BSD 3-Clause License',
                spdx_id='BSD-3-Clause',
                license_type=LicenseType.PERMISSIVE,
                risk_level=RiskLevel.LOW,
                description='Permissive license with non-endorsement clause',
                restrictions=['Include copyright notice', 'Include license text',
                             'No endorsement using author names'],
                obligations=['Attribution'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': False
                }
            ),
            
            'BSD-2-Clause': LicenseInfo(
                name='BSD 2-Clause License',
                spdx_id='BSD-2-Clause',
                license_type=LicenseType.PERMISSIVE,
                risk_level=RiskLevel.LOW,
                description='Very permissive license similar to MIT',
                restrictions=['Include copyright notice', 'Include license text'],
                obligations=['Attribution'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': False
                }
            ),
            
            'ISC': LicenseInfo(
                name='ISC License',
                spdx_id='ISC',
                license_type=LicenseType.PERMISSIVE,
                risk_level=RiskLevel.LOW,
                description='Functionally equivalent to MIT license',
                restrictions=['Include copyright notice'],
                obligations=['Attribution'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': False
                }
            ),
            
            # Weak Copyleft Licenses (Medium Risk)
            'MPL-2.0': LicenseInfo(
                name='Mozilla Public License 2.0',
                spdx_id='MPL-2.0',
                license_type=LicenseType.COPYLEFT_WEAK,
                risk_level=RiskLevel.MEDIUM,
                description='File-level copyleft license',
                restrictions=['Disclose source of modified files', 'Include copyright notice',
                             'Include license text', 'State changes'],
                obligations=['Source disclosure (modified files only)'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': True
                }
            ),
            
            'LGPL-2.1': LicenseInfo(
                name='GNU Lesser General Public License 2.1',
                spdx_id='LGPL-2.1',
                license_type=LicenseType.COPYLEFT_WEAK,
                risk_level=RiskLevel.MEDIUM,
                description='Library-level copyleft license',
                restrictions=['Disclose source of library modifications', 'Include copyright notice',
                             'Include license text', 'Allow relinking'],
                obligations=['Source disclosure (library modifications)', 'Dynamic linking preferred'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': False
                }
            ),
            
            'LGPL-3.0': LicenseInfo(
                name='GNU Lesser General Public License 3.0',
                spdx_id='LGPL-3.0',
                license_type=LicenseType.COPYLEFT_WEAK,
                risk_level=RiskLevel.MEDIUM,
                description='Library-level copyleft with patent provisions',
                restrictions=['Disclose source of library modifications', 'Include copyright notice',
                             'Include license text', 'Allow relinking', 'Anti-tivoization'],
                obligations=['Source disclosure (library modifications)', 'Patent grant'],
                compatibility={
                    'commercial': True, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': True
                }
            ),
            
            # Strong Copyleft Licenses (High Risk)
            'GPL-2.0': LicenseInfo(
                name='GNU General Public License 2.0',
                spdx_id='GPL-2.0',
                license_type=LicenseType.COPYLEFT_STRONG,
                risk_level=RiskLevel.HIGH,
                description='Strong copyleft requiring full source disclosure',
                restrictions=['Disclose entire source code', 'Include copyright notice',
                             'Include license text', 'Use same license'],
                obligations=['Full source disclosure', 'License compatibility'],
                compatibility={
                    'commercial': False, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': False
                }
            ),
            
            'GPL-3.0': LicenseInfo(
                name='GNU General Public License 3.0',
                spdx_id='GPL-3.0',
                license_type=LicenseType.COPYLEFT_STRONG,
                risk_level=RiskLevel.HIGH,
                description='Strong copyleft with patent and hardware provisions',
                restrictions=['Disclose entire source code', 'Include copyright notice',
                             'Include license text', 'Use same license', 'Anti-tivoization'],
                obligations=['Full source disclosure', 'Patent grant', 'License compatibility'],
                compatibility={
                    'commercial': False, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': True
                }
            ),
            
            'AGPL-3.0': LicenseInfo(
                name='GNU Affero General Public License 3.0',
                spdx_id='AGPL-3.0',
                license_type=LicenseType.COPYLEFT_STRONG,
                risk_level=RiskLevel.CRITICAL,
                description='Network copyleft extending GPL to SaaS',
                restrictions=['Disclose entire source code', 'Include copyright notice',
                             'Include license text', 'Use same license', 'Network use triggers copyleft'],
                obligations=['Full source disclosure', 'Network service source disclosure'],
                compatibility={
                    'commercial': False, 'modification': True, 'distribution': True,
                    'private_use': True, 'patent_grant': True
                }
            ),
            
            # Proprietary/Commercial Licenses (High Risk)
            'PROPRIETARY': LicenseInfo(
                name='Proprietary License',
                spdx_id=None,
                license_type=LicenseType.PROPRIETARY,
                risk_level=RiskLevel.HIGH,
                description='Commercial or custom proprietary license',
                restrictions=['Varies by license', 'Often no redistribution',
                             'May require commercial license'],
                obligations=['License agreement compliance', 'Payment obligations'],
                compatibility={
                    'commercial': False, 'modification': False, 'distribution': False,
                    'private_use': True, 'patent_grant': False
                }
            ),
            
            # Unknown/Unlicensed (Critical Risk)
            'UNKNOWN': LicenseInfo(
                name='Unknown License',
                spdx_id=None,
                license_type=LicenseType.UNKNOWN,
                risk_level=RiskLevel.CRITICAL,
                description='No license detected or ambiguous licensing',
                restrictions=['Unknown', 'Assume no rights granted'],
                obligations=['Investigate and clarify licensing'],
                compatibility={
                    'commercial': False, 'modification': False, 'distribution': False,
                    'private_use': False, 'patent_grant': False
                }
            )
        }
    
    def _build_compatibility_matrix(self) -> Dict[str, Dict[str, bool]]:
        """Build license compatibility matrix."""
        return {
            'MIT': {
                'MIT': True, 'Apache-2.0': True, 'BSD-3-Clause': True, 'BSD-2-Clause': True,
                'ISC': True, 'MPL-2.0': True, 'LGPL-2.1': True, 'LGPL-3.0': True,
                'GPL-2.0': False, 'GPL-3.0': False, 'AGPL-3.0': False, 'PROPRIETARY': False
            },
            'Apache-2.0': {
                'MIT': True, 'Apache-2.0': True, 'BSD-3-Clause': True, 'BSD-2-Clause': True,
                'ISC': True, 'MPL-2.0': True, 'LGPL-2.1': False, 'LGPL-3.0': True,
                'GPL-2.0': False, 'GPL-3.0': True, 'AGPL-3.0': True, 'PROPRIETARY': False
            },
            'GPL-2.0': {
                'MIT': True, 'Apache-2.0': False, 'BSD-3-Clause': True, 'BSD-2-Clause': True,
                'ISC': True, 'MPL-2.0': False, 'LGPL-2.1': True, 'LGPL-3.0': False,
                'GPL-2.0': True, 'GPL-3.0': False, 'AGPL-3.0': False, 'PROPRIETARY': False
            },
            'GPL-3.0': {
                'MIT': True, 'Apache-2.0': True, 'BSD-3-Clause': True, 'BSD-2-Clause': True,
                'ISC': True, 'MPL-2.0': True, 'LGPL-2.1': False, 'LGPL-3.0': True,
                'GPL-2.0': False, 'GPL-3.0': True, 'AGPL-3.0': True, 'PROPRIETARY': False
            },
            'AGPL-3.0': {
                'MIT': True, 'Apache-2.0': True, 'BSD-3-Clause': True, 'BSD-2-Clause': True,
                'ISC': True, 'MPL-2.0': True, 'LGPL-2.1': False, 'LGPL-3.0': True,
                'GPL-2.0': False, 'GPL-3.0': True, 'AGPL-3.0': True, 'PROPRIETARY': False
            }
        }
    
    def _build_license_patterns(self) -> Dict[str, List[str]]:
        """Build license detection patterns for text analysis."""
        return {
            'MIT': [
                r'MIT License',
                r'Permission is hereby granted, free of charge',
                r'THE SOFTWARE IS PROVIDED "AS IS"'
            ],
            'Apache-2.0': [
                r'Apache License, Version 2\.0',
                r'Licensed under the Apache License',
                r'http://www\.apache\.org/licenses/LICENSE-2\.0'
            ],
            'GPL-2.0': [
                r'GNU GENERAL PUBLIC LICENSE\s+Version 2',
                r'This program is free software.*GPL.*version 2',
                r'http://www\.gnu\.org/licenses/gpl-2\.0'
            ],
            'GPL-3.0': [
                r'GNU GENERAL PUBLIC LICENSE\s+Version 3',
                r'This program is free software.*GPL.*version 3',
                r'http://www\.gnu\.org/licenses/gpl-3\.0'
            ],
            'BSD-3-Clause': [
                r'BSD 3-Clause License',
                r'Redistributions of source code must retain',
                r'Neither the name.*may be used to endorse'
            ],
            'BSD-2-Clause': [
                r'BSD 2-Clause License',
                r'Redistributions of source code must retain.*Redistributions in binary form'
            ]
        }
    
    def analyze_project(self, project_path: str, dependency_inventory: Optional[str] = None) -> Dict[str, Any]:
        """Analyze license compliance for a project."""
        project_path = Path(project_path)
        
        analysis_results = {
            'timestamp': datetime.now().isoformat(),
            'project_path': str(project_path),
            'project_license': self._detect_project_license(project_path),
            'dependencies': [],
            'license_summary': {},
            'conflicts': [],
            'compliance_score': 0.0,
            'risk_assessment': {},
            'recommendations': []
        }
        
        # Load dependencies from inventory or scan project
        if dependency_inventory:
            dependencies = self._load_dependency_inventory(dependency_inventory)
        else:
            dependencies = self._scan_project_dependencies(project_path)
        
        # Analyze each dependency's license
        for dep in dependencies:
            license_info = self._analyze_dependency_license(dep, project_path)
            analysis_results['dependencies'].append(license_info)
        
        # Generate license summary
        analysis_results['license_summary'] = self._generate_license_summary(
            analysis_results['dependencies']
        )
        
        # Detect conflicts
        analysis_results['conflicts'] = self._detect_license_conflicts(
            analysis_results['project_license'],
            analysis_results['dependencies']
        )
        
        # Calculate compliance score
        analysis_results['compliance_score'] = self._calculate_compliance_score(
            analysis_results['dependencies'],
            analysis_results['conflicts']
        )
        
        # Generate risk assessment
        analysis_results['risk_assessment'] = self._generate_risk_assessment(
            analysis_results['dependencies'],
            analysis_results['conflicts']
        )
        
        # Generate recommendations
        analysis_results['recommendations'] = self._generate_compliance_recommendations(
            analysis_results
        )
        
        return analysis_results
    
    def _detect_project_license(self, project_path: Path) -> Optional[str]:
        """Detect the main project license."""
        license_files = ['LICENSE', 'LICENSE.txt', 'LICENSE.md', 'COPYING', 'COPYING.txt']
        
        for license_file in license_files:
            license_path = project_path / license_file
            if license_path.exists():
                try:
                    with open(license_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                    
                    # Analyze license content
                    detected_license = self._detect_license_from_text(content)
                    if detected_license:
                        return detected_license
                except Exception as e:
                    print(f"Error reading license file {license_path}: {e}")
        
        return None
    
    def _detect_license_from_text(self, text: str) -> Optional[str]:
        """Detect license type from text content."""
        text_upper = text.upper()
        
        for license_id, patterns in self.license_patterns.items():
            for pattern in patterns:
                if re.search(pattern, text, re.IGNORECASE):
                    return license_id
        
        # Common license text patterns
        if 'MIT' in text_upper and 'PERMISSION IS HEREBY GRANTED' in text_upper:
            return 'MIT'
        elif 'APACHE LICENSE' in text_upper and 'VERSION 2.0' in text_upper:
            return 'Apache-2.0'
        elif 'GPL' in text_upper and 'VERSION 2' in text_upper:
            return 'GPL-2.0'
        elif 'GPL' in text_upper and 'VERSION 3' in text_upper:
            return 'GPL-3.0'
        
        return None
    
    def _load_dependency_inventory(self, inventory_path: str) -> List[Dict[str, Any]]:
        """Load dependencies from JSON inventory file."""
        try:
            with open(inventory_path, 'r') as f:
                data = json.load(f)
            
            if 'dependencies' in data:
                return data['dependencies']
            else:
                return data if isinstance(data, list) else []
        except Exception as e:
            print(f"Error loading dependency inventory: {e}")
            return []
    
    def _scan_project_dependencies(self, project_path: Path) -> List[Dict[str, Any]]:
        """Basic dependency scanning - in practice, would integrate with dep_scanner.py."""
        dependencies = []
        
        # Simple package.json parsing as example
        package_json = project_path / 'package.json'
        if package_json.exists():
            try:
                with open(package_json, 'r') as f:
                    data = json.load(f)
                
                for dep_type in ['dependencies', 'devDependencies']:
                    if dep_type in data:
                        for name, version in data[dep_type].items():
                            dependencies.append({
                                'name': name,
                                'version': version,
                                'ecosystem': 'npm',
                                'direct': True
                            })
            except Exception as e:
                print(f"Error parsing package.json: {e}")
        
        return dependencies
    
    def _analyze_dependency_license(self, dependency: Dict[str, Any], project_path: Path) -> DependencyLicense:
        """Analyze license information for a single dependency."""
        dep_license = DependencyLicense(
            name=dependency['name'],
            version=dependency.get('version', ''),
            ecosystem=dependency.get('ecosystem', ''),
            direct=dependency.get('direct', False),
            license_declared=dependency.get('license'),
            license_detected=None,
            license_files=[],
            confidence=0.0
        )
        
        # Try to detect license from various sources
        declared_license = dependency.get('license')
        if declared_license:
            license_info = self._resolve_license_info(declared_license)
            if license_info:
                dep_license.license_detected = license_info
                dep_license.confidence = 0.9
        
        # For unknown licenses, try to find license files in node_modules (example)
        if not dep_license.license_detected and dep_license.ecosystem == 'npm':
            node_modules_path = project_path / 'node_modules' / dep_license.name
            if node_modules_path.exists():
                license_info = self._scan_package_directory(node_modules_path)
                if license_info:
                    dep_license.license_detected = license_info
                    dep_license.confidence = 0.7
        
        # Default to unknown if no license detected
        if not dep_license.license_detected:
            dep_license.license_detected = self.license_database['UNKNOWN']
            dep_license.confidence = 0.0
        
        return dep_license
    
    def _resolve_license_info(self, license_string: str) -> Optional[LicenseInfo]:
        """Resolve license string to LicenseInfo object."""
        if not license_string:
            return None
        
        license_string = license_string.strip()
        
        # Direct SPDX ID match
        if license_string in self.license_database:
            return self.license_database[license_string]
        
        # Common variations and mappings
        license_mappings = {
            'mit': 'MIT',
            'apache': 'Apache-2.0',
            'apache-2.0': 'Apache-2.0',
            'apache 2.0': 'Apache-2.0',
            'bsd': 'BSD-3-Clause',
            'bsd-3-clause': 'BSD-3-Clause',
            'bsd-2-clause': 'BSD-2-Clause',
            'gpl-2.0': 'GPL-2.0',
            'gpl-3.0': 'GPL-3.0',
            'lgpl-2.1': 'LGPL-2.1',
            'lgpl-3.0': 'LGPL-3.0',
            'mpl-2.0': 'MPL-2.0',
            'isc': 'ISC',
            'unlicense': 'MIT',  # Treat as permissive
            'public domain': 'MIT',  # Treat as permissive
            'proprietary': 'PROPRIETARY',
            'commercial': 'PROPRIETARY'
        }
        
        license_lower = license_string.lower()
        for pattern, mapped_license in license_mappings.items():
            if pattern in license_lower:
                return self.license_database.get(mapped_license)
        
        return None
    
    def _scan_package_directory(self, package_path: Path) -> Optional[LicenseInfo]:
        """Scan package directory for license information."""
        license_files = ['LICENSE', 'LICENSE.txt', 'LICENSE.md', 'COPYING', 'README.md', 'package.json']
        
        for license_file in license_files:
            file_path = package_path / license_file
            if file_path.exists():
                try:
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    
                    # Try to detect license from content
                    if license_file == 'package.json':
                        # Parse JSON for license field
                        try:
                            data = json.loads(content)
                            license_field = data.get('license')
                            if license_field:
                                return self._resolve_license_info(license_field)
                        except:
                            continue
                    else:
                        # Analyze text content
                        detected_license = self._detect_license_from_text(content)
                        if detected_license:
                            return self.license_database.get(detected_license)
                except Exception:
                    continue
        
        return None
    
    def _generate_license_summary(self, dependencies: List[DependencyLicense]) -> Dict[str, Any]:
        """Generate summary of license distribution."""
        summary = {
            'total_dependencies': len(dependencies),
            'license_types': {},
            'risk_levels': {},
            'unknown_licenses': 0,
            'direct_dependencies': 0,
            'transitive_dependencies': 0
        }
        
        for dep in dependencies:
            # Count by license type
            license_type = dep.license_detected.license_type.value
            summary['license_types'][license_type] = summary['license_types'].get(license_type, 0) + 1
            
            # Count by risk level
            risk_level = dep.license_detected.risk_level.value
            summary['risk_levels'][risk_level] = summary['risk_levels'].get(risk_level, 0) + 1
            
            # Count unknowns
            if dep.license_detected.license_type == LicenseType.UNKNOWN:
                summary['unknown_licenses'] += 1
            
            # Count direct vs transitive
            if dep.direct:
                summary['direct_dependencies'] += 1
            else:
                summary['transitive_dependencies'] += 1
        
        return summary
    
    def _detect_license_conflicts(self, project_license: Optional[str], 
                                 dependencies: List[DependencyLicense]) -> List[LicenseConflict]:
        """Detect license compatibility conflicts."""
        conflicts = []
        
        if not project_license:
            # If no project license detected, flag as potential issue
            for dep in dependencies:
                if dep.license_detected.risk_level in [RiskLevel.HIGH, RiskLevel.CRITICAL]:
                    conflicts.append(LicenseConflict(
                        dependency1='Project',
                        license1='Unknown',
                        dependency2=dep.name,
                        license2=dep.license_detected.spdx_id or dep.license_detected.name,
                        conflict_type='Unknown project license',
                        severity=RiskLevel.HIGH,
                        description=f'Project license unknown, dependency {dep.name} has {dep.license_detected.risk_level.value} risk license',
                        resolution_options=['Define project license', 'Review dependency usage']
                    ))
            return conflicts
        
        project_license_info = self.license_database.get(project_license)
        if not project_license_info:
            return conflicts
        
        # Check compatibility with project license
        for dep in dependencies:
            dep_license_id = dep.license_detected.spdx_id or 'UNKNOWN'
            
            # Check compatibility matrix
            if project_license in self.compatibility_matrix:
                compatibility = self.compatibility_matrix[project_license].get(dep_license_id, False)
                
                if not compatibility:
                    severity = self._determine_conflict_severity(project_license_info, dep.license_detected)
                    
                    conflicts.append(LicenseConflict(
                        dependency1='Project',
                        license1=project_license,
                        dependency2=dep.name,
                        license2=dep_license_id,
                        conflict_type='License incompatibility',
                        severity=severity,
                        description=f'Project license {project_license} is incompatible with dependency license {dep_license_id}',
                        resolution_options=self._generate_conflict_resolutions(project_license, dep_license_id)
                    ))
        
        # Check for GPL contamination in permissive projects
        if project_license_info.license_type == LicenseType.PERMISSIVE:
            for dep in dependencies:
                if dep.license_detected.license_type == LicenseType.COPYLEFT_STRONG:
                    conflicts.append(LicenseConflict(
                        dependency1='Project',
                        license1=project_license,
                        dependency2=dep.name,
                        license2=dep.license_detected.spdx_id or dep.license_detected.name,
                        conflict_type='GPL contamination',
                        severity=RiskLevel.CRITICAL,
                        description=f'GPL dependency {dep.name} may contaminate permissive project',
                        resolution_options=['Remove GPL dependency', 'Change project license to GPL', 
                                          'Use dynamic linking', 'Find alternative dependency']
                    ))
        
        return conflicts
    
    def _determine_conflict_severity(self, project_license: LicenseInfo, dep_license: LicenseInfo) -> RiskLevel:
        """Determine severity of a license conflict."""
        if dep_license.license_type == LicenseType.UNKNOWN:
            return RiskLevel.CRITICAL
        elif (project_license.license_type == LicenseType.PERMISSIVE and 
              dep_license.license_type == LicenseType.COPYLEFT_STRONG):
            return RiskLevel.CRITICAL
        elif dep_license.license_type == LicenseType.PROPRIETARY:
            return RiskLevel.HIGH
        else:
            return RiskLevel.MEDIUM
    
    def _generate_conflict_resolutions(self, project_license: str, dep_license: str) -> List[str]:
        """Generate resolution options for license conflicts."""
        resolutions = []
        
        if 'GPL' in dep_license:
            resolutions.extend([
                'Find alternative non-GPL dependency',
                'Use dynamic linking if possible',
                'Consider changing project license to GPL-compatible',
                'Remove the dependency if not essential'
            ])
        elif dep_license == 'PROPRIETARY':
            resolutions.extend([
                'Obtain commercial license',
                'Find open-source alternative',
                'Remove dependency if not essential',
                'Negotiate license terms'
            ])
        else:
            resolutions.extend([
                'Review license compatibility carefully',
                'Consult legal counsel',
                'Find alternative dependency',
                'Consider license exception'
            ])
        
        return resolutions
    
    def _calculate_compliance_score(self, dependencies: List[DependencyLicense], 
                                   conflicts: List[LicenseConflict]) -> float:
        """Calculate overall compliance score (0-100)."""
        if not dependencies:
            return 100.0
        
        base_score = 100.0
        
        # Deduct points for unknown licenses
        unknown_count = sum(1 for dep in dependencies 
                           if dep.license_detected.license_type == LicenseType.UNKNOWN)
        base_score -= (unknown_count / len(dependencies)) * 30
        
        # Deduct points for high-risk licenses
        high_risk_count = sum(1 for dep in dependencies 
                             if dep.license_detected.risk_level in [RiskLevel.HIGH, RiskLevel.CRITICAL])
        base_score -= (high_risk_count / len(dependencies)) * 20
        
        # Deduct points for conflicts
        if conflicts:
            critical_conflicts = sum(1 for c in conflicts if c.severity == RiskLevel.CRITICAL)
            high_conflicts = sum(1 for c in conflicts if c.severity == RiskLevel.HIGH)
            
            base_score -= critical_conflicts * 15
            base_score -= high_conflicts * 10
        
        return max(0.0, base_score)
    
    def _generate_risk_assessment(self, dependencies: List[DependencyLicense], 
                                 conflicts: List[LicenseConflict]) -> Dict[str, Any]:
        """Generate comprehensive risk assessment."""
        return {
            'overall_risk': self._calculate_overall_risk(dependencies, conflicts),
            'license_risk_breakdown': self._calculate_license_risks(dependencies),
            'conflict_summary': {
                'total_conflicts': len(conflicts),
                'critical_conflicts': len([c for c in conflicts if c.severity == RiskLevel.CRITICAL]),
                'high_conflicts': len([c for c in conflicts if c.severity == RiskLevel.HIGH])
            },
            'distribution_risks': self._assess_distribution_risks(dependencies),
            'commercial_risks': self._assess_commercial_risks(dependencies)
        }
    
    def _calculate_overall_risk(self, dependencies: List[DependencyLicense], 
                               conflicts: List[LicenseConflict]) -> str:
        """Calculate overall project risk level."""
        if any(c.severity == RiskLevel.CRITICAL for c in conflicts):
            return 'CRITICAL'
        elif any(dep.license_detected.risk_level == RiskLevel.CRITICAL for dep in dependencies):
            return 'CRITICAL'
        elif any(c.severity == RiskLevel.HIGH for c in conflicts):
            return 'HIGH'
        elif any(dep.license_detected.risk_level == RiskLevel.HIGH for dep in dependencies):
            return 'HIGH'
        elif any(dep.license_detected.risk_level == RiskLevel.MEDIUM for dep in dependencies):
            return 'MEDIUM'
        else:
            return 'LOW'
    
    def _calculate_license_risks(self, dependencies: List[DependencyLicense]) -> Dict[str, int]:
        """Calculate breakdown of license risks."""
        risks = {'low': 0, 'medium': 0, 'high': 0, 'critical': 0}
        
        for dep in dependencies:
            risk_level = dep.license_detected.risk_level.value
            risks[risk_level] += 1
        
        return risks
    
    def _assess_distribution_risks(self, dependencies: List[DependencyLicense]) -> List[str]:
        """Assess risks related to software distribution."""
        risks = []
        
        gpl_deps = [dep for dep in dependencies 
                   if dep.license_detected.license_type == LicenseType.COPYLEFT_STRONG]
        if gpl_deps:
            risks.append(f"GPL dependencies require source code disclosure: {[d.name for d in gpl_deps]}")
        
        proprietary_deps = [dep for dep in dependencies 
                           if dep.license_detected.license_type == LicenseType.PROPRIETARY]
        if proprietary_deps:
            risks.append(f"Proprietary dependencies may require commercial licenses: {[d.name for d in proprietary_deps]}")
        
        unknown_deps = [dep for dep in dependencies 
                       if dep.license_detected.license_type == LicenseType.UNKNOWN]
        if unknown_deps:
            risks.append(f"Unknown licenses pose legal uncertainty: {[d.name for d in unknown_deps]}")
        
        return risks
    
    def _assess_commercial_risks(self, dependencies: List[DependencyLicense]) -> List[str]:
        """Assess risks for commercial usage."""
        risks = []
        
        agpl_deps = [dep for dep in dependencies 
                    if dep.license_detected.spdx_id == 'AGPL-3.0']
        if agpl_deps:
            risks.append(f"AGPL dependencies trigger copyleft for network services: {[d.name for d in agpl_deps]}")
        
        return risks
    
    def _generate_compliance_recommendations(self, analysis_results: Dict[str, Any]) -> List[str]:
        """Generate actionable compliance recommendations."""
        recommendations = []
        
        # Address critical issues first
        critical_conflicts = [c for c in analysis_results['conflicts'] 
                             if c.severity == RiskLevel.CRITICAL]
        if critical_conflicts:
            recommendations.append("CRITICAL: Address license conflicts immediately before any distribution")
            for conflict in critical_conflicts[:3]:  # Top 3
                recommendations.append(f"  • {conflict.description}")
        
        # Unknown licenses
        unknown_count = analysis_results['license_summary']['unknown_licenses']
        if unknown_count > 0:
            recommendations.append(f"Investigate and clarify licenses for {unknown_count} dependencies with unknown licensing")
        
        # GPL contamination
        gpl_deps = [dep for dep in analysis_results['dependencies'] 
                   if dep.license_detected.license_type == LicenseType.COPYLEFT_STRONG]
        if gpl_deps and analysis_results.get('project_license') in ['MIT', 'Apache-2.0', 'BSD-3-Clause']:
            recommendations.append("Consider removing GPL dependencies or changing project license for permissive project")
        
        # Compliance score
        if analysis_results['compliance_score'] < 70:
            recommendations.append("Overall compliance score is low - prioritize license cleanup")
        
        return recommendations
    
    def generate_report(self, analysis_results: Dict[str, Any], format: str = 'text') -> str:
        """Generate compliance report in specified format."""
        if format == 'json':
            # Convert dataclass objects for JSON serialization
            serializable_results = analysis_results.copy()
            serializable_results['dependencies'] = [
                {
                    'name': dep.name,
                    'version': dep.version,
                    'ecosystem': dep.ecosystem,
                    'direct': dep.direct,
                    'license_declared': dep.license_declared,
                    'license_detected': asdict(dep.license_detected) if dep.license_detected else None,
                    'confidence': dep.confidence
                }
                for dep in analysis_results['dependencies']
            ]
            serializable_results['conflicts'] = [asdict(conflict) for conflict in analysis_results['conflicts']]
            return json.dumps(serializable_results, indent=2, default=str)
        
        # Text format report
        report = []
        report.append("=" * 60)
        report.append("LICENSE COMPLIANCE REPORT")
        report.append("=" * 60)
        report.append(f"Analysis Date: {analysis_results['timestamp']}")
        report.append(f"Project: {analysis_results['project_path']}")
        report.append(f"Project License: {analysis_results['project_license'] or 'Unknown'}")
        report.append("")
        
        # Summary
        summary = analysis_results['license_summary']
        report.append("SUMMARY:")
        report.append(f"  Total Dependencies: {summary['total_dependencies']}")
        report.append(f"  Compliance Score: {analysis_results['compliance_score']:.1f}/100")
        report.append(f"  Overall Risk: {analysis_results['risk_assessment']['overall_risk']}")
        report.append(f"  License Conflicts: {len(analysis_results['conflicts'])}")
        report.append("")
        
        # License distribution
        report.append("LICENSE DISTRIBUTION:")
        for license_type, count in summary['license_types'].items():
            report.append(f"  {license_type.title()}: {count}")
        report.append("")
        
        # Risk breakdown
        report.append("RISK BREAKDOWN:")
        for risk_level, count in summary['risk_levels'].items():
            report.append(f"  {risk_level.title()}: {count}")
        report.append("")
        
        # Conflicts
        if analysis_results['conflicts']:
            report.append("LICENSE CONFLICTS:")
            report.append("-" * 30)
            for conflict in analysis_results['conflicts']:
                report.append(f"Conflict: {conflict.dependency2} ({conflict.license2})")
                report.append(f"  Issue: {conflict.description}")
                report.append(f"  Severity: {conflict.severity.value.upper()}")
                report.append(f"  Resolutions: {', '.join(conflict.resolution_options[:2])}")
                report.append("")
        
        # High-risk dependencies
        high_risk_deps = [dep for dep in analysis_results['dependencies'] 
                         if dep.license_detected.risk_level in [RiskLevel.HIGH, RiskLevel.CRITICAL]]
        if high_risk_deps:
            report.append("HIGH-RISK DEPENDENCIES:")
            report.append("-" * 30)
            for dep in high_risk_deps[:10]:  # Top 10
                license_name = dep.license_detected.spdx_id or dep.license_detected.name
                report.append(f"  {dep.name} v{dep.version}: {license_name} ({dep.license_detected.risk_level.value.upper()})")
            report.append("")
        
        # Recommendations
        if analysis_results['recommendations']:
            report.append("RECOMMENDATIONS:")
            report.append("-" * 20)
            for i, rec in enumerate(analysis_results['recommendations'], 1):
                report.append(f"{i}. {rec}")
            report.append("")
        
        report.append("=" * 60)
        return '\n'.join(report)

def main():
    """Main entry point for the license checker."""
    parser = argparse.ArgumentParser(
        description='Analyze dependency licenses for compliance and conflicts',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python license_checker.py /path/to/project
  python license_checker.py . --format json --output compliance.json
  python license_checker.py /app --inventory deps.json --policy strict
        """
    )
    
    parser.add_argument('project_path',
                       help='Path to the project directory to analyze')
    parser.add_argument('--inventory',
                       help='Path to dependency inventory JSON file')
    parser.add_argument('--format', choices=['text', 'json'], default='text',
                       help='Output format (default: text)')
    parser.add_argument('--output', '-o',
                       help='Output file path (default: stdout)')
    parser.add_argument('--policy', choices=['permissive', 'strict'], default='permissive',
                       help='License policy strictness (default: permissive)')
    parser.add_argument('--warn-conflicts', action='store_true',
                       help='Show warnings for potential conflicts')
    
    args = parser.parse_args()
    
    try:
        checker = LicenseChecker()
        results = checker.analyze_project(args.project_path, args.inventory)
        report = checker.generate_report(results, args.format)
        
        if args.output:
            with open(args.output, 'w') as f:
                f.write(report)
            print(f"Compliance report saved to {args.output}")
        else:
            print(report)
        
        # Exit with error code for policy violations
        if args.policy == 'strict' and results['compliance_score'] < 80:
            sys.exit(1)
        
        if args.warn_conflicts and results['conflicts']:
            print("\nWARNING: License conflicts detected!")
            sys.exit(2)
    
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()