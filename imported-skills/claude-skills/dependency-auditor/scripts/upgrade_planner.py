#!/usr/bin/env python3
"""
Upgrade Planner - Dependency upgrade path planning and risk analysis tool.

This script analyzes dependency inventories, evaluates semantic versioning patterns,
estimates breaking change risks, and generates prioritized upgrade plans with
migration checklists and rollback procedures.

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
from datetime import datetime, timedelta
from enum import Enum
import re
import subprocess

class UpgradeRisk(Enum):
    """Upgrade risk levels."""
    SAFE = "safe"
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    CRITICAL = "critical"

class UpdateType(Enum):
    """Semantic versioning update types."""
    PATCH = "patch"
    MINOR = "minor"
    MAJOR = "major"
    PRERELEASE = "prerelease"

@dataclass
class VersionInfo:
    """Represents version information."""
    major: int
    minor: int
    patch: int
    prerelease: Optional[str] = None
    build: Optional[str] = None
    
    def __str__(self):
        version = f"{self.major}.{self.minor}.{self.patch}"
        if self.prerelease:
            version += f"-{self.prerelease}"
        if self.build:
            version += f"+{self.build}"
        return version

@dataclass
class DependencyUpgrade:
    """Represents a potential dependency upgrade."""
    name: str
    current_version: str
    latest_version: str
    ecosystem: str
    direct: bool
    update_type: UpdateType
    risk_level: UpgradeRisk
    security_updates: List[str]
    breaking_changes: List[str]
    migration_effort: str
    dependencies_affected: List[str]
    rollback_complexity: str
    estimated_time: str
    priority_score: float

@dataclass
class UpgradePlan:
    """Represents a complete upgrade plan."""
    name: str
    description: str
    phase: int
    dependencies: List[str]
    estimated_duration: str
    prerequisites: List[str]
    migration_steps: List[str]
    testing_requirements: List[str]
    rollback_plan: List[str]
    success_criteria: List[str]

class UpgradePlanner:
    """Main upgrade planning and risk analysis class."""
    
    def __init__(self):
        self.breaking_change_patterns = self._build_breaking_change_patterns()
        self.ecosystem_knowledge = self._build_ecosystem_knowledge()
        self.security_advisories = self._build_security_advisories()
    
    def _build_breaking_change_patterns(self) -> Dict[str, List[str]]:
        """Build patterns for detecting breaking changes."""
        return {
            'npm': [
                r'BREAKING\s*CHANGE',
                r'breaking\s*change',
                r'major\s*version',
                r'removed.*API',
                r'deprecated.*removed',
                r'no\s*longer\s*supported',
                r'minimum.*node.*version',
                r'peer.*dependency.*change'
            ],
            'pypi': [
                r'BREAKING\s*CHANGE',
                r'breaking\s*change',
                r'removed.*function',
                r'deprecated.*removed',
                r'minimum.*python.*version',
                r'incompatible.*change',
                r'API.*change'
            ],
            'maven': [
                r'BREAKING\s*CHANGE',
                r'breaking\s*change',
                r'removed.*method',
                r'deprecated.*removed',
                r'minimum.*java.*version',
                r'API.*incompatible'
            ]
        }
    
    def _build_ecosystem_knowledge(self) -> Dict[str, Dict[str, Any]]:
        """Build ecosystem-specific upgrade knowledge."""
        return {
            'npm': {
                'typical_major_cycle_months': 12,
                'typical_patch_cycle_weeks': 2,
                'deprecation_notice_months': 6,
                'lts_support_years': 3,
                'common_breaking_changes': [
                    'Node.js version requirements',
                    'Peer dependency updates',
                    'API signature changes',
                    'Configuration format changes'
                ]
            },
            'pypi': {
                'typical_major_cycle_months': 18,
                'typical_patch_cycle_weeks': 4,
                'deprecation_notice_months': 12,
                'lts_support_years': 2,
                'common_breaking_changes': [
                    'Python version requirements',
                    'Function signature changes',
                    'Import path changes',
                    'Configuration changes'
                ]
            },
            'maven': {
                'typical_major_cycle_months': 24,
                'typical_patch_cycle_weeks': 6,
                'deprecation_notice_months': 12,
                'lts_support_years': 5,
                'common_breaking_changes': [
                    'Java version requirements',
                    'Method signature changes',
                    'Package restructuring',
                    'Dependency changes'
                ]
            },
            'cargo': {
                'typical_major_cycle_months': 6,
                'typical_patch_cycle_weeks': 2,
                'deprecation_notice_months': 3,
                'lts_support_years': 1,
                'common_breaking_changes': [
                    'Rust edition changes',
                    'Trait changes',
                    'Module restructuring',
                    'Macro changes'
                ]
            }
        }
    
    def _build_security_advisories(self) -> Dict[str, List[Dict[str, Any]]]:
        """Build security advisory database for upgrade prioritization."""
        return {
            'lodash': [
                {
                    'advisory_id': 'CVE-2021-23337',
                    'severity': 'HIGH',
                    'fixed_in': '4.17.21',
                    'description': 'Prototype pollution vulnerability'
                }
            ],
            'django': [
                {
                    'advisory_id': 'CVE-2024-27351',
                    'severity': 'HIGH',
                    'fixed_in': '4.2.11',
                    'description': 'SQL injection vulnerability'
                }
            ],
            'express': [
                {
                    'advisory_id': 'CVE-2022-24999',
                    'severity': 'MEDIUM',
                    'fixed_in': '4.18.2',
                    'description': 'Open redirect vulnerability'
                }
            ],
            'axios': [
                {
                    'advisory_id': 'CVE-2023-45857',
                    'severity': 'MEDIUM',
                    'fixed_in': '1.6.0',
                    'description': 'Cross-site request forgery'
                }
            ]
        }
    
    def analyze_upgrades(self, dependency_inventory: str, timeline_days: int = 90) -> Dict[str, Any]:
        """Analyze potential dependency upgrades and create upgrade plan."""
        dependencies = self._load_dependency_inventory(dependency_inventory)
        
        analysis_results = {
            'timestamp': datetime.now().isoformat(),
            'timeline_days': timeline_days,
            'dependencies_analyzed': len(dependencies),
            'available_upgrades': [],
            'upgrade_statistics': {},
            'risk_assessment': {},
            'upgrade_plans': [],
            'recommendations': []
        }
        
        # Analyze each dependency for upgrades
        for dep in dependencies:
            upgrade_info = self._analyze_dependency_upgrade(dep)
            if upgrade_info:
                analysis_results['available_upgrades'].append(upgrade_info)
        
        # Generate upgrade statistics
        analysis_results['upgrade_statistics'] = self._generate_upgrade_statistics(
            analysis_results['available_upgrades']
        )
        
        # Perform risk assessment
        analysis_results['risk_assessment'] = self._perform_risk_assessment(
            analysis_results['available_upgrades']
        )
        
        # Create phased upgrade plans
        analysis_results['upgrade_plans'] = self._create_upgrade_plans(
            analysis_results['available_upgrades'],
            timeline_days
        )
        
        # Generate recommendations
        analysis_results['recommendations'] = self._generate_upgrade_recommendations(
            analysis_results
        )
        
        return analysis_results
    
    def _load_dependency_inventory(self, inventory_path: str) -> List[Dict[str, Any]]:
        """Load dependency inventory from JSON file."""
        try:
            with open(inventory_path, 'r') as f:
                data = json.load(f)
            
            if 'dependencies' in data:
                return data['dependencies']
            elif isinstance(data, list):
                return data
            else:
                print("Warning: Unexpected inventory format")
                return []
        
        except Exception as e:
            print(f"Error loading dependency inventory: {e}")
            return []
    
    def _analyze_dependency_upgrade(self, dependency: Dict[str, Any]) -> Optional[DependencyUpgrade]:
        """Analyze upgrade possibilities for a single dependency."""
        name = dependency.get('name', '')
        current_version = dependency.get('version', '').replace('^', '').replace('~', '')
        ecosystem = dependency.get('ecosystem', '')
        
        if not name or not current_version:
            return None
        
        # Parse current version
        current_ver = self._parse_version(current_version)
        if not current_ver:
            return None
        
        # Get latest version (simulated - in practice would query package registries)
        latest_version = self._get_latest_version(name, ecosystem)
        if not latest_version:
            return None
        
        latest_ver = self._parse_version(latest_version)
        if not latest_ver:
            return None
        
        # Determine if upgrade is needed
        if self._compare_versions(current_ver, latest_ver) >= 0:
            return None  # Already up to date
        
        # Determine update type
        update_type = self._determine_update_type(current_ver, latest_ver)
        
        # Assess upgrade risk
        risk_level = self._assess_upgrade_risk(name, current_ver, latest_ver, ecosystem, update_type)
        
        # Check for security updates
        security_updates = self._check_security_updates(name, current_version, latest_version)
        
        # Analyze breaking changes
        breaking_changes = self._analyze_breaking_changes(name, current_ver, latest_ver, ecosystem)
        
        # Calculate priority score
        priority_score = self._calculate_priority_score(
            update_type, risk_level, security_updates, dependency.get('direct', False)
        )
        
        return DependencyUpgrade(
            name=name,
            current_version=current_version,
            latest_version=latest_version,
            ecosystem=ecosystem,
            direct=dependency.get('direct', False),
            update_type=update_type,
            risk_level=risk_level,
            security_updates=security_updates,
            breaking_changes=breaking_changes,
            migration_effort=self._estimate_migration_effort(update_type, breaking_changes),
            dependencies_affected=self._get_affected_dependencies(name, dependency),
            rollback_complexity=self._assess_rollback_complexity(update_type, risk_level),
            estimated_time=self._estimate_upgrade_time(update_type, breaking_changes),
            priority_score=priority_score
        )
    
    def _parse_version(self, version_string: str) -> Optional[VersionInfo]:
        """Parse semantic version string."""
        # Clean version string
        version = re.sub(r'[^0-9a-zA-Z.-]', '', version_string)
        
        # Basic semver pattern
        pattern = r'^(\d+)\.(\d+)\.(\d+)(?:-([0-9A-Za-z.-]+))?(?:\+([0-9A-Za-z.-]+))?$'
        match = re.match(pattern, version)
        
        if match:
            major, minor, patch, prerelease, build = match.groups()
            return VersionInfo(
                major=int(major),
                minor=int(minor),
                patch=int(patch),
                prerelease=prerelease,
                build=build
            )
        
        # Fallback for simpler version patterns
        simple_pattern = r'^(\d+)\.(\d+)(?:\.(\d+))?'
        match = re.match(simple_pattern, version)
        if match:
            major, minor, patch = match.groups()
            return VersionInfo(
                major=int(major),
                minor=int(minor),
                patch=int(patch or 0)
            )
        
        return None
    
    def _compare_versions(self, v1: VersionInfo, v2: VersionInfo) -> int:
        """Compare two versions. Returns -1, 0, or 1."""
        if (v1.major, v1.minor, v1.patch) < (v2.major, v2.minor, v2.patch):
            return -1
        elif (v1.major, v1.minor, v1.patch) > (v2.major, v2.minor, v2.patch):
            return 1
        else:
            # Handle prerelease comparison
            if v1.prerelease and not v2.prerelease:
                return -1
            elif not v1.prerelease and v2.prerelease:
                return 1
            elif v1.prerelease and v2.prerelease:
                if v1.prerelease < v2.prerelease:
                    return -1
                elif v1.prerelease > v2.prerelease:
                    return 1
            
            return 0
    
    def _get_latest_version(self, package_name: str, ecosystem: str) -> Optional[str]:
        """Get latest version from package registry (simulated)."""
        # Simulated latest versions for common packages
        mock_versions = {
            'lodash': '4.17.21',
            'express': '4.18.2',
            'react': '18.2.0',
            'axios': '1.6.0',
            'django': '4.2.11',
            'requests': '2.31.0',
            'numpy': '1.24.0',
            'flask': '2.3.0',
            'fastapi': '0.104.0',
            'pytest': '7.4.0'
        }
        
        # In production, would query actual package registries:
        # npm: npm view <package> version
        # pypi: pip index versions <package>
        # maven: maven metadata API
        
        return mock_versions.get(package_name.lower())
    
    def _determine_update_type(self, current: VersionInfo, latest: VersionInfo) -> UpdateType:
        """Determine the type of update based on semantic versioning."""
        if latest.major > current.major:
            return UpdateType.MAJOR
        elif latest.minor > current.minor:
            return UpdateType.MINOR
        elif latest.patch > current.patch:
            return UpdateType.PATCH
        elif latest.prerelease and not current.prerelease:
            return UpdateType.PRERELEASE
        else:
            return UpdateType.PATCH  # Default fallback
    
    def _assess_upgrade_risk(self, package_name: str, current: VersionInfo, latest: VersionInfo,
                            ecosystem: str, update_type: UpdateType) -> UpgradeRisk:
        """Assess the risk level of an upgrade."""
        # Base risk assessment on update type
        base_risk = {
            UpdateType.PATCH: UpgradeRisk.SAFE,
            UpdateType.MINOR: UpgradeRisk.LOW,
            UpdateType.MAJOR: UpgradeRisk.HIGH,
            UpdateType.PRERELEASE: UpgradeRisk.MEDIUM
        }.get(update_type, UpgradeRisk.MEDIUM)
        
        # Adjust for package-specific factors
        high_risk_packages = [
            'webpack', 'babel', 'typescript', 'eslint',  # Build tools
            'react', 'vue', 'angular',  # Frameworks
            'django', 'flask', 'fastapi',  # Web frameworks
            'spring-boot', 'hibernate'  # Java frameworks
        ]
        
        if package_name.lower() in high_risk_packages and update_type == UpdateType.MAJOR:
            base_risk = UpgradeRisk.CRITICAL
        
        # Check for known breaking changes
        if self._has_known_breaking_changes(package_name, current, latest):
            if base_risk in [UpgradeRisk.SAFE, UpgradeRisk.LOW]:
                base_risk = UpgradeRisk.MEDIUM
            elif base_risk == UpgradeRisk.MEDIUM:
                base_risk = UpgradeRisk.HIGH
        
        return base_risk
    
    def _has_known_breaking_changes(self, package_name: str, current: VersionInfo, latest: VersionInfo) -> bool:
        """Check if there are known breaking changes between versions."""
        # Simulated breaking change detection
        breaking_change_versions = {
            'react': ['16.0.0', '17.0.0', '18.0.0'],
            'django': ['2.0.0', '3.0.0', '4.0.0'],
            'webpack': ['4.0.0', '5.0.0'],
            'babel': ['7.0.0', '8.0.0'],
            'typescript': ['4.0.0', '5.0.0']
        }
        
        package_versions = breaking_change_versions.get(package_name.lower(), [])
        latest_str = str(latest)
        
        return any(latest_str.startswith(v.split('.')[0]) for v in package_versions)
    
    def _check_security_updates(self, package_name: str, current_version: str, latest_version: str) -> List[str]:
        """Check for security updates in the upgrade."""
        security_updates = []
        
        if package_name in self.security_advisories:
            for advisory in self.security_advisories[package_name]:
                fixed_version = advisory['fixed_in']
                
                # Simple version comparison for security fixes
                if (self._is_version_greater(fixed_version, current_version) and
                    not self._is_version_greater(fixed_version, latest_version)):
                    security_updates.append(f"{advisory['advisory_id']}: {advisory['description']}")
        
        return security_updates
    
    def _is_version_greater(self, v1: str, v2: str) -> bool:
        """Simple version comparison."""
        v1_parts = [int(x) for x in v1.split('.')]
        v2_parts = [int(x) for x in v2.split('.')]
        
        # Pad shorter version
        max_len = max(len(v1_parts), len(v2_parts))
        v1_parts.extend([0] * (max_len - len(v1_parts)))
        v2_parts.extend([0] * (max_len - len(v2_parts)))
        
        return v1_parts > v2_parts
    
    def _analyze_breaking_changes(self, package_name: str, current: VersionInfo, 
                                 latest: VersionInfo, ecosystem: str) -> List[str]:
        """Analyze potential breaking changes."""
        breaking_changes = []
        
        # Check if major version change
        if latest.major > current.major:
            breaking_changes.append(f"Major version upgrade from {current.major}.x to {latest.major}.x")
            
            # Add ecosystem-specific common breaking changes
            ecosystem_knowledge = self.ecosystem_knowledge.get(ecosystem, {})
            common_changes = ecosystem_knowledge.get('common_breaking_changes', [])
            breaking_changes.extend(common_changes[:2])  # Add top 2
        
        # Check for specific package patterns
        if package_name.lower() == 'react' and latest.major >= 17:
            breaking_changes.append("New JSX Transform")
            if latest.major >= 18:
                breaking_changes.append("Concurrent Rendering changes")
        
        elif package_name.lower() == 'django' and latest.major >= 4:
            breaking_changes.append("CSRF token changes")
            breaking_changes.append("Default AUTO_INCREMENT field changes")
        
        elif package_name.lower() == 'webpack' and latest.major >= 5:
            breaking_changes.append("Module Federation support")
            breaking_changes.append("Asset modules replace file-loader")
        
        return breaking_changes
    
    def _calculate_priority_score(self, update_type: UpdateType, risk_level: UpgradeRisk,
                                 security_updates: List[str], is_direct: bool) -> float:
        """Calculate priority score for upgrade (0-100)."""
        score = 50.0  # Base score
        
        # Security updates get highest priority
        if security_updates:
            score += 30.0
            score += len(security_updates) * 5.0  # Multiple security fixes
        
        # Update type scoring
        type_scores = {
            UpdateType.PATCH: 20.0,
            UpdateType.MINOR: 10.0,
            UpdateType.MAJOR: -10.0,
            UpdateType.PRERELEASE: -5.0
        }
        score += type_scores.get(update_type, 0)
        
        # Risk level adjustment
        risk_adjustments = {
            UpgradeRisk.SAFE: 15.0,
            UpgradeRisk.LOW: 5.0,
            UpgradeRisk.MEDIUM: -5.0,
            UpgradeRisk.HIGH: -15.0,
            UpgradeRisk.CRITICAL: -25.0
        }
        score += risk_adjustments.get(risk_level, 0)
        
        # Direct dependencies get slightly higher priority
        if is_direct:
            score += 5.0
        
        return max(0.0, min(100.0, score))
    
    def _estimate_migration_effort(self, update_type: UpdateType, breaking_changes: List[str]) -> str:
        """Estimate migration effort level."""
        if update_type == UpdateType.PATCH and not breaking_changes:
            return "Minimal"
        elif update_type == UpdateType.MINOR and len(breaking_changes) <= 1:
            return "Low"
        elif update_type == UpdateType.MAJOR or len(breaking_changes) > 2:
            return "High"
        else:
            return "Medium"
    
    def _get_affected_dependencies(self, package_name: str, dependency: Dict[str, Any]) -> List[str]:
        """Get list of dependencies that might be affected by this upgrade."""
        # Simulated dependency impact analysis
        common_dependencies = {
            'react': ['react-dom', 'react-router', 'react-redux'],
            'django': ['djangorestframework', 'django-cors-headers', 'celery'],
            'webpack': ['webpack-cli', 'webpack-dev-server', 'html-webpack-plugin'],
            'babel': ['@babel/core', '@babel/preset-env', '@babel/preset-react']
        }
        
        return common_dependencies.get(package_name.lower(), [])
    
    def _assess_rollback_complexity(self, update_type: UpdateType, risk_level: UpgradeRisk) -> str:
        """Assess complexity of rolling back the upgrade."""
        if update_type == UpdateType.PATCH:
            return "Simple"
        elif update_type == UpdateType.MINOR and risk_level in [UpgradeRisk.SAFE, UpgradeRisk.LOW]:
            return "Simple"
        elif risk_level in [UpgradeRisk.HIGH, UpgradeRisk.CRITICAL]:
            return "Complex"
        else:
            return "Moderate"
    
    def _estimate_upgrade_time(self, update_type: UpdateType, breaking_changes: List[str]) -> str:
        """Estimate time required for upgrade."""
        base_times = {
            UpdateType.PATCH: "30 minutes",
            UpdateType.MINOR: "2 hours",
            UpdateType.MAJOR: "1 day",
            UpdateType.PRERELEASE: "4 hours"
        }
        
        base_time = base_times.get(update_type, "4 hours")
        
        if len(breaking_changes) > 2:
            if "30 minutes" in base_time:
                base_time = "2 hours"
            elif "2 hours" in base_time:
                base_time = "1 day"
            elif "1 day" in base_time:
                base_time = "3 days"
        
        return base_time
    
    def _generate_upgrade_statistics(self, upgrades: List[DependencyUpgrade]) -> Dict[str, Any]:
        """Generate statistics about available upgrades."""
        if not upgrades:
            return {}
        
        return {
            'total_upgrades': len(upgrades),
            'by_type': {
                'patch': len([u for u in upgrades if u.update_type == UpdateType.PATCH]),
                'minor': len([u for u in upgrades if u.update_type == UpdateType.MINOR]),
                'major': len([u for u in upgrades if u.update_type == UpdateType.MAJOR]),
                'prerelease': len([u for u in upgrades if u.update_type == UpdateType.PRERELEASE])
            },
            'by_risk': {
                'safe': len([u for u in upgrades if u.risk_level == UpgradeRisk.SAFE]),
                'low': len([u for u in upgrades if u.risk_level == UpgradeRisk.LOW]),
                'medium': len([u for u in upgrades if u.risk_level == UpgradeRisk.MEDIUM]),
                'high': len([u for u in upgrades if u.risk_level == UpgradeRisk.HIGH]),
                'critical': len([u for u in upgrades if u.risk_level == UpgradeRisk.CRITICAL])
            },
            'security_updates': len([u for u in upgrades if u.security_updates]),
            'direct_dependencies': len([u for u in upgrades if u.direct]),
            'average_priority': sum(u.priority_score for u in upgrades) / len(upgrades)
        }
    
    def _perform_risk_assessment(self, upgrades: List[DependencyUpgrade]) -> Dict[str, Any]:
        """Perform comprehensive risk assessment."""
        high_risk_upgrades = [u for u in upgrades if u.risk_level in [UpgradeRisk.HIGH, UpgradeRisk.CRITICAL]]
        security_upgrades = [u for u in upgrades if u.security_updates]
        major_upgrades = [u for u in upgrades if u.update_type == UpdateType.MAJOR]
        
        return {
            'overall_risk': self._calculate_overall_upgrade_risk(upgrades),
            'high_risk_count': len(high_risk_upgrades),
            'security_critical_count': len(security_upgrades),
            'major_version_count': len(major_upgrades),
            'risk_factors': self._identify_risk_factors(upgrades),
            'mitigation_strategies': self._suggest_mitigation_strategies(upgrades)
        }
    
    def _calculate_overall_upgrade_risk(self, upgrades: List[DependencyUpgrade]) -> str:
        """Calculate overall risk level for all upgrades."""
        if not upgrades:
            return "LOW"
        
        risk_scores = {
            UpgradeRisk.SAFE: 1,
            UpgradeRisk.LOW: 2,
            UpgradeRisk.MEDIUM: 3,
            UpgradeRisk.HIGH: 4,
            UpgradeRisk.CRITICAL: 5
        }
        
        total_score = sum(risk_scores.get(u.risk_level, 3) for u in upgrades)
        average_score = total_score / len(upgrades)
        
        if average_score >= 4.0:
            return "CRITICAL"
        elif average_score >= 3.0:
            return "HIGH"
        elif average_score >= 2.0:
            return "MEDIUM"
        else:
            return "LOW"
    
    def _identify_risk_factors(self, upgrades: List[DependencyUpgrade]) -> List[str]:
        """Identify key risk factors across all upgrades."""
        factors = []
        
        major_count = len([u for u in upgrades if u.update_type == UpdateType.MAJOR])
        if major_count > 0:
            factors.append(f"{major_count} major version upgrades with potential breaking changes")
        
        critical_count = len([u for u in upgrades if u.risk_level == UpgradeRisk.CRITICAL])
        if critical_count > 0:
            factors.append(f"{critical_count} critical risk upgrades requiring careful planning")
        
        framework_upgrades = [u for u in upgrades if any(fw in u.name.lower() 
                             for fw in ['react', 'django', 'spring', 'webpack', 'babel'])]
        if framework_upgrades:
            factors.append(f"Core framework upgrades: {[u.name for u in framework_upgrades[:3]]}")
        
        return factors
    
    def _suggest_mitigation_strategies(self, upgrades: List[DependencyUpgrade]) -> List[str]:
        """Suggest risk mitigation strategies."""
        strategies = []
        
        high_risk_count = len([u for u in upgrades if u.risk_level in [UpgradeRisk.HIGH, UpgradeRisk.CRITICAL]])
        if high_risk_count > 0:
            strategies.append("Create comprehensive test suite before high-risk upgrades")
            strategies.append("Plan rollback procedures for critical upgrades")
        
        major_count = len([u for u in upgrades if u.update_type == UpdateType.MAJOR])
        if major_count > 3:
            strategies.append("Phase major upgrades across multiple releases")
            strategies.append("Use feature flags for gradual rollout")
        
        security_count = len([u for u in upgrades if u.security_updates])
        if security_count > 0:
            strategies.append("Prioritize security updates regardless of risk level")
        
        return strategies
    
    def _create_upgrade_plans(self, upgrades: List[DependencyUpgrade], timeline_days: int) -> List[UpgradePlan]:
        """Create phased upgrade plans."""
        if not upgrades:
            return []
        
        # Sort upgrades by priority score (descending)
        sorted_upgrades = sorted(upgrades, key=lambda x: x.priority_score, reverse=True)
        
        plans = []
        
        # Phase 1: Security and safe updates (first 30% of timeline)
        phase1_upgrades = [u for u in sorted_upgrades if 
                          u.security_updates or u.risk_level == UpgradeRisk.SAFE][:10]
        if phase1_upgrades:
            plans.append(self._create_upgrade_plan(
                "Phase 1: Security & Safe Updates",
                "Immediate security fixes and low-risk updates",
                1, phase1_upgrades, timeline_days // 3
            ))
        
        # Phase 2: Low-medium risk updates (middle 40% of timeline)
        phase2_upgrades = [u for u in sorted_upgrades if 
                          u.risk_level in [UpgradeRisk.LOW, UpgradeRisk.MEDIUM] and
                          not u.security_updates][:8]
        if phase2_upgrades:
            plans.append(self._create_upgrade_plan(
                "Phase 2: Regular Updates",
                "Standard dependency updates with moderate risk",
                2, phase2_upgrades, timeline_days * 2 // 5
            ))
        
        # Phase 3: High-risk and major updates (final 30% of timeline)
        phase3_upgrades = [u for u in sorted_upgrades if 
                          u.risk_level in [UpgradeRisk.HIGH, UpgradeRisk.CRITICAL]][:5]
        if phase3_upgrades:
            plans.append(self._create_upgrade_plan(
                "Phase 3: Major Updates",
                "High-risk upgrades requiring careful planning",
                3, phase3_upgrades, timeline_days // 3
            ))
        
        return plans
    
    def _create_upgrade_plan(self, name: str, description: str, phase: int,
                            upgrades: List[DependencyUpgrade], duration_days: int) -> UpgradePlan:
        """Create a detailed upgrade plan for a phase."""
        dependency_names = [u.name for u in upgrades]
        
        # Generate migration steps
        migration_steps = []
        migration_steps.append("1. Create feature branch for upgrades")
        migration_steps.append("2. Update dependency versions in manifest files")
        migration_steps.append("3. Run dependency install/update commands")
        migration_steps.append("4. Fix breaking changes and deprecation warnings")
        migration_steps.append("5. Update test suite for compatibility")
        migration_steps.append("6. Run comprehensive test suite")
        migration_steps.append("7. Update documentation and changelog")
        migration_steps.append("8. Create pull request for review")
        
        # Add phase-specific steps
        if phase == 1:
            migration_steps.insert(3, "3a. Verify security fixes are applied")
        elif phase == 3:
            migration_steps.insert(5, "5a. Perform extensive integration testing")
            migration_steps.insert(6, "6a. Test with production-like data")
        
        # Generate testing requirements
        testing_requirements = [
            "Unit test suite passes 100%",
            "Integration tests cover upgrade scenarios",
            "Performance benchmarks within acceptable range"
        ]
        
        if any(u.risk_level in [UpgradeRisk.HIGH, UpgradeRisk.CRITICAL] for u in upgrades):
            testing_requirements.extend([
                "Manual testing of critical user flows",
                "Load testing for performance regression",
                "Security scanning for new vulnerabilities"
            ])
        
        # Generate rollback plan
        rollback_plan = [
            "1. Revert dependency versions in manifest files",
            "2. Run dependency install with previous versions",
            "3. Restore previous configuration files if changed",
            "4. Run smoke tests to verify rollback success",
            "5. Monitor system health metrics"
        ]
        
        # Success criteria
        success_criteria = [
            "All tests pass in CI/CD pipeline",
            "No security vulnerabilities introduced",
            "Performance metrics within acceptable thresholds",
            "No critical user workflows broken"
        ]
        
        return UpgradePlan(
            name=name,
            description=description,
            phase=phase,
            dependencies=dependency_names,
            estimated_duration=f"{duration_days} days",
            prerequisites=self._generate_prerequisites(upgrades),
            migration_steps=migration_steps,
            testing_requirements=testing_requirements,
            rollback_plan=rollback_plan,
            success_criteria=success_criteria
        )
    
    def _generate_prerequisites(self, upgrades: List[DependencyUpgrade]) -> List[str]:
        """Generate prerequisites for upgrade phase."""
        prerequisites = [
            "Comprehensive test suite with good coverage",
            "Backup of current working state",
            "Development environment setup"
        ]
        
        if any(u.risk_level in [UpgradeRisk.HIGH, UpgradeRisk.CRITICAL] for u in upgrades):
            prerequisites.extend([
                "Staging environment for testing",
                "Rollback procedure documented and tested",
                "Team availability for issue resolution"
            ])
        
        if any(u.security_updates for u in upgrades):
            prerequisites.append("Security team notification for validation")
        
        return prerequisites
    
    def _generate_upgrade_recommendations(self, analysis_results: Dict[str, Any]) -> List[str]:
        """Generate actionable upgrade recommendations."""
        recommendations = []
        
        security_count = analysis_results['upgrade_statistics'].get('security_updates', 0)
        if security_count > 0:
            recommendations.append(f"URGENT: {security_count} security updates available - prioritize immediately")
        
        safe_count = analysis_results['upgrade_statistics']['by_risk'].get('safe', 0)
        if safe_count > 0:
            recommendations.append(f"Quick wins: {safe_count} safe updates can be applied with minimal risk")
        
        critical_count = analysis_results['risk_assessment']['high_risk_count']
        if critical_count > 0:
            recommendations.append(f"Plan carefully: {critical_count} high-risk upgrades need thorough testing")
        
        major_count = analysis_results['upgrade_statistics']['by_type'].get('major', 0)
        if major_count > 3:
            recommendations.append("Consider phasing major upgrades across multiple releases")
        
        overall_risk = analysis_results['risk_assessment']['overall_risk']
        if overall_risk in ['HIGH', 'CRITICAL']:
            recommendations.append("Overall upgrade risk is high - recommend gradual approach")
        
        return recommendations
    
    def generate_report(self, analysis_results: Dict[str, Any], format: str = 'text') -> str:
        """Generate upgrade plan report in specified format."""
        if format == 'json':
            # Convert dataclass objects for JSON serialization
            serializable_results = analysis_results.copy()
            serializable_results['available_upgrades'] = [asdict(upgrade) for upgrade in analysis_results['available_upgrades']]
            serializable_results['upgrade_plans'] = [asdict(plan) for plan in analysis_results['upgrade_plans']]
            return json.dumps(serializable_results, indent=2, default=str)
        
        # Text format report
        report = []
        report.append("=" * 60)
        report.append("DEPENDENCY UPGRADE PLAN")
        report.append("=" * 60)
        report.append(f"Generated: {analysis_results['timestamp']}")
        report.append(f"Timeline: {analysis_results['timeline_days']} days")
        report.append("")
        
        # Statistics
        stats = analysis_results['upgrade_statistics']
        report.append("UPGRADE SUMMARY:")
        report.append(f"  Total Upgrades Available: {stats.get('total_upgrades', 0)}")
        report.append(f"  Security Updates: {stats.get('security_updates', 0)}")
        report.append(f"  Major Version Updates: {stats['by_type'].get('major', 0)}")
        report.append(f"  High Risk Updates: {stats['by_risk'].get('high', 0)}")
        report.append("")
        
        # Risk Assessment
        risk = analysis_results['risk_assessment']
        report.append("RISK ASSESSMENT:")
        report.append(f"  Overall Risk Level: {risk['overall_risk']}")
        if risk.get('risk_factors'):
            report.append("  Key Risk Factors:")
            for factor in risk['risk_factors'][:3]:
                report.append(f"    • {factor}")
        report.append("")
        
        # High Priority Upgrades
        high_priority = sorted([u for u in analysis_results['available_upgrades']], 
                              key=lambda x: x.priority_score, reverse=True)[:10]
        
        if high_priority:
            report.append("TOP PRIORITY UPGRADES:")
            report.append("-" * 30)
            for upgrade in high_priority:
                risk_indicator = "🔴" if upgrade.risk_level in [UpgradeRisk.HIGH, UpgradeRisk.CRITICAL] else \
                               "🟡" if upgrade.risk_level == UpgradeRisk.MEDIUM else "🟢"
                security_indicator = " 🔒" if upgrade.security_updates else ""
                
                report.append(f"{risk_indicator} {upgrade.name}: {upgrade.current_version} → {upgrade.latest_version}{security_indicator}")
                report.append(f"   Type: {upgrade.update_type.value.title()} | Risk: {upgrade.risk_level.value.title()} | Priority: {upgrade.priority_score:.1f}")
                if upgrade.security_updates:
                    report.append(f"   Security: {upgrade.security_updates[0]}")
                report.append("")
        
        # Upgrade Plans
        if analysis_results['upgrade_plans']:
            report.append("PHASED UPGRADE PLANS:")
            report.append("-" * 30)
            
            for plan in analysis_results['upgrade_plans']:
                report.append(f"{plan.name} ({plan.estimated_duration})")
                report.append(f"  Dependencies: {', '.join(plan.dependencies[:5])}")
                if len(plan.dependencies) > 5:
                    report.append(f"  ... and {len(plan.dependencies) - 5} more")
                report.append(f"  Key Steps: {'; '.join(plan.migration_steps[:3])}")
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
    """Main entry point for the upgrade planner."""
    parser = argparse.ArgumentParser(
        description='Analyze dependency upgrades and create migration plans',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python upgrade_planner.py deps.json
  python upgrade_planner.py inventory.json --timeline 60 --format json
  python upgrade_planner.py deps.json --risk-threshold medium --output plan.txt
        """
    )
    
    parser.add_argument('inventory_file',
                       help='Path to dependency inventory JSON file')
    parser.add_argument('--timeline', type=int, default=90,
                       help='Timeline for upgrade plan in days (default: 90)')
    parser.add_argument('--format', choices=['text', 'json'], default='text',
                       help='Output format (default: text)')
    parser.add_argument('--output', '-o',
                       help='Output file path (default: stdout)')
    parser.add_argument('--risk-threshold', 
                       choices=['safe', 'low', 'medium', 'high', 'critical'],
                       default='high',
                       help='Maximum risk level to include (default: high)')
    parser.add_argument('--security-only', action='store_true',
                       help='Only plan upgrades with security fixes')
    
    args = parser.parse_args()
    
    try:
        planner = UpgradePlanner()
        results = planner.analyze_upgrades(args.inventory_file, args.timeline)
        
        # Filter by risk threshold if specified
        if args.risk_threshold != 'critical':
            risk_levels = ['safe', 'low', 'medium', 'high', 'critical']
            max_index = risk_levels.index(args.risk_threshold)
            allowed_risks = set(risk_levels[:max_index + 1])
            
            results['available_upgrades'] = [
                u for u in results['available_upgrades']
                if u.risk_level.value in allowed_risks
            ]
        
        # Filter for security-only if specified
        if args.security_only:
            results['available_upgrades'] = [
                u for u in results['available_upgrades']
                if u.security_updates
            ]
        
        report = planner.generate_report(results, args.format)
        
        if args.output:
            with open(args.output, 'w') as f:
                f.write(report)
            print(f"Upgrade plan saved to {args.output}")
        else:
            print(report)
    
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()