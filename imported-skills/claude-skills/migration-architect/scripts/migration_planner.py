#!/usr/bin/env python3
"""
Migration Planner - Generate comprehensive migration plans with risk assessment

This tool analyzes migration specifications and generates detailed, phased migration plans
including pre-migration checklists, validation gates, rollback triggers, timeline estimates,
and risk matrices.

Author: Migration Architect Skill
Version: 1.0.0
License: MIT
"""

import json
import argparse
import sys
import datetime
import hashlib
import math
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from enum import Enum


class MigrationType(Enum):
    """Migration type enumeration"""
    DATABASE = "database"
    SERVICE = "service"
    INFRASTRUCTURE = "infrastructure"
    DATA = "data"
    API = "api"


class MigrationComplexity(Enum):
    """Migration complexity levels"""
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    CRITICAL = "critical"


class RiskLevel(Enum):
    """Risk assessment levels"""
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    CRITICAL = "critical"


@dataclass
class MigrationConstraint:
    """Migration constraint definition"""
    type: str
    description: str
    impact: str
    mitigation: str


@dataclass
class MigrationPhase:
    """Individual migration phase"""
    name: str
    description: str
    duration_hours: int
    dependencies: List[str]
    validation_criteria: List[str]
    rollback_triggers: List[str]
    tasks: List[str]
    risk_level: str
    resources_required: List[str]


@dataclass
class RiskItem:
    """Individual risk assessment item"""
    category: str
    description: str
    probability: str  # low, medium, high
    impact: str  # low, medium, high
    severity: str  # low, medium, high, critical
    mitigation: str
    owner: str


@dataclass
class MigrationPlan:
    """Complete migration plan structure"""
    migration_id: str
    source_system: str
    target_system: str
    migration_type: str
    complexity: str
    estimated_duration_hours: int
    phases: List[MigrationPhase]
    risks: List[RiskItem]
    success_criteria: List[str]
    rollback_plan: Dict[str, Any]
    stakeholders: List[str]
    created_at: str


class MigrationPlanner:
    """Main migration planner class"""
    
    def __init__(self):
        self.migration_patterns = self._load_migration_patterns()
        self.risk_templates = self._load_risk_templates()
        
    def _load_migration_patterns(self) -> Dict[str, Any]:
        """Load predefined migration patterns"""
        return {
            "database": {
                "schema_change": {
                    "phases": ["preparation", "expand", "migrate", "contract", "cleanup"],
                    "base_duration": 24,
                    "complexity_multiplier": {"low": 1.0, "medium": 1.5, "high": 2.5, "critical": 4.0}
                },
                "data_migration": {
                    "phases": ["assessment", "setup", "bulk_copy", "delta_sync", "validation", "cutover"],
                    "base_duration": 48,
                    "complexity_multiplier": {"low": 1.2, "medium": 2.0, "high": 3.0, "critical": 5.0}
                }
            },
            "service": {
                "strangler_fig": {
                    "phases": ["intercept", "implement", "redirect", "validate", "retire"],
                    "base_duration": 168,  # 1 week
                    "complexity_multiplier": {"low": 0.8, "medium": 1.0, "high": 1.8, "critical": 3.0}
                },
                "parallel_run": {
                    "phases": ["setup", "deploy", "shadow", "compare", "cutover", "cleanup"],
                    "base_duration": 72,
                    "complexity_multiplier": {"low": 1.0, "medium": 1.3, "high": 2.0, "critical": 3.5}
                }
            },
            "infrastructure": {
                "cloud_migration": {
                    "phases": ["assessment", "design", "pilot", "migration", "optimization", "decommission"],
                    "base_duration": 720,  # 30 days
                    "complexity_multiplier": {"low": 0.6, "medium": 1.0, "high": 1.5, "critical": 2.5}
                },
                "on_prem_to_cloud": {
                    "phases": ["discovery", "planning", "pilot", "migration", "validation", "cutover"],
                    "base_duration": 480,  # 20 days
                    "complexity_multiplier": {"low": 0.8, "medium": 1.2, "high": 2.0, "critical": 3.0}
                }
            }
        }
    
    def _load_risk_templates(self) -> Dict[str, List[RiskItem]]:
        """Load risk templates for different migration types"""
        return {
            "database": [
                RiskItem("technical", "Data corruption during migration", "low", "critical", "high",
                        "Implement comprehensive backup and validation procedures", "DBA Team"),
                RiskItem("technical", "Extended downtime due to migration complexity", "medium", "high", "high",
                        "Use blue-green deployment and phased migration approach", "DevOps Team"),
                RiskItem("business", "Business process disruption", "medium", "high", "high",
                        "Communicate timeline and provide alternate workflows", "Business Owner"),
                RiskItem("operational", "Insufficient rollback testing", "high", "critical", "critical",
                        "Execute full rollback procedures in staging environment", "QA Team")
            ],
            "service": [
                RiskItem("technical", "Service compatibility issues", "medium", "high", "high",
                        "Implement comprehensive integration testing", "Development Team"),
                RiskItem("technical", "Performance degradation", "medium", "medium", "medium",
                        "Conduct load testing and performance benchmarking", "DevOps Team"),
                RiskItem("business", "Feature parity gaps", "high", "high", "high",
                        "Document feature mapping and acceptance criteria", "Product Owner"),
                RiskItem("operational", "Monitoring gap during transition", "medium", "medium", "medium",
                        "Set up dual monitoring and alerting systems", "SRE Team")
            ],
            "infrastructure": [
                RiskItem("technical", "Network connectivity issues", "medium", "critical", "high",
                        "Implement redundant network paths and monitoring", "Network Team"),
                RiskItem("technical", "Security configuration drift", "high", "high", "high",
                        "Automated security scanning and compliance checks", "Security Team"),
                RiskItem("business", "Cost overrun during transition", "high", "medium", "medium",
                        "Implement cost monitoring and budget alerts", "Finance Team"),
                RiskItem("operational", "Team knowledge gaps", "high", "medium", "medium",
                        "Provide training and create detailed documentation", "Platform Team")
            ]
        }
    
    def _calculate_complexity(self, spec: Dict[str, Any]) -> str:
        """Calculate migration complexity based on specification"""
        complexity_score = 0
        
        # Data volume complexity
        data_volume = spec.get("constraints", {}).get("data_volume_gb", 0)
        if data_volume > 10000:
            complexity_score += 3
        elif data_volume > 1000:
            complexity_score += 2
        elif data_volume > 100:
            complexity_score += 1
        
        # System dependencies
        dependencies = len(spec.get("constraints", {}).get("dependencies", []))
        if dependencies > 10:
            complexity_score += 3
        elif dependencies > 5:
            complexity_score += 2
        elif dependencies > 2:
            complexity_score += 1
        
        # Downtime constraints
        max_downtime = spec.get("constraints", {}).get("max_downtime_minutes", 480)
        if max_downtime < 60:
            complexity_score += 3
        elif max_downtime < 240:
            complexity_score += 2
        elif max_downtime < 480:
            complexity_score += 1
        
        # Special requirements
        special_reqs = spec.get("constraints", {}).get("special_requirements", [])
        complexity_score += len(special_reqs)
        
        if complexity_score >= 8:
            return "critical"
        elif complexity_score >= 5:
            return "high"
        elif complexity_score >= 3:
            return "medium"
        else:
            return "low"
    
    def _estimate_duration(self, migration_type: str, migration_pattern: str, complexity: str) -> int:
        """Estimate migration duration based on type, pattern, and complexity"""
        pattern_info = self.migration_patterns.get(migration_type, {}).get(migration_pattern, {})
        base_duration = pattern_info.get("base_duration", 48)
        multiplier = pattern_info.get("complexity_multiplier", {}).get(complexity, 1.5)
        
        return int(base_duration * multiplier)
    
    def _generate_phases(self, spec: Dict[str, Any]) -> List[MigrationPhase]:
        """Generate migration phases based on specification"""
        migration_type = spec.get("type")
        migration_pattern = spec.get("pattern", "")
        complexity = self._calculate_complexity(spec)
        
        pattern_info = self.migration_patterns.get(migration_type, {})
        if migration_pattern in pattern_info:
            phase_names = pattern_info[migration_pattern]["phases"]
        else:
            # Default phases based on migration type
            phase_names = {
                "database": ["preparation", "migration", "validation", "cutover"],
                "service": ["preparation", "deployment", "testing", "cutover"],
                "infrastructure": ["assessment", "preparation", "migration", "validation"]
            }.get(migration_type, ["preparation", "execution", "validation", "cleanup"])
        
        phases = []
        total_duration = self._estimate_duration(migration_type, migration_pattern, complexity)
        phase_duration = total_duration // len(phase_names)
        
        for i, phase_name in enumerate(phase_names):
            phase = self._create_phase(phase_name, phase_duration, complexity, i, phase_names)
            phases.append(phase)
        
        return phases
    
    def _create_phase(self, phase_name: str, duration: int, complexity: str, 
                     phase_index: int, all_phases: List[str]) -> MigrationPhase:
        """Create a detailed migration phase"""
        phase_templates = {
            "preparation": {
                "description": "Prepare systems and teams for migration",
                "tasks": [
                    "Backup source system",
                    "Set up monitoring and alerting",
                    "Prepare rollback procedures",
                    "Communicate migration timeline",
                    "Validate prerequisites"
                ],
                "validation_criteria": [
                    "All backups completed successfully",
                    "Monitoring systems operational",
                    "Team members briefed and ready",
                    "Rollback procedures tested"
                ],
                "risk_level": "medium"
            },
            "assessment": {
                "description": "Assess current state and migration requirements",
                "tasks": [
                    "Inventory existing systems and dependencies",
                    "Analyze data volumes and complexity",
                    "Identify integration points",
                    "Document current architecture",
                    "Create migration mapping"
                ],
                "validation_criteria": [
                    "Complete system inventory documented",
                    "Dependencies mapped and validated",
                    "Migration scope clearly defined",
                    "Resource requirements identified"
                ],
                "risk_level": "low"
            },
            "migration": {
                "description": "Execute core migration processes",
                "tasks": [
                    "Begin data/service migration",
                    "Monitor migration progress",
                    "Validate data consistency",
                    "Handle migration errors",
                    "Update configuration"
                ],
                "validation_criteria": [
                    "Migration progress within expected parameters",
                    "Data consistency checks passing",
                    "Error rates within acceptable limits",
                    "Performance metrics stable"
                ],
                "risk_level": "high"
            },
            "validation": {
                "description": "Validate migration success and system health",
                "tasks": [
                    "Execute comprehensive testing",
                    "Validate business processes",
                    "Check system performance",
                    "Verify data integrity",
                    "Confirm security controls"
                ],
                "validation_criteria": [
                    "All critical tests passing",
                    "Performance within acceptable range",
                    "Security controls functioning",
                    "Business processes operational"
                ],
                "risk_level": "medium"
            },
            "cutover": {
                "description": "Switch production traffic to new system",
                "tasks": [
                    "Update DNS/load balancer configuration",
                    "Redirect production traffic",
                    "Monitor system performance",
                    "Validate end-user experience",
                    "Confirm business operations"
                ],
                "validation_criteria": [
                    "Traffic successfully redirected",
                    "System performance stable",
                    "User experience satisfactory",
                    "Business operations normal"
                ],
                "risk_level": "critical"
            }
        }
        
        template = phase_templates.get(phase_name, {
            "description": f"Execute {phase_name} phase",
            "tasks": [f"Complete {phase_name} activities"],
            "validation_criteria": [f"{phase_name.title()} phase completed successfully"],
            "risk_level": "medium"
        })
        
        dependencies = []
        if phase_index > 0:
            dependencies.append(all_phases[phase_index - 1])
        
        rollback_triggers = [
            "Critical system failure",
            "Data corruption detected",
            "Performance degradation > 50%",
            "Business process failure"
        ]
        
        resources_required = [
            "Technical team availability",
            "System access and permissions",
            "Monitoring and alerting systems",
            "Communication channels"
        ]
        
        return MigrationPhase(
            name=phase_name,
            description=template["description"],
            duration_hours=duration,
            dependencies=dependencies,
            validation_criteria=template["validation_criteria"],
            rollback_triggers=rollback_triggers,
            tasks=template["tasks"],
            risk_level=template["risk_level"],
            resources_required=resources_required
        )
    
    def _assess_risks(self, spec: Dict[str, Any]) -> List[RiskItem]:
        """Generate risk assessment for migration"""
        migration_type = spec.get("type")
        base_risks = self.risk_templates.get(migration_type, [])
        
        # Add specification-specific risks
        additional_risks = []
        constraints = spec.get("constraints", {})
        
        if constraints.get("max_downtime_minutes", 480) < 60:
            additional_risks.append(
                RiskItem("business", "Zero-downtime requirement increases complexity", "high", "medium", "high",
                        "Implement blue-green deployment or rolling update strategy", "DevOps Team")
            )
        
        if constraints.get("data_volume_gb", 0) > 5000:
            additional_risks.append(
                RiskItem("technical", "Large data volumes may cause extended migration time", "high", "medium", "medium",
                        "Implement parallel processing and progress monitoring", "Data Team")
            )
        
        compliance_reqs = constraints.get("compliance_requirements", [])
        if compliance_reqs:
            additional_risks.append(
                RiskItem("compliance", "Regulatory compliance requirements", "medium", "high", "high",
                        "Ensure all compliance checks are integrated into migration process", "Compliance Team")
            )
        
        return base_risks + additional_risks
    
    def _generate_rollback_plan(self, phases: List[MigrationPhase]) -> Dict[str, Any]:
        """Generate comprehensive rollback plan"""
        rollback_phases = []
        
        for phase in reversed(phases):
            rollback_phase = {
                "phase": phase.name,
                "rollback_actions": [
                    f"Revert {phase.name} changes",
                    f"Restore pre-{phase.name} state",
                    f"Validate {phase.name} rollback success"
                ],
                "validation_criteria": [
                    f"System restored to pre-{phase.name} state",
                    f"All {phase.name} changes successfully reverted",
                    "System functionality confirmed"
                ],
                "estimated_time_minutes": phase.duration_hours * 15  # 25% of original phase time
            }
            rollback_phases.append(rollback_phase)
        
        return {
            "rollback_phases": rollback_phases,
            "rollback_triggers": [
                "Critical system failure",
                "Data corruption detected",
                "Migration timeline exceeded by > 50%",
                "Business-critical functionality unavailable",
                "Security breach detected",
                "Stakeholder decision to abort"
            ],
            "rollback_decision_matrix": {
                "low_severity": "Continue with monitoring",
                "medium_severity": "Assess and decide within 15 minutes",
                "high_severity": "Immediate rollback initiation",
                "critical_severity": "Emergency rollback - all hands"
            },
            "rollback_contacts": [
                "Migration Lead",
                "Technical Lead", 
                "Business Owner",
                "On-call Engineer"
            ]
        }
    
    def generate_plan(self, spec: Dict[str, Any]) -> MigrationPlan:
        """Generate complete migration plan from specification"""
        migration_id = hashlib.md5(json.dumps(spec, sort_keys=True).encode()).hexdigest()[:12]
        complexity = self._calculate_complexity(spec)
        phases = self._generate_phases(spec)
        risks = self._assess_risks(spec)
        total_duration = sum(phase.duration_hours for phase in phases)
        rollback_plan = self._generate_rollback_plan(phases)
        
        success_criteria = [
            "All data successfully migrated with 100% integrity",
            "System performance meets or exceeds baseline",
            "All business processes functioning normally",
            "No critical security vulnerabilities introduced",
            "Stakeholder acceptance criteria met",
            "Documentation and runbooks updated"
        ]
        
        stakeholders = [
            "Business Owner",
            "Technical Lead",
            "DevOps Team",
            "QA Team", 
            "Security Team",
            "End Users"
        ]
        
        return MigrationPlan(
            migration_id=migration_id,
            source_system=spec.get("source", "Unknown"),
            target_system=spec.get("target", "Unknown"),
            migration_type=spec.get("type", "Unknown"),
            complexity=complexity,
            estimated_duration_hours=total_duration,
            phases=phases,
            risks=risks,
            success_criteria=success_criteria,
            rollback_plan=rollback_plan,
            stakeholders=stakeholders,
            created_at=datetime.datetime.now().isoformat()
        )
    
    def generate_human_readable_plan(self, plan: MigrationPlan) -> str:
        """Generate human-readable migration plan"""
        output = []
        output.append("=" * 80)
        output.append(f"MIGRATION PLAN: {plan.migration_id}")
        output.append("=" * 80)
        output.append(f"Source System: {plan.source_system}")
        output.append(f"Target System: {plan.target_system}")
        output.append(f"Migration Type: {plan.migration_type.upper()}")
        output.append(f"Complexity Level: {plan.complexity.upper()}")
        output.append(f"Estimated Duration: {plan.estimated_duration_hours} hours ({plan.estimated_duration_hours/24:.1f} days)")
        output.append(f"Created: {plan.created_at}")
        output.append("")
        
        # Phases
        output.append("MIGRATION PHASES")
        output.append("-" * 40)
        for i, phase in enumerate(plan.phases, 1):
            output.append(f"{i}. {phase.name.upper()} ({phase.duration_hours}h)")
            output.append(f"   Description: {phase.description}")
            output.append(f"   Risk Level: {phase.risk_level.upper()}")
            if phase.dependencies:
                output.append(f"   Dependencies: {', '.join(phase.dependencies)}")
            output.append("   Tasks:")
            for task in phase.tasks:
                output.append(f"     • {task}")
            output.append("   Success Criteria:")
            for criteria in phase.validation_criteria:
                output.append(f"     ✓ {criteria}")
            output.append("")
        
        # Risk Assessment
        output.append("RISK ASSESSMENT")
        output.append("-" * 40)
        risk_by_severity = {}
        for risk in plan.risks:
            if risk.severity not in risk_by_severity:
                risk_by_severity[risk.severity] = []
            risk_by_severity[risk.severity].append(risk)
        
        for severity in ["critical", "high", "medium", "low"]:
            if severity in risk_by_severity:
                output.append(f"{severity.upper()} SEVERITY RISKS:")
                for risk in risk_by_severity[severity]:
                    output.append(f"  • {risk.description}")
                    output.append(f"    Category: {risk.category}")
                    output.append(f"    Probability: {risk.probability} | Impact: {risk.impact}")
                    output.append(f"    Mitigation: {risk.mitigation}")
                    output.append(f"    Owner: {risk.owner}")
                    output.append("")
        
        # Rollback Plan
        output.append("ROLLBACK STRATEGY")
        output.append("-" * 40)
        output.append("Rollback Triggers:")
        for trigger in plan.rollback_plan["rollback_triggers"]:
            output.append(f"  • {trigger}")
        output.append("")
        
        output.append("Rollback Phases:")
        for rb_phase in plan.rollback_plan["rollback_phases"]:
            output.append(f"  {rb_phase['phase'].upper()}:")
            for action in rb_phase["rollback_actions"]:
                output.append(f"    - {action}")
            output.append(f"    Estimated Time: {rb_phase['estimated_time_minutes']} minutes")
            output.append("")
        
        # Success Criteria
        output.append("SUCCESS CRITERIA")
        output.append("-" * 40)
        for criteria in plan.success_criteria:
            output.append(f"✓ {criteria}")
        output.append("")
        
        # Stakeholders
        output.append("STAKEHOLDERS")
        output.append("-" * 40)
        for stakeholder in plan.stakeholders:
            output.append(f"• {stakeholder}")
        output.append("")
        
        return "\n".join(output)


def main():
    """Main function with command line interface"""
    parser = argparse.ArgumentParser(description="Generate comprehensive migration plans")
    parser.add_argument("--input", "-i", required=True, help="Input migration specification file (JSON)")
    parser.add_argument("--output", "-o", help="Output file for migration plan (JSON)")
    parser.add_argument("--format", "-f", choices=["json", "text", "both"], default="both",
                       help="Output format")
    parser.add_argument("--validate", action="store_true", help="Validate migration specification only")
    
    args = parser.parse_args()
    
    try:
        # Load migration specification
        with open(args.input, 'r') as f:
            spec = json.load(f)
        
        # Validate required fields
        required_fields = ["type", "source", "target"]
        for field in required_fields:
            if field not in spec:
                print(f"Error: Missing required field '{field}' in specification", file=sys.stderr)
                return 1
        
        if args.validate:
            print("Migration specification is valid")
            return 0
        
        # Generate migration plan
        planner = MigrationPlanner()
        plan = planner.generate_plan(spec)
        
        # Output results
        if args.format in ["json", "both"]:
            plan_dict = asdict(plan)
            if args.output:
                with open(args.output, 'w') as f:
                    json.dump(plan_dict, f, indent=2)
                print(f"Migration plan saved to {args.output}")
            else:
                print(json.dumps(plan_dict, indent=2))
        
        if args.format in ["text", "both"]:
            human_plan = planner.generate_human_readable_plan(plan)
            text_output = args.output.replace('.json', '.txt') if args.output else None
            if text_output:
                with open(text_output, 'w') as f:
                    f.write(human_plan)
                print(f"Human-readable plan saved to {text_output}")
            else:
                print("\n" + "="*80)
                print("HUMAN-READABLE MIGRATION PLAN")
                print("="*80)
                print(human_plan)
        
    except FileNotFoundError:
        print(f"Error: Input file '{args.input}' not found", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in input file: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())