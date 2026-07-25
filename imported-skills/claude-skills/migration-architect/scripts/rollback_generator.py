#!/usr/bin/env python3
"""
Rollback Generator - Generate comprehensive rollback procedures for migrations

This tool takes a migration plan and generates detailed rollback procedures for each phase,
including data rollback scripts, service rollback steps, validation checks, and communication
templates to ensure safe and reliable migration reversals.

Author: Migration Architect Skill
Version: 1.0.0
License: MIT
"""

import json
import argparse
import sys
import datetime
import hashlib
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from enum import Enum


class RollbackTrigger(Enum):
    """Types of rollback triggers"""
    MANUAL = "manual"
    AUTOMATED = "automated"
    THRESHOLD_BASED = "threshold_based"
    TIME_BASED = "time_based"


class RollbackUrgency(Enum):
    """Rollback urgency levels"""
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    EMERGENCY = "emergency"


@dataclass
class RollbackStep:
    """Individual rollback step"""
    step_id: str
    name: str
    description: str
    script_type: str  # sql, bash, api, manual
    script_content: str
    estimated_duration_minutes: int
    dependencies: List[str]
    validation_commands: List[str]
    success_criteria: List[str]
    failure_escalation: str
    rollback_order: int


@dataclass
class RollbackPhase:
    """Rollback phase containing multiple steps"""
    phase_name: str
    description: str
    urgency_level: str
    estimated_duration_minutes: int
    prerequisites: List[str]
    steps: List[RollbackStep]
    validation_checkpoints: List[str]
    communication_requirements: List[str]
    risk_level: str


@dataclass
class RollbackTriggerCondition:
    """Conditions that trigger automatic rollback"""
    trigger_id: str
    name: str
    condition: str
    metric_threshold: Optional[Dict[str, Any]]
    evaluation_window_minutes: int
    auto_execute: bool
    escalation_contacts: List[str]


@dataclass
class DataRecoveryPlan:
    """Data recovery and restoration plan"""
    recovery_method: str  # backup_restore, point_in_time, event_replay
    backup_location: str
    recovery_scripts: List[str]
    data_validation_queries: List[str]
    estimated_recovery_time_minutes: int
    recovery_dependencies: List[str]


@dataclass
class CommunicationTemplate:
    """Communication template for rollback scenarios"""
    template_type: str  # start, progress, completion, escalation
    audience: str  # technical, business, executive, customers
    subject: str
    body: str
    urgency: str
    delivery_methods: List[str]


@dataclass
class RollbackRunbook:
    """Complete rollback runbook"""
    runbook_id: str
    migration_id: str
    created_at: str
    rollback_phases: List[RollbackPhase]
    trigger_conditions: List[RollbackTriggerCondition]
    data_recovery_plan: DataRecoveryPlan
    communication_templates: List[CommunicationTemplate]
    escalation_matrix: Dict[str, Any]
    validation_checklist: List[str]
    post_rollback_procedures: List[str]
    emergency_contacts: List[Dict[str, str]]


class RollbackGenerator:
    """Main rollback generator class"""
    
    def __init__(self):
        self.rollback_templates = self._load_rollback_templates()
        self.validation_templates = self._load_validation_templates()
        self.communication_templates = self._load_communication_templates()
    
    def _load_rollback_templates(self) -> Dict[str, Any]:
        """Load rollback script templates for different migration types"""
        return {
            "database": {
                "schema_rollback": {
                    "drop_table": "DROP TABLE IF EXISTS {table_name};",
                    "drop_column": "ALTER TABLE {table_name} DROP COLUMN IF EXISTS {column_name};",
                    "restore_column": "ALTER TABLE {table_name} ADD COLUMN {column_definition};",
                    "revert_type": "ALTER TABLE {table_name} ALTER COLUMN {column_name} TYPE {original_type};",
                    "drop_constraint": "ALTER TABLE {table_name} DROP CONSTRAINT {constraint_name};",
                    "add_constraint": "ALTER TABLE {table_name} ADD CONSTRAINT {constraint_name} {constraint_definition};"
                },
                "data_rollback": {
                    "restore_backup": "pg_restore -d {database_name} -c {backup_file}",
                    "point_in_time_recovery": "SELECT pg_create_restore_point('pre_migration_{timestamp}');",
                    "delete_migrated_data": "DELETE FROM {table_name} WHERE migration_batch_id = '{batch_id}';",
                    "restore_original_values": "UPDATE {table_name} SET {column_name} = backup_{column_name} WHERE migration_flag = true;"
                }
            },
            "service": {
                "deployment_rollback": {
                    "rollback_blue_green": "kubectl patch service {service_name} -p '{\"spec\":{\"selector\":{\"version\":\"blue\"}}}'",
                    "rollback_canary": "kubectl scale deployment {service_name}-canary --replicas=0",
                    "restore_previous_version": "kubectl rollout undo deployment/{service_name} --to-revision={revision_number}",
                    "update_load_balancer": "aws elbv2 modify-rule --rule-arn {rule_arn} --actions Type=forward,TargetGroupArn={original_target_group}"
                },
                "configuration_rollback": {
                    "restore_config_map": "kubectl apply -f {original_config_file}",
                    "revert_feature_flags": "curl -X PUT {feature_flag_api}/flags/{flag_name} -d '{\"enabled\": false}'",
                    "restore_environment_vars": "kubectl set env deployment/{deployment_name} {env_var_name}={original_value}"
                }
            },
            "infrastructure": {
                "cloud_rollback": {
                    "revert_terraform": "terraform apply -target={resource_name} {rollback_plan_file}",
                    "restore_dns": "aws route53 change-resource-record-sets --hosted-zone-id {zone_id} --change-batch file://{rollback_dns_changes}",
                    "rollback_security_groups": "aws ec2 authorize-security-group-ingress --group-id {group_id} --protocol {protocol} --port {port} --cidr {cidr}",
                    "restore_iam_policies": "aws iam put-role-policy --role-name {role_name} --policy-name {policy_name} --policy-document file://{original_policy}"
                },
                "network_rollback": {
                    "restore_routing": "aws ec2 replace-route --route-table-id {route_table_id} --destination-cidr-block {cidr} --gateway-id {original_gateway}",
                    "revert_load_balancer": "aws elbv2 modify-load-balancer --load-balancer-arn {lb_arn} --scheme {original_scheme}",
                    "restore_firewall_rules": "aws ec2 revoke-security-group-ingress --group-id {group_id} --protocol {protocol} --port {port} --source-group {source_group}"
                }
            }
        }
    
    def _load_validation_templates(self) -> Dict[str, List[str]]:
        """Load validation command templates"""
        return {
            "database": [
                "SELECT COUNT(*) FROM {table_name};",
                "SELECT COUNT(*) FROM information_schema.tables WHERE table_name = '{table_name}';",
                "SELECT COUNT(*) FROM information_schema.columns WHERE table_name = '{table_name}' AND column_name = '{column_name}';",
                "SELECT COUNT(DISTINCT {primary_key}) FROM {table_name};",
                "SELECT MAX({timestamp_column}) FROM {table_name};"
            ],
            "service": [
                "curl -f {health_check_url}",
                "kubectl get pods -l app={service_name} --field-selector=status.phase=Running",
                "kubectl logs deployment/{service_name} --tail=100 | grep -i error",
                "curl -f {service_endpoint}/api/v1/status"
            ],
            "infrastructure": [
                "aws ec2 describe-instances --instance-ids {instance_id} --query 'Reservations[*].Instances[*].State.Name'",
                "nslookup {domain_name}",
                "curl -I {load_balancer_url}",
                "aws elbv2 describe-target-health --target-group-arn {target_group_arn}"
            ]
        }
    
    def _load_communication_templates(self) -> Dict[str, Dict[str, str]]:
        """Load communication templates"""
        return {
            "rollback_start": {
                "technical": {
                    "subject": "ROLLBACK INITIATED: {migration_name}",
                    "body": """Team,

We have initiated rollback for migration: {migration_name}
Rollback ID: {rollback_id}
Start Time: {start_time}
Estimated Duration: {estimated_duration}

Reason: {rollback_reason}

Current Status: Rolling back phase {current_phase}

Next Updates: Every 15 minutes or upon phase completion

Actions Required:
- Monitor system health dashboards
- Stand by for escalation if needed
- Do not make manual changes during rollback

Incident Commander: {incident_commander}
"""
                },
                "business": {
                    "subject": "System Rollback In Progress - {system_name}",
                    "body": """Business Stakeholders,

We are currently performing a planned rollback of the {system_name} migration due to {rollback_reason}.

Impact: {business_impact}
Expected Resolution: {estimated_completion_time}
Affected Services: {affected_services}

We will provide updates every 30 minutes.

Contact: {business_contact}
"""
                },
                "executive": {
                    "subject": "EXEC ALERT: Critical System Rollback - {system_name}",
                    "body": """Executive Team,

A critical rollback is in progress for {system_name}.

Summary:
- Rollback Reason: {rollback_reason}
- Business Impact: {business_impact}
- Expected Resolution: {estimated_completion_time}
- Customer Impact: {customer_impact}

We are following established procedures and will update hourly.

Escalation: {escalation_contact}
"""
                }
            },
            "rollback_complete": {
                "technical": {
                    "subject": "ROLLBACK COMPLETED: {migration_name}",
                    "body": """Team,

Rollback has been successfully completed for migration: {migration_name}

Summary:
- Start Time: {start_time}
- End Time: {end_time}
- Duration: {actual_duration}
- Phases Completed: {completed_phases}

Validation Results:
{validation_results}

System Status: {system_status}

Next Steps:
- Continue monitoring for 24 hours
- Post-rollback review scheduled for {review_date}
- Root cause analysis to begin

All clear to resume normal operations.

Incident Commander: {incident_commander}
"""
                }
            }
        }
    
    def generate_rollback_runbook(self, migration_plan: Dict[str, Any]) -> RollbackRunbook:
        """Generate comprehensive rollback runbook from migration plan"""
        runbook_id = f"rb_{hashlib.md5(str(migration_plan).encode()).hexdigest()[:8]}"
        migration_id = migration_plan.get("migration_id", "unknown")
        migration_type = migration_plan.get("migration_type", "unknown")
        
        # Generate rollback phases (reverse order of migration phases)
        rollback_phases = self._generate_rollback_phases(migration_plan)
        
        # Generate trigger conditions
        trigger_conditions = self._generate_trigger_conditions(migration_plan)
        
        # Generate data recovery plan
        data_recovery_plan = self._generate_data_recovery_plan(migration_plan)
        
        # Generate communication templates
        communication_templates = self._generate_communication_templates(migration_plan)
        
        # Generate escalation matrix
        escalation_matrix = self._generate_escalation_matrix(migration_plan)
        
        # Generate validation checklist
        validation_checklist = self._generate_validation_checklist(migration_plan)
        
        # Generate post-rollback procedures
        post_rollback_procedures = self._generate_post_rollback_procedures(migration_plan)
        
        # Generate emergency contacts
        emergency_contacts = self._generate_emergency_contacts(migration_plan)
        
        return RollbackRunbook(
            runbook_id=runbook_id,
            migration_id=migration_id,
            created_at=datetime.datetime.now().isoformat(),
            rollback_phases=rollback_phases,
            trigger_conditions=trigger_conditions,
            data_recovery_plan=data_recovery_plan,
            communication_templates=communication_templates,
            escalation_matrix=escalation_matrix,
            validation_checklist=validation_checklist,
            post_rollback_procedures=post_rollback_procedures,
            emergency_contacts=emergency_contacts
        )
    
    def _generate_rollback_phases(self, migration_plan: Dict[str, Any]) -> List[RollbackPhase]:
        """Generate rollback phases from migration plan"""
        migration_phases = migration_plan.get("phases", [])
        migration_type = migration_plan.get("migration_type", "unknown")
        rollback_phases = []
        
        # Reverse the order of migration phases for rollback
        for i, phase in enumerate(reversed(migration_phases)):
            if isinstance(phase, dict):
                phase_name = phase.get("name", f"phase_{i}")
                phase_duration = phase.get("duration_hours", 2) * 60  # Convert to minutes
                phase_risk = phase.get("risk_level", "medium")
            else:
                phase_name = str(phase)
                phase_duration = 120  # Default 2 hours
                phase_risk = "medium"
            
            rollback_steps = self._generate_rollback_steps(phase_name, migration_type, i)
            
            rollback_phase = RollbackPhase(
                phase_name=f"rollback_{phase_name}",
                description=f"Rollback changes made during {phase_name} phase",
                urgency_level=self._calculate_urgency(phase_risk),
                estimated_duration_minutes=phase_duration // 2,  # Rollback typically faster
                prerequisites=self._get_rollback_prerequisites(phase_name, i),
                steps=rollback_steps,
                validation_checkpoints=self._get_validation_checkpoints(phase_name, migration_type),
                communication_requirements=self._get_communication_requirements(phase_name, phase_risk),
                risk_level=phase_risk
            )
            
            rollback_phases.append(rollback_phase)
        
        return rollback_phases
    
    def _generate_rollback_steps(self, phase_name: str, migration_type: str, phase_index: int) -> List[RollbackStep]:
        """Generate specific rollback steps for a phase"""
        steps = []
        templates = self.rollback_templates.get(migration_type, {})
        
        if migration_type == "database":
            if "migration" in phase_name.lower() or "cutover" in phase_name.lower():
                # Data rollback steps
                steps.extend([
                    RollbackStep(
                        step_id=f"rb_data_{phase_index}_01",
                        name="Stop data migration processes",
                        description="Halt all ongoing data migration processes",
                        script_type="sql",
                        script_content="-- Stop migration processes\nSELECT pg_cancel_backend(pid) FROM pg_stat_activity WHERE query LIKE '%migration%';",
                        estimated_duration_minutes=5,
                        dependencies=[],
                        validation_commands=["SELECT COUNT(*) FROM pg_stat_activity WHERE query LIKE '%migration%';"],
                        success_criteria=["No active migration processes"],
                        failure_escalation="Contact DBA immediately",
                        rollback_order=1
                    ),
                    RollbackStep(
                        step_id=f"rb_data_{phase_index}_02",
                        name="Restore from backup",
                        description="Restore database from pre-migration backup",
                        script_type="bash",
                        script_content=templates.get("data_rollback", {}).get("restore_backup", "pg_restore -d {database_name} -c {backup_file}"),
                        estimated_duration_minutes=30,
                        dependencies=[f"rb_data_{phase_index}_01"],
                        validation_commands=["SELECT COUNT(*) FROM information_schema.tables;"],
                        success_criteria=["Database restored successfully", "All expected tables present"],
                        failure_escalation="Escalate to senior DBA and infrastructure team",
                        rollback_order=2
                    )
                ])
            
            if "preparation" in phase_name.lower():
                # Schema rollback steps
                steps.append(
                    RollbackStep(
                        step_id=f"rb_schema_{phase_index}_01",
                        name="Drop migration artifacts",
                        description="Remove temporary migration tables and procedures",
                        script_type="sql",
                        script_content="-- Drop migration artifacts\nDROP TABLE IF EXISTS migration_log;\nDROP PROCEDURE IF EXISTS migrate_data();",
                        estimated_duration_minutes=5,
                        dependencies=[],
                        validation_commands=["SELECT COUNT(*) FROM information_schema.tables WHERE table_name LIKE '%migration%';"],
                        success_criteria=["No migration artifacts remain"],
                        failure_escalation="Manual cleanup required",
                        rollback_order=1
                    )
                )
        
        elif migration_type == "service":
            if "cutover" in phase_name.lower():
                # Service rollback steps
                steps.extend([
                    RollbackStep(
                        step_id=f"rb_service_{phase_index}_01",
                        name="Redirect traffic back to old service",
                        description="Update load balancer to route traffic back to previous service version",
                        script_type="bash",
                        script_content=templates.get("deployment_rollback", {}).get("update_load_balancer", "aws elbv2 modify-rule --rule-arn {rule_arn} --actions Type=forward,TargetGroupArn={original_target_group}"),
                        estimated_duration_minutes=2,
                        dependencies=[],
                        validation_commands=["curl -f {health_check_url}"],
                        success_criteria=["Traffic routing to original service", "Health checks passing"],
                        failure_escalation="Emergency procedure - manual traffic routing",
                        rollback_order=1
                    ),
                    RollbackStep(
                        step_id=f"rb_service_{phase_index}_02",
                        name="Rollback service deployment",
                        description="Revert to previous service deployment version",
                        script_type="bash",
                        script_content=templates.get("deployment_rollback", {}).get("restore_previous_version", "kubectl rollout undo deployment/{service_name} --to-revision={revision_number}"),
                        estimated_duration_minutes=10,
                        dependencies=[f"rb_service_{phase_index}_01"],
                        validation_commands=["kubectl get pods -l app={service_name} --field-selector=status.phase=Running"],
                        success_criteria=["Previous version deployed", "All pods running"],
                        failure_escalation="Manual pod management required",
                        rollback_order=2
                    )
                ])
        
        elif migration_type == "infrastructure":
            steps.extend([
                RollbackStep(
                    step_id=f"rb_infra_{phase_index}_01",
                    name="Revert infrastructure changes",
                    description="Apply terraform plan to revert infrastructure to previous state",
                    script_type="bash",
                    script_content=templates.get("cloud_rollback", {}).get("revert_terraform", "terraform apply -target={resource_name} {rollback_plan_file}"),
                    estimated_duration_minutes=15,
                    dependencies=[],
                    validation_commands=["terraform plan -detailed-exitcode"],
                    success_criteria=["Infrastructure matches previous state", "No planned changes"],
                    failure_escalation="Manual infrastructure review required",
                    rollback_order=1
                ),
                RollbackStep(
                    step_id=f"rb_infra_{phase_index}_02",
                    name="Restore DNS configuration",
                    description="Revert DNS changes to point back to original infrastructure",
                    script_type="bash",
                    script_content=templates.get("cloud_rollback", {}).get("restore_dns", "aws route53 change-resource-record-sets --hosted-zone-id {zone_id} --change-batch file://{rollback_dns_changes}"),
                    estimated_duration_minutes=10,
                    dependencies=[f"rb_infra_{phase_index}_01"],
                    validation_commands=["nslookup {domain_name}"],
                    success_criteria=["DNS resolves to original endpoints"],
                    failure_escalation="Contact DNS administrator",
                    rollback_order=2
                )
            ])
        
        # Add generic validation step for all migration types
        steps.append(
            RollbackStep(
                step_id=f"rb_validate_{phase_index}_final",
                name="Validate rollback completion",
                description=f"Comprehensive validation that {phase_name} rollback completed successfully",
                script_type="manual",
                script_content="Execute validation checklist for this phase",
                estimated_duration_minutes=10,
                dependencies=[step.step_id for step in steps],
                validation_commands=self.validation_templates.get(migration_type, []),
                success_criteria=[f"{phase_name} fully rolled back", "All validation checks pass"],
                failure_escalation=f"Investigate {phase_name} rollback failures",
                rollback_order=99
            )
        )
        
        return steps
    
    def _generate_trigger_conditions(self, migration_plan: Dict[str, Any]) -> List[RollbackTriggerCondition]:
        """Generate automatic rollback trigger conditions"""
        triggers = []
        migration_type = migration_plan.get("migration_type", "unknown")
        
        # Generic triggers for all migration types
        triggers.extend([
            RollbackTriggerCondition(
                trigger_id="error_rate_spike",
                name="Error Rate Spike",
                condition="error_rate > baseline * 5 for 5 minutes",
                metric_threshold={
                    "metric": "error_rate",
                    "operator": "greater_than",
                    "value": "baseline_error_rate * 5",
                    "duration_minutes": 5
                },
                evaluation_window_minutes=5,
                auto_execute=True,
                escalation_contacts=["on_call_engineer", "migration_lead"]
            ),
            RollbackTriggerCondition(
                trigger_id="response_time_degradation",
                name="Response Time Degradation",
                condition="p95_response_time > baseline * 3 for 10 minutes",
                metric_threshold={
                    "metric": "p95_response_time",
                    "operator": "greater_than",
                    "value": "baseline_p95 * 3",
                    "duration_minutes": 10
                },
                evaluation_window_minutes=10,
                auto_execute=False,
                escalation_contacts=["performance_team", "migration_lead"]
            ),
            RollbackTriggerCondition(
                trigger_id="availability_drop",
                name="Service Availability Drop",
                condition="availability < 95% for 2 minutes",
                metric_threshold={
                    "metric": "availability",
                    "operator": "less_than",
                    "value": 0.95,
                    "duration_minutes": 2
                },
                evaluation_window_minutes=2,
                auto_execute=True,
                escalation_contacts=["sre_team", "incident_commander"]
            )
        ])
        
        # Migration-type specific triggers
        if migration_type == "database":
            triggers.extend([
                RollbackTriggerCondition(
                    trigger_id="data_integrity_failure",
                    name="Data Integrity Check Failure",
                    condition="data_validation_failures > 0",
                    metric_threshold={
                        "metric": "data_validation_failures",
                        "operator": "greater_than",
                        "value": 0,
                        "duration_minutes": 1
                    },
                    evaluation_window_minutes=1,
                    auto_execute=True,
                    escalation_contacts=["dba_team", "data_team"]
                ),
                RollbackTriggerCondition(
                    trigger_id="migration_progress_stalled",
                    name="Migration Progress Stalled",
                    condition="migration_progress unchanged for 30 minutes",
                    metric_threshold={
                        "metric": "migration_progress_rate",
                        "operator": "equals",
                        "value": 0,
                        "duration_minutes": 30
                    },
                    evaluation_window_minutes=30,
                    auto_execute=False,
                    escalation_contacts=["migration_team", "dba_team"]
                )
            ])
        
        elif migration_type == "service":
            triggers.extend([
                RollbackTriggerCondition(
                    trigger_id="cpu_utilization_spike",
                    name="CPU Utilization Spike",
                    condition="cpu_utilization > 90% for 15 minutes",
                    metric_threshold={
                        "metric": "cpu_utilization",
                        "operator": "greater_than",
                        "value": 0.90,
                        "duration_minutes": 15
                    },
                    evaluation_window_minutes=15,
                    auto_execute=False,
                    escalation_contacts=["devops_team", "infrastructure_team"]
                ),
                RollbackTriggerCondition(
                    trigger_id="memory_leak_detected",
                    name="Memory Leak Detected",
                    condition="memory_usage increasing continuously for 20 minutes",
                    metric_threshold={
                        "metric": "memory_growth_rate",
                        "operator": "greater_than",
                        "value": "1MB/minute",
                        "duration_minutes": 20
                    },
                    evaluation_window_minutes=20,
                    auto_execute=True,
                    escalation_contacts=["development_team", "sre_team"]
                )
            ])
        
        return triggers
    
    def _generate_data_recovery_plan(self, migration_plan: Dict[str, Any]) -> DataRecoveryPlan:
        """Generate data recovery plan"""
        migration_type = migration_plan.get("migration_type", "unknown")
        
        if migration_type == "database":
            return DataRecoveryPlan(
                recovery_method="point_in_time",
                backup_location="/backups/pre_migration_{migration_id}_{timestamp}.sql",
                recovery_scripts=[
                    "pg_restore -d production -c /backups/pre_migration_backup.sql",
                    "SELECT pg_create_restore_point('rollback_point');",
                    "VACUUM ANALYZE; -- Refresh statistics after restore"
                ],
                data_validation_queries=[
                    "SELECT COUNT(*) FROM critical_business_table;",
                    "SELECT MAX(created_at) FROM audit_log;",
                    "SELECT COUNT(DISTINCT user_id) FROM user_sessions;",
                    "SELECT SUM(amount) FROM financial_transactions WHERE date = CURRENT_DATE;"
                ],
                estimated_recovery_time_minutes=45,
                recovery_dependencies=["database_instance_running", "backup_file_accessible"]
            )
        else:
            return DataRecoveryPlan(
                recovery_method="backup_restore",
                backup_location="/backups/pre_migration_state",
                recovery_scripts=[
                    "# Restore configuration files from backup",
                    "cp -r /backups/pre_migration_state/config/* /app/config/",
                    "# Restart services with previous configuration",
                    "systemctl restart application_service"
                ],
                data_validation_queries=[
                    "curl -f http://localhost:8080/health",
                    "curl -f http://localhost:8080/api/status"
                ],
                estimated_recovery_time_minutes=20,
                recovery_dependencies=["service_stopped", "backup_accessible"]
            )
    
    def _generate_communication_templates(self, migration_plan: Dict[str, Any]) -> List[CommunicationTemplate]:
        """Generate communication templates for rollback scenarios"""
        templates = []
        base_templates = self.communication_templates
        
        # Rollback start notifications
        for audience in ["technical", "business", "executive"]:
            if audience in base_templates["rollback_start"]:
                template_data = base_templates["rollback_start"][audience]
                templates.append(CommunicationTemplate(
                    template_type="rollback_start",
                    audience=audience,
                    subject=template_data["subject"],
                    body=template_data["body"],
                    urgency="high" if audience == "executive" else "medium",
                    delivery_methods=["email", "slack"] if audience == "technical" else ["email"]
                ))
        
        # Rollback completion notifications
        for audience in ["technical", "business"]:
            if audience in base_templates.get("rollback_complete", {}):
                template_data = base_templates["rollback_complete"][audience]
                templates.append(CommunicationTemplate(
                    template_type="rollback_complete",
                    audience=audience,
                    subject=template_data["subject"],
                    body=template_data["body"],
                    urgency="medium",
                    delivery_methods=["email", "slack"] if audience == "technical" else ["email"]
                ))
        
        # Emergency escalation template
        templates.append(CommunicationTemplate(
            template_type="emergency_escalation",
            audience="executive",
            subject="CRITICAL: Rollback Emergency - {migration_name}",
            body="""CRITICAL SITUATION - IMMEDIATE ATTENTION REQUIRED

Migration: {migration_name}
Issue: Rollback procedure has encountered critical failures

Current Status: {current_status}
Failed Components: {failed_components}
Business Impact: {business_impact}
Customer Impact: {customer_impact}

Immediate Actions:
1. Emergency response team activated
2. {emergency_action_1}
3. {emergency_action_2}

War Room: {war_room_location}
Bridge Line: {conference_bridge}

Next Update: {next_update_time}

Incident Commander: {incident_commander}
Executive On-Call: {executive_on_call}
""",
            urgency="emergency",
            delivery_methods=["email", "sms", "phone_call"]
        ))
        
        return templates
    
    def _generate_escalation_matrix(self, migration_plan: Dict[str, Any]) -> Dict[str, Any]:
        """Generate escalation matrix for different failure scenarios"""
        return {
            "level_1": {
                "trigger": "Single component failure",
                "response_time_minutes": 5,
                "contacts": ["on_call_engineer", "migration_lead"],
                "actions": ["Investigate issue", "Attempt automated remediation", "Monitor closely"]
            },
            "level_2": {
                "trigger": "Multiple component failures or single critical failure",
                "response_time_minutes": 2,
                "contacts": ["senior_engineer", "team_lead", "devops_lead"],
                "actions": ["Initiate rollback", "Establish war room", "Notify stakeholders"]
            },
            "level_3": {
                "trigger": "System-wide failure or data corruption",
                "response_time_minutes": 1,
                "contacts": ["engineering_manager", "cto", "incident_commander"],
                "actions": ["Emergency rollback", "All hands on deck", "Executive notification"]
            },
            "emergency": {
                "trigger": "Business-critical failure with customer impact",
                "response_time_minutes": 0,
                "contacts": ["ceo", "cto", "head_of_operations"],
                "actions": ["Emergency procedures", "Customer communication", "Media preparation if needed"]
            }
        }
    
    def _generate_validation_checklist(self, migration_plan: Dict[str, Any]) -> List[str]:
        """Generate comprehensive validation checklist"""
        migration_type = migration_plan.get("migration_type", "unknown")
        
        base_checklist = [
            "Verify system is responding to health checks",
            "Confirm error rates are within normal parameters",
            "Validate response times meet SLA requirements",
            "Check all critical business processes are functioning",
            "Verify monitoring and alerting systems are operational",
            "Confirm no data corruption has occurred",
            "Validate security controls are functioning properly",
            "Check backup systems are working correctly",
            "Verify integration points with downstream systems",
            "Confirm user authentication and authorization working"
        ]
        
        if migration_type == "database":
            base_checklist.extend([
                "Validate database schema matches expected state",
                "Confirm referential integrity constraints",
                "Check database performance metrics",
                "Verify data consistency across related tables",
                "Validate indexes and statistics are optimal",
                "Confirm transaction logs are clean",
                "Check database connections and connection pooling"
            ])
        
        elif migration_type == "service":
            base_checklist.extend([
                "Verify service discovery is working correctly",
                "Confirm load balancing is distributing traffic properly",
                "Check service-to-service communication",
                "Validate API endpoints are responding correctly",
                "Confirm feature flags are in correct state",
                "Check resource utilization (CPU, memory, disk)",
                "Verify container orchestration is healthy"
            ])
        
        elif migration_type == "infrastructure":
            base_checklist.extend([
                "Verify network connectivity between components",
                "Confirm DNS resolution is working correctly",
                "Check firewall rules and security groups",
                "Validate load balancer configuration",
                "Confirm SSL/TLS certificates are valid",
                "Check storage systems are accessible",
                "Verify backup and disaster recovery systems"
            ])
        
        return base_checklist
    
    def _generate_post_rollback_procedures(self, migration_plan: Dict[str, Any]) -> List[str]:
        """Generate post-rollback procedures"""
        return [
            "Monitor system stability for 24-48 hours post-rollback",
            "Conduct thorough post-rollback testing of all critical paths",
            "Review and analyze rollback metrics and timing",
            "Document lessons learned and rollback procedure improvements",
            "Schedule post-mortem meeting with all stakeholders",
            "Update rollback procedures based on actual experience",
            "Communicate rollback completion to all stakeholders",
            "Archive rollback logs and artifacts for future reference",
            "Review and update monitoring thresholds if needed",
            "Plan for next migration attempt with improved procedures",
            "Conduct security review to ensure no vulnerabilities introduced",
            "Update disaster recovery procedures if affected by rollback",
            "Review capacity planning based on rollback resource usage",
            "Update documentation with rollback experience and timings"
        ]
    
    def _generate_emergency_contacts(self, migration_plan: Dict[str, Any]) -> List[Dict[str, str]]:
        """Generate emergency contact list"""
        return [
            {
                "role": "Incident Commander",
                "name": "TBD - Assigned during migration",
                "primary_phone": "+1-XXX-XXX-XXXX",
                "email": "incident.commander@company.com",
                "backup_contact": "backup.commander@company.com"
            },
            {
                "role": "Technical Lead",
                "name": "TBD - Migration technical owner",
                "primary_phone": "+1-XXX-XXX-XXXX",
                "email": "tech.lead@company.com",
                "backup_contact": "senior.engineer@company.com"
            },
            {
                "role": "Business Owner",
                "name": "TBD - Business stakeholder",
                "primary_phone": "+1-XXX-XXX-XXXX",
                "email": "business.owner@company.com",
                "backup_contact": "product.manager@company.com"
            },
            {
                "role": "On-Call Engineer",
                "name": "Current on-call rotation",
                "primary_phone": "+1-XXX-XXX-XXXX",
                "email": "oncall@company.com",
                "backup_contact": "backup.oncall@company.com"
            },
            {
                "role": "Executive Escalation",
                "name": "CTO/VP Engineering",
                "primary_phone": "+1-XXX-XXX-XXXX",
                "email": "cto@company.com",
                "backup_contact": "vp.engineering@company.com"
            }
        ]
    
    def _calculate_urgency(self, risk_level: str) -> str:
        """Calculate rollback urgency based on risk level"""
        risk_to_urgency = {
            "low": "low",
            "medium": "medium", 
            "high": "high",
            "critical": "emergency"
        }
        return risk_to_urgency.get(risk_level, "medium")
    
    def _get_rollback_prerequisites(self, phase_name: str, phase_index: int) -> List[str]:
        """Get prerequisites for rollback phase"""
        prerequisites = [
            "Incident commander assigned and briefed",
            "All team members notified of rollback initiation",
            "Monitoring systems confirmed operational",
            "Backup systems verified and accessible"
        ]
        
        if phase_index > 0:
            prerequisites.append("Previous rollback phase completed successfully")
        
        if "cutover" in phase_name.lower():
            prerequisites.extend([
                "Traffic redirection capabilities confirmed",
                "Load balancer configuration backed up",
                "DNS changes prepared for quick execution"
            ])
        
        if "data" in phase_name.lower() or "migration" in phase_name.lower():
            prerequisites.extend([
                "Database backup verified and accessible",
                "Data validation queries prepared",
                "Database administrator on standby"
            ])
        
        return prerequisites
    
    def _get_validation_checkpoints(self, phase_name: str, migration_type: str) -> List[str]:
        """Get validation checkpoints for rollback phase"""
        checkpoints = [
            f"{phase_name} rollback steps completed",
            "System health checks passing",
            "No critical errors in logs",
            "Key metrics within acceptable ranges"
        ]
        
        validation_commands = self.validation_templates.get(migration_type, [])
        checkpoints.extend([f"Validation command passed: {cmd[:50]}..." for cmd in validation_commands[:3]])
        
        return checkpoints
    
    def _get_communication_requirements(self, phase_name: str, risk_level: str) -> List[str]:
        """Get communication requirements for rollback phase"""
        base_requirements = [
            "Notify incident commander of phase start/completion",
            "Update rollback status dashboard",
            "Log all actions and decisions"
        ]
        
        if risk_level in ["high", "critical"]:
            base_requirements.extend([
                "Notify all stakeholders of phase progress",
                "Update executive team if rollback extends beyond expected time",
                "Prepare customer communication if needed"
            ])
        
        if "cutover" in phase_name.lower():
            base_requirements.append("Immediate notification when traffic is redirected")
        
        return base_requirements
    
    def generate_human_readable_runbook(self, runbook: RollbackRunbook) -> str:
        """Generate human-readable rollback runbook"""
        output = []
        output.append("=" * 80)
        output.append(f"ROLLBACK RUNBOOK: {runbook.runbook_id}")
        output.append("=" * 80)
        output.append(f"Migration ID: {runbook.migration_id}")
        output.append(f"Created: {runbook.created_at}")
        output.append("")
        
        # Emergency Contacts
        output.append("EMERGENCY CONTACTS")
        output.append("-" * 40)
        for contact in runbook.emergency_contacts:
            output.append(f"{contact['role']}: {contact['name']}")
            output.append(f"  Phone: {contact['primary_phone']}")
            output.append(f"  Email: {contact['email']}")
            output.append(f"  Backup: {contact['backup_contact']}")
            output.append("")
        
        # Escalation Matrix
        output.append("ESCALATION MATRIX")
        output.append("-" * 40)
        for level, details in runbook.escalation_matrix.items():
            output.append(f"{level.upper()}:")
            output.append(f"  Trigger: {details['trigger']}")
            output.append(f"  Response Time: {details['response_time_minutes']} minutes")
            output.append(f"  Contacts: {', '.join(details['contacts'])}")
            output.append(f"  Actions: {', '.join(details['actions'])}")
            output.append("")
        
        # Rollback Trigger Conditions
        output.append("AUTOMATIC ROLLBACK TRIGGERS")
        output.append("-" * 40)
        for trigger in runbook.trigger_conditions:
            output.append(f"• {trigger.name}")
            output.append(f"  Condition: {trigger.condition}")
            output.append(f"  Auto-Execute: {'Yes' if trigger.auto_execute else 'No'}")
            output.append(f"  Evaluation Window: {trigger.evaluation_window_minutes} minutes")
            output.append(f"  Contacts: {', '.join(trigger.escalation_contacts)}")
            output.append("")
        
        # Rollback Phases
        output.append("ROLLBACK PHASES")
        output.append("-" * 40)
        for i, phase in enumerate(runbook.rollback_phases, 1):
            output.append(f"{i}. {phase.phase_name.upper()}")
            output.append(f"   Description: {phase.description}")
            output.append(f"   Urgency: {phase.urgency_level.upper()}")
            output.append(f"   Duration: {phase.estimated_duration_minutes} minutes")
            output.append(f"   Risk Level: {phase.risk_level.upper()}")
            
            if phase.prerequisites:
                output.append("   Prerequisites:")
                for prereq in phase.prerequisites:
                    output.append(f"     ✓ {prereq}")
            
            output.append("   Steps:")
            for step in sorted(phase.steps, key=lambda x: x.rollback_order):
                output.append(f"     {step.rollback_order}. {step.name}")
                output.append(f"        Duration: {step.estimated_duration_minutes} min")
                output.append(f"        Type: {step.script_type}")
                if step.script_content and step.script_type != "manual":
                    output.append("        Script:")
                    for line in step.script_content.split('\n')[:3]:  # Show first 3 lines
                        output.append(f"          {line}")
                    if len(step.script_content.split('\n')) > 3:
                        output.append("          ...")
                output.append(f"        Success Criteria: {', '.join(step.success_criteria)}")
                output.append("")
            
            if phase.validation_checkpoints:
                output.append("   Validation Checkpoints:")
                for checkpoint in phase.validation_checkpoints:
                    output.append(f"     ☐ {checkpoint}")
            output.append("")
        
        # Data Recovery Plan
        output.append("DATA RECOVERY PLAN")
        output.append("-" * 40)
        drp = runbook.data_recovery_plan
        output.append(f"Recovery Method: {drp.recovery_method}")
        output.append(f"Backup Location: {drp.backup_location}")
        output.append(f"Estimated Recovery Time: {drp.estimated_recovery_time_minutes} minutes")
        output.append("Recovery Scripts:")
        for script in drp.recovery_scripts:
            output.append(f"  • {script}")
        output.append("Validation Queries:")
        for query in drp.data_validation_queries:
            output.append(f"  • {query}")
        output.append("")
        
        # Validation Checklist
        output.append("POST-ROLLBACK VALIDATION CHECKLIST")
        output.append("-" * 40)
        for i, item in enumerate(runbook.validation_checklist, 1):
            output.append(f"{i:2d}. ☐ {item}")
        output.append("")
        
        # Post-Rollback Procedures
        output.append("POST-ROLLBACK PROCEDURES")
        output.append("-" * 40)
        for i, procedure in enumerate(runbook.post_rollback_procedures, 1):
            output.append(f"{i:2d}. {procedure}")
        output.append("")
        
        return "\n".join(output)


def main():
    """Main function with command line interface"""
    parser = argparse.ArgumentParser(description="Generate comprehensive rollback runbooks from migration plans")
    parser.add_argument("--input", "-i", required=True, help="Input migration plan file (JSON)")
    parser.add_argument("--output", "-o", help="Output file for rollback runbook (JSON)")
    parser.add_argument("--format", "-f", choices=["json", "text", "both"], default="both", help="Output format")
    
    args = parser.parse_args()
    
    try:
        # Load migration plan
        with open(args.input, 'r') as f:
            migration_plan = json.load(f)
        
        # Validate required fields
        if "migration_id" not in migration_plan and "source" not in migration_plan:
            print("Error: Migration plan must contain migration_id or source field", file=sys.stderr)
            return 1
        
        # Generate rollback runbook
        generator = RollbackGenerator()
        runbook = generator.generate_rollback_runbook(migration_plan)
        
        # Output results
        if args.format in ["json", "both"]:
            runbook_dict = asdict(runbook)
            if args.output:
                with open(args.output, 'w') as f:
                    json.dump(runbook_dict, f, indent=2)
                print(f"Rollback runbook saved to {args.output}")
            else:
                print(json.dumps(runbook_dict, indent=2))
        
        if args.format in ["text", "both"]:
            human_runbook = generator.generate_human_readable_runbook(runbook)
            text_output = args.output.replace('.json', '.txt') if args.output else None
            if text_output:
                with open(text_output, 'w') as f:
                    f.write(human_runbook)
                print(f"Human-readable runbook saved to {text_output}")
            else:
                print("\n" + "="*80)
                print("HUMAN-READABLE ROLLBACK RUNBOOK")
                print("="*80)
                print(human_runbook)
        
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