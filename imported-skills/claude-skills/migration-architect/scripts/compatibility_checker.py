#!/usr/bin/env python3
"""
Compatibility Checker - Analyze schema and API compatibility between versions

This tool analyzes schema and API changes between versions and identifies backward
compatibility issues including breaking changes, data type mismatches, missing fields,
constraint violations, and generates migration scripts suggestions.

Author: Migration Architect Skill
Version: 1.0.0
License: MIT
"""

import json
import argparse
import sys
import re
import datetime
from typing import Dict, List, Any, Optional, Tuple, Set
from dataclasses import dataclass, asdict
from enum import Enum


class ChangeType(Enum):
    """Types of changes detected"""
    BREAKING = "breaking"
    POTENTIALLY_BREAKING = "potentially_breaking"
    NON_BREAKING = "non_breaking"
    ADDITIVE = "additive"


class CompatibilityLevel(Enum):
    """Compatibility assessment levels"""
    FULLY_COMPATIBLE = "fully_compatible"
    BACKWARD_COMPATIBLE = "backward_compatible"
    POTENTIALLY_INCOMPATIBLE = "potentially_incompatible"
    BREAKING_CHANGES = "breaking_changes"


@dataclass
class CompatibilityIssue:
    """Individual compatibility issue"""
    type: str
    severity: str
    description: str
    field_path: str
    old_value: Any
    new_value: Any
    impact: str
    suggested_migration: str
    affected_operations: List[str]


@dataclass
class MigrationScript:
    """Migration script suggestion"""
    script_type: str  # sql, api, config
    description: str
    script_content: str
    rollback_script: str
    dependencies: List[str]
    validation_query: str


@dataclass
class CompatibilityReport:
    """Complete compatibility analysis report"""
    schema_before: str
    schema_after: str
    analysis_date: str
    overall_compatibility: str
    breaking_changes_count: int
    potentially_breaking_count: int
    non_breaking_changes_count: int
    additive_changes_count: int
    issues: List[CompatibilityIssue]
    migration_scripts: List[MigrationScript]
    risk_assessment: Dict[str, Any]
    recommendations: List[str]


class SchemaCompatibilityChecker:
    """Main schema compatibility checker class"""
    
    def __init__(self):
        self.type_compatibility_matrix = self._build_type_compatibility_matrix()
        self.constraint_implications = self._build_constraint_implications()
    
    def _build_type_compatibility_matrix(self) -> Dict[str, Dict[str, str]]:
        """Build data type compatibility matrix"""
        return {
            # SQL data types compatibility
            "varchar": {
                "text": "compatible",
                "char": "potentially_breaking",  # length might be different
                "nvarchar": "compatible",
                "int": "breaking",
                "bigint": "breaking",
                "decimal": "breaking",
                "datetime": "breaking",
                "boolean": "breaking"
            },
            "int": {
                "bigint": "compatible",
                "smallint": "potentially_breaking",  # range reduction
                "decimal": "compatible",
                "float": "potentially_breaking",  # precision loss
                "varchar": "breaking",
                "boolean": "breaking"
            },
            "bigint": {
                "int": "potentially_breaking",  # range reduction
                "decimal": "compatible",
                "varchar": "breaking",
                "boolean": "breaking"
            },
            "decimal": {
                "float": "potentially_breaking",  # precision loss
                "int": "potentially_breaking",  # precision loss
                "bigint": "potentially_breaking",  # precision loss
                "varchar": "breaking",
                "boolean": "breaking"
            },
            "datetime": {
                "timestamp": "compatible",
                "date": "potentially_breaking",  # time component lost
                "varchar": "breaking",
                "int": "breaking"
            },
            "boolean": {
                "tinyint": "compatible",
                "varchar": "breaking",
                "int": "breaking"
            },
            # JSON/API field types
            "string": {
                "number": "breaking",
                "boolean": "breaking",
                "array": "breaking",
                "object": "breaking",
                "null": "potentially_breaking"
            },
            "number": {
                "string": "breaking",
                "boolean": "breaking",
                "array": "breaking",
                "object": "breaking",
                "null": "potentially_breaking"
            },
            "boolean": {
                "string": "breaking",
                "number": "breaking",
                "array": "breaking",
                "object": "breaking",
                "null": "potentially_breaking"
            },
            "array": {
                "string": "breaking",
                "number": "breaking",
                "boolean": "breaking",
                "object": "breaking",
                "null": "potentially_breaking"
            },
            "object": {
                "string": "breaking",
                "number": "breaking",
                "boolean": "breaking",
                "array": "breaking",
                "null": "potentially_breaking"
            }
        }
    
    def _build_constraint_implications(self) -> Dict[str, Dict[str, str]]:
        """Build constraint change implications"""
        return {
            "required": {
                "added": "breaking",  # Previously optional field now required
                "removed": "non_breaking"  # Previously required field now optional
            },
            "not_null": {
                "added": "breaking",  # Previously nullable now NOT NULL
                "removed": "non_breaking"  # Previously NOT NULL now nullable
            },
            "unique": {
                "added": "potentially_breaking",  # May fail if duplicates exist
                "removed": "non_breaking"  # No longer enforcing uniqueness
            },
            "primary_key": {
                "added": "breaking",  # Major structural change
                "removed": "breaking",  # Major structural change
                "modified": "breaking"  # Primary key change is always breaking
            },
            "foreign_key": {
                "added": "potentially_breaking",  # May fail if referential integrity violated
                "removed": "potentially_breaking",  # May allow orphaned records
                "modified": "breaking"  # Reference change is breaking
            },
            "check": {
                "added": "potentially_breaking",  # May fail if existing data violates check
                "removed": "non_breaking",  # No longer enforcing check
                "modified": "potentially_breaking"  # Different validation rules
            },
            "index": {
                "added": "non_breaking",  # Performance improvement
                "removed": "non_breaking",  # Performance impact only
                "modified": "non_breaking"  # Performance impact only
            }
        }
    
    def analyze_database_schema(self, before_schema: Dict[str, Any], 
                              after_schema: Dict[str, Any]) -> CompatibilityReport:
        """Analyze database schema compatibility"""
        issues = []
        migration_scripts = []
        
        before_tables = before_schema.get("tables", {})
        after_tables = after_schema.get("tables", {})
        
        # Check for removed tables
        for table_name in before_tables:
            if table_name not in after_tables:
                issues.append(CompatibilityIssue(
                    type="table_removed",
                    severity="breaking",
                    description=f"Table '{table_name}' has been removed",
                    field_path=f"tables.{table_name}",
                    old_value=before_tables[table_name],
                    new_value=None,
                    impact="All operations on this table will fail",
                    suggested_migration=f"CREATE VIEW {table_name} AS SELECT * FROM replacement_table;",
                    affected_operations=["SELECT", "INSERT", "UPDATE", "DELETE"]
                ))
        
        # Check for added tables
        for table_name in after_tables:
            if table_name not in before_tables:
                migration_scripts.append(MigrationScript(
                    script_type="sql",
                    description=f"Create new table {table_name}",
                    script_content=self._generate_create_table_sql(table_name, after_tables[table_name]),
                    rollback_script=f"DROP TABLE IF EXISTS {table_name};",
                    dependencies=[],
                    validation_query=f"SELECT COUNT(*) FROM information_schema.tables WHERE table_name = '{table_name}';"
                ))
        
        # Check for modified tables
        for table_name in set(before_tables.keys()) & set(after_tables.keys()):
            table_issues, table_scripts = self._analyze_table_changes(
                table_name, before_tables[table_name], after_tables[table_name]
            )
            issues.extend(table_issues)
            migration_scripts.extend(table_scripts)
        
        return self._build_compatibility_report(
            before_schema, after_schema, issues, migration_scripts
        )
    
    def analyze_api_schema(self, before_schema: Dict[str, Any], 
                          after_schema: Dict[str, Any]) -> CompatibilityReport:
        """Analyze REST API schema compatibility"""
        issues = []
        migration_scripts = []
        
        # Analyze endpoints
        before_paths = before_schema.get("paths", {})
        after_paths = after_schema.get("paths", {})
        
        # Check for removed endpoints
        for path in before_paths:
            if path not in after_paths:
                for method in before_paths[path]:
                    issues.append(CompatibilityIssue(
                        type="endpoint_removed",
                        severity="breaking",
                        description=f"Endpoint {method.upper()} {path} has been removed",
                        field_path=f"paths.{path}.{method}",
                        old_value=before_paths[path][method],
                        new_value=None,
                        impact="Client requests to this endpoint will fail with 404",
                        suggested_migration=f"Implement redirect to replacement endpoint or maintain backward compatibility stub",
                        affected_operations=[f"{method.upper()} {path}"]
                    ))
        
        # Check for modified endpoints
        for path in set(before_paths.keys()) & set(after_paths.keys()):
            path_issues, path_scripts = self._analyze_endpoint_changes(
                path, before_paths[path], after_paths[path]
            )
            issues.extend(path_issues)
            migration_scripts.extend(path_scripts)
        
        # Analyze data models
        before_components = before_schema.get("components", {}).get("schemas", {})
        after_components = after_schema.get("components", {}).get("schemas", {})
        
        for model_name in set(before_components.keys()) & set(after_components.keys()):
            model_issues, model_scripts = self._analyze_model_changes(
                model_name, before_components[model_name], after_components[model_name]
            )
            issues.extend(model_issues)
            migration_scripts.extend(model_scripts)
        
        return self._build_compatibility_report(
            before_schema, after_schema, issues, migration_scripts
        )
    
    def _analyze_table_changes(self, table_name: str, before_table: Dict[str, Any], 
                             after_table: Dict[str, Any]) -> Tuple[List[CompatibilityIssue], List[MigrationScript]]:
        """Analyze changes to a specific table"""
        issues = []
        scripts = []
        
        before_columns = before_table.get("columns", {})
        after_columns = after_table.get("columns", {})
        
        # Check for removed columns
        for col_name in before_columns:
            if col_name not in after_columns:
                issues.append(CompatibilityIssue(
                    type="column_removed",
                    severity="breaking",
                    description=f"Column '{col_name}' removed from table '{table_name}'",
                    field_path=f"tables.{table_name}.columns.{col_name}",
                    old_value=before_columns[col_name],
                    new_value=None,
                    impact="SELECT statements including this column will fail",
                    suggested_migration=f"ALTER TABLE {table_name} ADD COLUMN {col_name}_deprecated AS computed_value;",
                    affected_operations=["SELECT", "INSERT", "UPDATE"]
                ))
        
        # Check for added columns
        for col_name in after_columns:
            if col_name not in before_columns:
                col_def = after_columns[col_name]
                is_required = col_def.get("nullable", True) == False and col_def.get("default") is None
                
                if is_required:
                    issues.append(CompatibilityIssue(
                        type="required_column_added",
                        severity="breaking",
                        description=f"Required column '{col_name}' added to table '{table_name}'",
                        field_path=f"tables.{table_name}.columns.{col_name}",
                        old_value=None,
                        new_value=col_def,
                        impact="INSERT statements without this column will fail",
                        suggested_migration=f"Add default value or make column nullable initially",
                        affected_operations=["INSERT"]
                    ))
                
                scripts.append(MigrationScript(
                    script_type="sql",
                    description=f"Add column {col_name} to table {table_name}",
                    script_content=f"ALTER TABLE {table_name} ADD COLUMN {self._generate_column_definition(col_name, col_def)};",
                    rollback_script=f"ALTER TABLE {table_name} DROP COLUMN {col_name};",
                    dependencies=[],
                    validation_query=f"SELECT COUNT(*) FROM information_schema.columns WHERE table_name = '{table_name}' AND column_name = '{col_name}';"
                ))
        
        # Check for modified columns
        for col_name in set(before_columns.keys()) & set(after_columns.keys()):
            col_issues, col_scripts = self._analyze_column_changes(
                table_name, col_name, before_columns[col_name], after_columns[col_name]
            )
            issues.extend(col_issues)
            scripts.extend(col_scripts)
        
        # Check constraint changes
        before_constraints = before_table.get("constraints", {})
        after_constraints = after_table.get("constraints", {})
        
        constraint_issues, constraint_scripts = self._analyze_constraint_changes(
            table_name, before_constraints, after_constraints
        )
        issues.extend(constraint_issues)
        scripts.extend(constraint_scripts)
        
        return issues, scripts
    
    def _analyze_column_changes(self, table_name: str, col_name: str, 
                              before_col: Dict[str, Any], after_col: Dict[str, Any]) -> Tuple[List[CompatibilityIssue], List[MigrationScript]]:
        """Analyze changes to a specific column"""
        issues = []
        scripts = []
        
        # Check data type changes
        before_type = before_col.get("type", "").lower()
        after_type = after_col.get("type", "").lower()
        
        if before_type != after_type:
            compatibility = self.type_compatibility_matrix.get(before_type, {}).get(after_type, "breaking")
            
            if compatibility == "breaking":
                issues.append(CompatibilityIssue(
                    type="incompatible_type_change",
                    severity="breaking",
                    description=f"Column '{col_name}' type changed from {before_type} to {after_type}",
                    field_path=f"tables.{table_name}.columns.{col_name}.type",
                    old_value=before_type,
                    new_value=after_type,
                    impact="Data conversion may fail or lose precision",
                    suggested_migration=f"Add conversion logic and validate data integrity",
                    affected_operations=["SELECT", "INSERT", "UPDATE", "WHERE clauses"]
                ))
                
                scripts.append(MigrationScript(
                    script_type="sql",
                    description=f"Convert column {col_name} from {before_type} to {after_type}",
                    script_content=f"ALTER TABLE {table_name} ALTER COLUMN {col_name} TYPE {after_type} USING {col_name}::{after_type};",
                    rollback_script=f"ALTER TABLE {table_name} ALTER COLUMN {col_name} TYPE {before_type};",
                    dependencies=[f"backup_{table_name}"],
                    validation_query=f"SELECT COUNT(*) FROM {table_name} WHERE {col_name} IS NOT NULL;"
                ))
            
            elif compatibility == "potentially_breaking":
                issues.append(CompatibilityIssue(
                    type="risky_type_change",
                    severity="potentially_breaking",
                    description=f"Column '{col_name}' type changed from {before_type} to {after_type} - may lose data",
                    field_path=f"tables.{table_name}.columns.{col_name}.type",
                    old_value=before_type,
                    new_value=after_type,
                    impact="Potential data loss or precision reduction",
                    suggested_migration=f"Validate all existing data can be converted safely",
                    affected_operations=["Data integrity"]
                ))
        
        # Check nullability changes
        before_nullable = before_col.get("nullable", True)
        after_nullable = after_col.get("nullable", True)
        
        if before_nullable != after_nullable:
            if before_nullable and not after_nullable:  # null -> not null
                issues.append(CompatibilityIssue(
                    type="nullability_restriction",
                    severity="breaking",
                    description=f"Column '{col_name}' changed from nullable to NOT NULL",
                    field_path=f"tables.{table_name}.columns.{col_name}.nullable",
                    old_value=before_nullable,
                    new_value=after_nullable,
                    impact="Existing NULL values will cause constraint violations",
                    suggested_migration=f"Update NULL values to valid defaults before applying NOT NULL constraint",
                    affected_operations=["INSERT", "UPDATE"]
                ))
                
                scripts.append(MigrationScript(
                    script_type="sql",
                    description=f"Make column {col_name} NOT NULL",
                    script_content=f"""
                    -- Update NULL values first
                    UPDATE {table_name} SET {col_name} = 'DEFAULT_VALUE' WHERE {col_name} IS NULL;
                    -- Add NOT NULL constraint
                    ALTER TABLE {table_name} ALTER COLUMN {col_name} SET NOT NULL;
                    """,
                    rollback_script=f"ALTER TABLE {table_name} ALTER COLUMN {col_name} DROP NOT NULL;",
                    dependencies=[],
                    validation_query=f"SELECT COUNT(*) FROM {table_name} WHERE {col_name} IS NULL;"
                ))
        
        # Check length/precision changes
        before_length = before_col.get("length")
        after_length = after_col.get("length")
        
        if before_length and after_length and before_length != after_length:
            if after_length < before_length:
                issues.append(CompatibilityIssue(
                    type="length_reduction",
                    severity="potentially_breaking",
                    description=f"Column '{col_name}' length reduced from {before_length} to {after_length}",
                    field_path=f"tables.{table_name}.columns.{col_name}.length",
                    old_value=before_length,
                    new_value=after_length,
                    impact="Data truncation may occur for values exceeding new length",
                    suggested_migration=f"Validate no existing data exceeds new length limit",
                    affected_operations=["INSERT", "UPDATE"]
                ))
        
        return issues, scripts
    
    def _analyze_constraint_changes(self, table_name: str, before_constraints: Dict[str, Any], 
                                  after_constraints: Dict[str, Any]) -> Tuple[List[CompatibilityIssue], List[MigrationScript]]:
        """Analyze constraint changes"""
        issues = []
        scripts = []
        
        for constraint_type in ["primary_key", "foreign_key", "unique", "check"]:
            before_constraint = before_constraints.get(constraint_type, [])
            after_constraint = after_constraints.get(constraint_type, [])
            
            # Convert to sets for comparison
            before_set = set(str(c) for c in before_constraint) if isinstance(before_constraint, list) else {str(before_constraint)} if before_constraint else set()
            after_set = set(str(c) for c in after_constraint) if isinstance(after_constraint, list) else {str(after_constraint)} if after_constraint else set()
            
            # Check for removed constraints
            for constraint in before_set - after_set:
                implication = self.constraint_implications.get(constraint_type, {}).get("removed", "non_breaking")
                issues.append(CompatibilityIssue(
                    type=f"{constraint_type}_removed",
                    severity=implication,
                    description=f"{constraint_type.replace('_', ' ').title()} constraint '{constraint}' removed from table '{table_name}'",
                    field_path=f"tables.{table_name}.constraints.{constraint_type}",
                    old_value=constraint,
                    new_value=None,
                    impact=f"No longer enforcing {constraint_type} constraint",
                    suggested_migration=f"Consider application-level validation for removed constraint",
                    affected_operations=["INSERT", "UPDATE", "DELETE"]
                ))
            
            # Check for added constraints
            for constraint in after_set - before_set:
                implication = self.constraint_implications.get(constraint_type, {}).get("added", "potentially_breaking")
                issues.append(CompatibilityIssue(
                    type=f"{constraint_type}_added",
                    severity=implication,
                    description=f"New {constraint_type.replace('_', ' ')} constraint '{constraint}' added to table '{table_name}'",
                    field_path=f"tables.{table_name}.constraints.{constraint_type}",
                    old_value=None,
                    new_value=constraint,
                    impact=f"New {constraint_type} constraint may reject existing data",
                    suggested_migration=f"Validate existing data complies with new constraint",
                    affected_operations=["INSERT", "UPDATE"]
                ))
                
                scripts.append(MigrationScript(
                    script_type="sql",
                    description=f"Add {constraint_type} constraint to {table_name}",
                    script_content=f"ALTER TABLE {table_name} ADD CONSTRAINT {constraint_type}_{table_name} {constraint_type.upper()} ({constraint});",
                    rollback_script=f"ALTER TABLE {table_name} DROP CONSTRAINT {constraint_type}_{table_name};",
                    dependencies=[],
                    validation_query=f"SELECT COUNT(*) FROM information_schema.table_constraints WHERE table_name = '{table_name}' AND constraint_type = '{constraint_type.upper()}';"
                ))
        
        return issues, scripts
    
    def _analyze_endpoint_changes(self, path: str, before_endpoint: Dict[str, Any], 
                                after_endpoint: Dict[str, Any]) -> Tuple[List[CompatibilityIssue], List[MigrationScript]]:
        """Analyze changes to an API endpoint"""
        issues = []
        scripts = []
        
        for method in set(before_endpoint.keys()) & set(after_endpoint.keys()):
            before_method = before_endpoint[method]
            after_method = after_endpoint[method]
            
            # Check parameter changes
            before_params = before_method.get("parameters", [])
            after_params = after_method.get("parameters", [])
            
            before_param_names = {p["name"] for p in before_params}
            after_param_names = {p["name"] for p in after_params}
            
            # Check for removed required parameters
            for param_name in before_param_names - after_param_names:
                param = next(p for p in before_params if p["name"] == param_name)
                if param.get("required", False):
                    issues.append(CompatibilityIssue(
                        type="required_parameter_removed",
                        severity="breaking",
                        description=f"Required parameter '{param_name}' removed from {method.upper()} {path}",
                        field_path=f"paths.{path}.{method}.parameters",
                        old_value=param,
                        new_value=None,
                        impact="Client requests with this parameter will fail",
                        suggested_migration="Implement parameter validation with backward compatibility",
                        affected_operations=[f"{method.upper()} {path}"]
                    ))
            
            # Check for added required parameters
            for param_name in after_param_names - before_param_names:
                param = next(p for p in after_params if p["name"] == param_name)
                if param.get("required", False):
                    issues.append(CompatibilityIssue(
                        type="required_parameter_added",
                        severity="breaking",
                        description=f"New required parameter '{param_name}' added to {method.upper()} {path}",
                        field_path=f"paths.{path}.{method}.parameters",
                        old_value=None,
                        new_value=param,
                        impact="Client requests without this parameter will fail",
                        suggested_migration="Provide default value or make parameter optional initially",
                        affected_operations=[f"{method.upper()} {path}"]
                    ))
            
            # Check response schema changes
            before_responses = before_method.get("responses", {})
            after_responses = after_method.get("responses", {})
            
            for status_code in before_responses:
                if status_code in after_responses:
                    before_schema = before_responses[status_code].get("content", {}).get("application/json", {}).get("schema", {})
                    after_schema = after_responses[status_code].get("content", {}).get("application/json", {}).get("schema", {})
                    
                    if before_schema != after_schema:
                        issues.append(CompatibilityIssue(
                            type="response_schema_changed",
                            severity="potentially_breaking",
                            description=f"Response schema changed for {method.upper()} {path} (status {status_code})",
                            field_path=f"paths.{path}.{method}.responses.{status_code}",
                            old_value=before_schema,
                            new_value=after_schema,
                            impact="Client response parsing may fail",
                            suggested_migration="Implement versioned API responses",
                            affected_operations=[f"{method.upper()} {path}"]
                        ))
        
        return issues, scripts
    
    def _analyze_model_changes(self, model_name: str, before_model: Dict[str, Any], 
                             after_model: Dict[str, Any]) -> Tuple[List[CompatibilityIssue], List[MigrationScript]]:
        """Analyze changes to an API data model"""
        issues = []
        scripts = []
        
        before_props = before_model.get("properties", {})
        after_props = after_model.get("properties", {})
        before_required = set(before_model.get("required", []))
        after_required = set(after_model.get("required", []))
        
        # Check for removed properties
        for prop_name in set(before_props.keys()) - set(after_props.keys()):
            issues.append(CompatibilityIssue(
                type="property_removed",
                severity="breaking",
                description=f"Property '{prop_name}' removed from model '{model_name}'",
                field_path=f"components.schemas.{model_name}.properties.{prop_name}",
                old_value=before_props[prop_name],
                new_value=None,
                impact="Client code expecting this property will fail",
                suggested_migration="Use API versioning to maintain backward compatibility",
                affected_operations=["Serialization", "Deserialization"]
            ))
        
        # Check for newly required properties
        for prop_name in after_required - before_required:
            issues.append(CompatibilityIssue(
                type="property_made_required",
                severity="breaking",
                description=f"Property '{prop_name}' is now required in model '{model_name}'",
                field_path=f"components.schemas.{model_name}.required",
                old_value=list(before_required),
                new_value=list(after_required),
                impact="Client requests without this property will fail validation",
                suggested_migration="Provide default values or implement gradual rollout",
                affected_operations=["Request validation"]
            ))
        
        # Check for property type changes
        for prop_name in set(before_props.keys()) & set(after_props.keys()):
            before_type = before_props[prop_name].get("type")
            after_type = after_props[prop_name].get("type")
            
            if before_type != after_type:
                compatibility = self.type_compatibility_matrix.get(before_type, {}).get(after_type, "breaking")
                issues.append(CompatibilityIssue(
                    type="property_type_changed",
                    severity=compatibility,
                    description=f"Property '{prop_name}' type changed from {before_type} to {after_type} in model '{model_name}'",
                    field_path=f"components.schemas.{model_name}.properties.{prop_name}.type",
                    old_value=before_type,
                    new_value=after_type,
                    impact="Client serialization/deserialization may fail",
                    suggested_migration="Implement type coercion or API versioning",
                    affected_operations=["Serialization", "Deserialization"]
                ))
        
        return issues, scripts
    
    def _build_compatibility_report(self, before_schema: Dict[str, Any], after_schema: Dict[str, Any],
                                  issues: List[CompatibilityIssue], migration_scripts: List[MigrationScript]) -> CompatibilityReport:
        """Build the final compatibility report"""
        # Count issues by severity
        breaking_count = sum(1 for issue in issues if issue.severity == "breaking")
        potentially_breaking_count = sum(1 for issue in issues if issue.severity == "potentially_breaking")
        non_breaking_count = sum(1 for issue in issues if issue.severity == "non_breaking")
        additive_count = sum(1 for issue in issues if issue.type == "additive")
        
        # Determine overall compatibility
        if breaking_count > 0:
            overall_compatibility = "breaking_changes"
        elif potentially_breaking_count > 0:
            overall_compatibility = "potentially_incompatible"
        elif non_breaking_count > 0:
            overall_compatibility = "backward_compatible"
        else:
            overall_compatibility = "fully_compatible"
        
        # Generate risk assessment
        risk_assessment = {
            "overall_risk": "high" if breaking_count > 0 else "medium" if potentially_breaking_count > 0 else "low",
            "deployment_risk": "requires_coordinated_deployment" if breaking_count > 0 else "safe_independent_deployment",
            "rollback_complexity": "high" if breaking_count > 3 else "medium" if breaking_count > 0 else "low",
            "testing_requirements": ["integration_testing", "regression_testing"] + 
                                  (["data_migration_testing"] if any(s.script_type == "sql" for s in migration_scripts) else [])
        }
        
        # Generate recommendations
        recommendations = []
        if breaking_count > 0:
            recommendations.append("Implement API versioning to maintain backward compatibility")
            recommendations.append("Plan for coordinated deployment with all clients")
            recommendations.append("Implement comprehensive rollback procedures")
        
        if potentially_breaking_count > 0:
            recommendations.append("Conduct thorough testing with realistic data volumes")
            recommendations.append("Implement monitoring for migration success metrics")
        
        if migration_scripts:
            recommendations.append("Test all migration scripts in staging environment")
            recommendations.append("Implement migration progress monitoring")
        
        recommendations.append("Create detailed communication plan for stakeholders")
        recommendations.append("Implement feature flags for gradual rollout")
        
        return CompatibilityReport(
            schema_before=json.dumps(before_schema, indent=2)[:500] + "..." if len(json.dumps(before_schema)) > 500 else json.dumps(before_schema, indent=2),
            schema_after=json.dumps(after_schema, indent=2)[:500] + "..." if len(json.dumps(after_schema)) > 500 else json.dumps(after_schema, indent=2),
            analysis_date=datetime.datetime.now().isoformat(),
            overall_compatibility=overall_compatibility,
            breaking_changes_count=breaking_count,
            potentially_breaking_count=potentially_breaking_count,
            non_breaking_changes_count=non_breaking_count,
            additive_changes_count=additive_count,
            issues=issues,
            migration_scripts=migration_scripts,
            risk_assessment=risk_assessment,
            recommendations=recommendations
        )
    
    def _generate_create_table_sql(self, table_name: str, table_def: Dict[str, Any]) -> str:
        """Generate CREATE TABLE SQL statement"""
        columns = []
        for col_name, col_def in table_def.get("columns", {}).items():
            columns.append(self._generate_column_definition(col_name, col_def))
        
        return f"CREATE TABLE {table_name} (\n  " + ",\n  ".join(columns) + "\n);"
    
    def _generate_column_definition(self, col_name: str, col_def: Dict[str, Any]) -> str:
        """Generate column definition for SQL"""
        col_type = col_def.get("type", "VARCHAR(255)")
        nullable = "" if col_def.get("nullable", True) else " NOT NULL"
        default = f" DEFAULT {col_def.get('default')}" if col_def.get("default") is not None else ""
        
        return f"{col_name} {col_type}{nullable}{default}"
    
    def generate_human_readable_report(self, report: CompatibilityReport) -> str:
        """Generate human-readable compatibility report"""
        output = []
        output.append("=" * 80)
        output.append("COMPATIBILITY ANALYSIS REPORT")
        output.append("=" * 80)
        output.append(f"Analysis Date: {report.analysis_date}")
        output.append(f"Overall Compatibility: {report.overall_compatibility.upper()}")
        output.append("")
        
        # Summary
        output.append("SUMMARY")
        output.append("-" * 40)
        output.append(f"Breaking Changes: {report.breaking_changes_count}")
        output.append(f"Potentially Breaking: {report.potentially_breaking_count}")
        output.append(f"Non-Breaking Changes: {report.non_breaking_changes_count}")
        output.append(f"Additive Changes: {report.additive_changes_count}")
        output.append(f"Total Issues Found: {len(report.issues)}")
        output.append("")
        
        # Risk Assessment
        output.append("RISK ASSESSMENT")
        output.append("-" * 40)
        for key, value in report.risk_assessment.items():
            output.append(f"{key.replace('_', ' ').title()}: {value}")
        output.append("")
        
        # Issues by Severity
        issues_by_severity = {}
        for issue in report.issues:
            if issue.severity not in issues_by_severity:
                issues_by_severity[issue.severity] = []
            issues_by_severity[issue.severity].append(issue)
        
        for severity in ["breaking", "potentially_breaking", "non_breaking"]:
            if severity in issues_by_severity:
                output.append(f"{severity.upper().replace('_', ' ')} ISSUES")
                output.append("-" * 40)
                for issue in issues_by_severity[severity]:
                    output.append(f"• {issue.description}")
                    output.append(f"  Field: {issue.field_path}")
                    output.append(f"  Impact: {issue.impact}")
                    output.append(f"  Migration: {issue.suggested_migration}")
                    if issue.affected_operations:
                        output.append(f"  Affected Operations: {', '.join(issue.affected_operations)}")
                    output.append("")
        
        # Migration Scripts
        if report.migration_scripts:
            output.append("SUGGESTED MIGRATION SCRIPTS")
            output.append("-" * 40)
            for i, script in enumerate(report.migration_scripts, 1):
                output.append(f"{i}. {script.description}")
                output.append(f"   Type: {script.script_type}")
                output.append("   Script:")
                for line in script.script_content.split('\n'):
                    output.append(f"     {line}")
                output.append("")
        
        # Recommendations
        output.append("RECOMMENDATIONS")
        output.append("-" * 40)
        for i, rec in enumerate(report.recommendations, 1):
            output.append(f"{i}. {rec}")
        output.append("")
        
        return "\n".join(output)


def main():
    """Main function with command line interface"""
    parser = argparse.ArgumentParser(description="Analyze schema and API compatibility between versions")
    parser.add_argument("--before", required=True, help="Before schema file (JSON)")
    parser.add_argument("--after", required=True, help="After schema file (JSON)")
    parser.add_argument("--type", choices=["database", "api"], default="database", help="Schema type to analyze")
    parser.add_argument("--output", "-o", help="Output file for compatibility report (JSON)")
    parser.add_argument("--format", "-f", choices=["json", "text", "both"], default="both", help="Output format")
    
    args = parser.parse_args()
    
    try:
        # Load schemas
        with open(args.before, 'r') as f:
            before_schema = json.load(f)
        
        with open(args.after, 'r') as f:
            after_schema = json.load(f)
        
        # Analyze compatibility
        checker = SchemaCompatibilityChecker()
        
        if args.type == "database":
            report = checker.analyze_database_schema(before_schema, after_schema)
        else:  # api
            report = checker.analyze_api_schema(before_schema, after_schema)
        
        # Output results
        if args.format in ["json", "both"]:
            report_dict = asdict(report)
            if args.output:
                with open(args.output, 'w') as f:
                    json.dump(report_dict, f, indent=2)
                print(f"Compatibility report saved to {args.output}")
            else:
                print(json.dumps(report_dict, indent=2))
        
        if args.format in ["text", "both"]:
            human_report = checker.generate_human_readable_report(report)
            text_output = args.output.replace('.json', '.txt') if args.output else None
            if text_output:
                with open(text_output, 'w') as f:
                    f.write(human_report)
                print(f"Human-readable report saved to {text_output}")
            else:
                print("\n" + "="*80)
                print("HUMAN-READABLE COMPATIBILITY REPORT")
                print("="*80)
                print(human_report)
        
        # Return exit code based on compatibility
        if report.breaking_changes_count > 0:
            return 2  # Breaking changes found
        elif report.potentially_breaking_count > 0:
            return 1  # Potentially breaking changes found
        else:
            return 0  # No compatibility issues
            
    except FileNotFoundError as e:
        print(f"Error: File not found: {e}", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())