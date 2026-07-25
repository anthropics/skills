#!/usr/bin/env python3
"""
Breaking Change Detector - Compares API specification versions to identify breaking changes.

This script analyzes two versions of an API specification and detects potentially
breaking changes including:
- Removed endpoints
- Modified response structures
- Removed or renamed fields
- Field type changes
- New required fields
- HTTP status code changes
- Parameter changes

Generates detailed reports with migration guides for each breaking change.
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Set, Optional, Tuple, Union
from dataclasses import dataclass, field
from enum import Enum


class ChangeType(Enum):
    """Types of API changes."""
    BREAKING = "breaking"
    POTENTIALLY_BREAKING = "potentially_breaking"
    NON_BREAKING = "non_breaking"
    ENHANCEMENT = "enhancement"


class ChangeSeverity(Enum):
    """Severity levels for changes."""
    CRITICAL = "critical"     # Will definitely break clients
    HIGH = "high"            # Likely to break some clients
    MEDIUM = "medium"        # May break clients depending on usage
    LOW = "low"             # Minor impact, unlikely to break clients
    INFO = "info"           # Informational, no breaking impact


@dataclass
class Change:
    """Represents a detected change between API versions."""
    change_type: ChangeType
    severity: ChangeSeverity
    category: str
    path: str
    message: str
    old_value: Any = None
    new_value: Any = None
    migration_guide: str = ""
    impact_description: str = ""
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert change to dictionary for JSON serialization."""
        return {
            "changeType": self.change_type.value,
            "severity": self.severity.value,
            "category": self.category,
            "path": self.path,
            "message": self.message,
            "oldValue": self.old_value,
            "newValue": self.new_value,
            "migrationGuide": self.migration_guide,
            "impactDescription": self.impact_description
        }


@dataclass
class ComparisonReport:
    """Complete comparison report between two API versions."""
    changes: List[Change] = field(default_factory=list)
    summary: Dict[str, int] = field(default_factory=dict)
    
    def add_change(self, change: Change) -> None:
        """Add a change to the report."""
        self.changes.append(change)
    
    def calculate_summary(self) -> None:
        """Calculate summary statistics."""
        self.summary = {
            "total_changes": len(self.changes),
            "breaking_changes": len([c for c in self.changes if c.change_type == ChangeType.BREAKING]),
            "potentially_breaking_changes": len([c for c in self.changes if c.change_type == ChangeType.POTENTIALLY_BREAKING]),
            "non_breaking_changes": len([c for c in self.changes if c.change_type == ChangeType.NON_BREAKING]),
            "enhancements": len([c for c in self.changes if c.change_type == ChangeType.ENHANCEMENT]),
            "critical_severity": len([c for c in self.changes if c.severity == ChangeSeverity.CRITICAL]),
            "high_severity": len([c for c in self.changes if c.severity == ChangeSeverity.HIGH]),
            "medium_severity": len([c for c in self.changes if c.severity == ChangeSeverity.MEDIUM]),
            "low_severity": len([c for c in self.changes if c.severity == ChangeSeverity.LOW]),
            "info_severity": len([c for c in self.changes if c.severity == ChangeSeverity.INFO])
        }
    
    def has_breaking_changes(self) -> bool:
        """Check if report contains any breaking changes."""
        return any(c.change_type in [ChangeType.BREAKING, ChangeType.POTENTIALLY_BREAKING] 
                  for c in self.changes)


class BreakingChangeDetector:
    """Main breaking change detection engine."""
    
    def __init__(self):
        self.report = ComparisonReport()
        self.old_spec: Optional[Dict] = None
        self.new_spec: Optional[Dict] = None
    
    def compare_specs(self, old_spec: Dict[str, Any], new_spec: Dict[str, Any]) -> ComparisonReport:
        """Compare two API specifications and detect changes."""
        self.old_spec = old_spec
        self.new_spec = new_spec
        self.report = ComparisonReport()
        
        # Compare different sections of the API specification
        self._compare_info_section()
        self._compare_servers_section()
        self._compare_paths_section()
        self._compare_components_section()
        self._compare_security_section()
        
        # Calculate summary statistics
        self.report.calculate_summary()
        
        return self.report
    
    def _compare_info_section(self) -> None:
        """Compare API info sections."""
        old_info = self.old_spec.get('info', {})
        new_info = self.new_spec.get('info', {})
        
        # Version comparison
        old_version = old_info.get('version', '')
        new_version = new_info.get('version', '')
        
        if old_version != new_version:
            self.report.add_change(Change(
                change_type=ChangeType.NON_BREAKING,
                severity=ChangeSeverity.INFO,
                category="versioning",
                path="/info/version",
                message=f"API version changed from '{old_version}' to '{new_version}'",
                old_value=old_version,
                new_value=new_version,
                impact_description="Version change indicates API evolution"
            ))
        
        # Title comparison
        old_title = old_info.get('title', '')
        new_title = new_info.get('title', '')
        
        if old_title != new_title:
            self.report.add_change(Change(
                change_type=ChangeType.NON_BREAKING,
                severity=ChangeSeverity.INFO,
                category="metadata",
                path="/info/title",
                message=f"API title changed from '{old_title}' to '{new_title}'",
                old_value=old_title,
                new_value=new_title,
                impact_description="Title change is cosmetic and doesn't affect functionality"
            ))
    
    def _compare_servers_section(self) -> None:
        """Compare server configurations."""
        old_servers = self.old_spec.get('servers', [])
        new_servers = self.new_spec.get('servers', [])
        
        old_urls = {server.get('url', '') for server in old_servers if isinstance(server, dict)}
        new_urls = {server.get('url', '') for server in new_servers if isinstance(server, dict)}
        
        # Removed servers
        removed_urls = old_urls - new_urls
        for url in removed_urls:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.HIGH,
                category="servers",
                path="/servers",
                message=f"Server URL removed: {url}",
                old_value=url,
                new_value=None,
                migration_guide=f"Update client configurations to use alternative server URLs: {list(new_urls)}",
                impact_description="Clients configured to use removed server URL will fail to connect"
            ))
        
        # Added servers
        added_urls = new_urls - old_urls
        for url in added_urls:
            self.report.add_change(Change(
                change_type=ChangeType.ENHANCEMENT,
                severity=ChangeSeverity.INFO,
                category="servers",
                path="/servers",
                message=f"New server URL added: {url}",
                old_value=None,
                new_value=url,
                impact_description="New server option provides additional deployment flexibility"
            ))
    
    def _compare_paths_section(self) -> None:
        """Compare API paths and operations."""
        old_paths = self.old_spec.get('paths', {})
        new_paths = self.new_spec.get('paths', {})
        
        # Find removed, added, and modified paths
        old_path_set = set(old_paths.keys())
        new_path_set = set(new_paths.keys())
        
        removed_paths = old_path_set - new_path_set
        added_paths = new_path_set - old_path_set
        common_paths = old_path_set & new_path_set
        
        # Handle removed paths
        for path in removed_paths:
            old_operations = self._extract_operations(old_paths[path])
            for method in old_operations:
                self.report.add_change(Change(
                    change_type=ChangeType.BREAKING,
                    severity=ChangeSeverity.CRITICAL,
                    category="endpoints",
                    path=f"/paths{path}",
                    message=f"Endpoint removed: {method.upper()} {path}",
                    old_value=f"{method.upper()} {path}",
                    new_value=None,
                    migration_guide=self._generate_endpoint_removal_migration(path, method, new_paths),
                    impact_description="Clients using this endpoint will receive 404 errors"
                ))
        
        # Handle added paths
        for path in added_paths:
            new_operations = self._extract_operations(new_paths[path])
            for method in new_operations:
                self.report.add_change(Change(
                    change_type=ChangeType.ENHANCEMENT,
                    severity=ChangeSeverity.INFO,
                    category="endpoints",
                    path=f"/paths{path}",
                    message=f"New endpoint added: {method.upper()} {path}",
                    old_value=None,
                    new_value=f"{method.upper()} {path}",
                    impact_description="New functionality available to clients"
                ))
        
        # Handle modified paths
        for path in common_paths:
            self._compare_path_operations(path, old_paths[path], new_paths[path])
    
    def _extract_operations(self, path_object: Dict[str, Any]) -> List[str]:
        """Extract HTTP operations from a path object."""
        http_methods = {'get', 'post', 'put', 'patch', 'delete', 'head', 'options', 'trace'}
        return [method for method in path_object.keys() if method.lower() in http_methods]
    
    def _compare_path_operations(self, path: str, old_path_obj: Dict, new_path_obj: Dict) -> None:
        """Compare operations within a specific path."""
        old_operations = set(self._extract_operations(old_path_obj))
        new_operations = set(self._extract_operations(new_path_obj))
        
        # Removed operations
        removed_ops = old_operations - new_operations
        for method in removed_ops:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.CRITICAL,
                category="endpoints",
                path=f"/paths{path}/{method}",
                message=f"HTTP method removed: {method.upper()} {path}",
                old_value=f"{method.upper()} {path}",
                new_value=None,
                migration_guide=self._generate_method_removal_migration(path, method, new_operations),
                impact_description="Clients using this method will receive 405 Method Not Allowed errors"
            ))
        
        # Added operations
        added_ops = new_operations - old_operations
        for method in added_ops:
            self.report.add_change(Change(
                change_type=ChangeType.ENHANCEMENT,
                severity=ChangeSeverity.INFO,
                category="endpoints",
                path=f"/paths{path}/{method}",
                message=f"New HTTP method added: {method.upper()} {path}",
                old_value=None,
                new_value=f"{method.upper()} {path}",
                impact_description="New method provides additional functionality for this resource"
            ))
        
        # Modified operations
        common_ops = old_operations & new_operations
        for method in common_ops:
            self._compare_operation_details(path, method, old_path_obj[method], new_path_obj[method])
    
    def _compare_operation_details(self, path: str, method: str, old_op: Dict, new_op: Dict) -> None:
        """Compare details of individual operations."""
        operation_path = f"/paths{path}/{method}"
        
        # Compare parameters
        self._compare_parameters(operation_path, old_op.get('parameters', []), new_op.get('parameters', []))
        
        # Compare request body
        self._compare_request_body(operation_path, old_op.get('requestBody'), new_op.get('requestBody'))
        
        # Compare responses
        self._compare_responses(operation_path, old_op.get('responses', {}), new_op.get('responses', {}))
        
        # Compare security requirements
        self._compare_security_requirements(operation_path, old_op.get('security'), new_op.get('security'))
    
    def _compare_parameters(self, base_path: str, old_params: List[Dict], new_params: List[Dict]) -> None:
        """Compare operation parameters."""
        # Create lookup dictionaries
        old_param_map = {(p.get('name'), p.get('in')): p for p in old_params}
        new_param_map = {(p.get('name'), p.get('in')): p for p in new_params}
        
        old_param_keys = set(old_param_map.keys())
        new_param_keys = set(new_param_map.keys())
        
        # Removed parameters
        removed_params = old_param_keys - new_param_keys
        for param_key in removed_params:
            name, location = param_key
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.HIGH,
                category="parameters",
                path=f"{base_path}/parameters",
                message=f"Parameter removed: {name} (in: {location})",
                old_value=old_param_map[param_key],
                new_value=None,
                migration_guide=f"Remove '{name}' parameter from {location} when calling this endpoint",
                impact_description="Clients sending this parameter may receive validation errors"
            ))
        
        # Added parameters
        added_params = new_param_keys - old_param_keys
        for param_key in added_params:
            name, location = param_key
            new_param = new_param_map[param_key]
            is_required = new_param.get('required', False)
            
            if is_required:
                self.report.add_change(Change(
                    change_type=ChangeType.BREAKING,
                    severity=ChangeSeverity.CRITICAL,
                    category="parameters",
                    path=f"{base_path}/parameters",
                    message=f"New required parameter added: {name} (in: {location})",
                    old_value=None,
                    new_value=new_param,
                    migration_guide=f"Add required '{name}' parameter to {location} when calling this endpoint",
                    impact_description="Clients not providing this parameter will receive 400 Bad Request errors"
                ))
            else:
                self.report.add_change(Change(
                    change_type=ChangeType.NON_BREAKING,
                    severity=ChangeSeverity.INFO,
                    category="parameters",
                    path=f"{base_path}/parameters",
                    message=f"New optional parameter added: {name} (in: {location})",
                    old_value=None,
                    new_value=new_param,
                    impact_description="Optional parameter provides additional functionality"
                ))
        
        # Modified parameters
        common_params = old_param_keys & new_param_keys
        for param_key in common_params:
            name, location = param_key
            old_param = old_param_map[param_key]
            new_param = new_param_map[param_key]
            self._compare_parameter_details(base_path, name, location, old_param, new_param)
    
    def _compare_parameter_details(self, base_path: str, name: str, location: str, 
                                 old_param: Dict, new_param: Dict) -> None:
        """Compare individual parameter details."""
        param_path = f"{base_path}/parameters/{name}"
        
        # Required status change
        old_required = old_param.get('required', False)
        new_required = new_param.get('required', False)
        
        if old_required != new_required:
            if new_required:
                self.report.add_change(Change(
                    change_type=ChangeType.BREAKING,
                    severity=ChangeSeverity.HIGH,
                    category="parameters",
                    path=param_path,
                    message=f"Parameter '{name}' is now required (was optional)",
                    old_value=old_required,
                    new_value=new_required,
                    migration_guide=f"Ensure '{name}' parameter is always provided when calling this endpoint",
                    impact_description="Clients not providing this parameter will receive validation errors"
                ))
            else:
                self.report.add_change(Change(
                    change_type=ChangeType.NON_BREAKING,
                    severity=ChangeSeverity.INFO,
                    category="parameters",
                    path=param_path,
                    message=f"Parameter '{name}' is now optional (was required)",
                    old_value=old_required,
                    new_value=new_required,
                    impact_description="Parameter is now optional, providing more flexibility to clients"
                ))
        
        # Schema/type changes
        old_schema = old_param.get('schema', {})
        new_schema = new_param.get('schema', {})
        
        if old_schema != new_schema:
            self._compare_schemas(param_path, old_schema, new_schema, f"parameter '{name}'")
    
    def _compare_request_body(self, base_path: str, old_body: Optional[Dict], new_body: Optional[Dict]) -> None:
        """Compare request body specifications."""
        body_path = f"{base_path}/requestBody"
        
        # Request body added
        if old_body is None and new_body is not None:
            is_required = new_body.get('required', False)
            if is_required:
                self.report.add_change(Change(
                    change_type=ChangeType.BREAKING,
                    severity=ChangeSeverity.HIGH,
                    category="request_body",
                    path=body_path,
                    message="Required request body added",
                    old_value=None,
                    new_value=new_body,
                    migration_guide="Include request body with appropriate content type when calling this endpoint",
                    impact_description="Clients not providing request body will receive validation errors"
                ))
            else:
                self.report.add_change(Change(
                    change_type=ChangeType.NON_BREAKING,
                    severity=ChangeSeverity.INFO,
                    category="request_body",
                    path=body_path,
                    message="Optional request body added",
                    old_value=None,
                    new_value=new_body,
                    impact_description="Optional request body provides additional functionality"
                ))
        
        # Request body removed
        elif old_body is not None and new_body is None:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.HIGH,
                category="request_body",
                path=body_path,
                message="Request body removed",
                old_value=old_body,
                new_value=None,
                migration_guide="Remove request body when calling this endpoint",
                impact_description="Clients sending request body may receive validation errors"
            ))
        
        # Request body modified
        elif old_body is not None and new_body is not None:
            self._compare_request_body_details(body_path, old_body, new_body)
    
    def _compare_request_body_details(self, base_path: str, old_body: Dict, new_body: Dict) -> None:
        """Compare request body details."""
        # Required status change
        old_required = old_body.get('required', False)
        new_required = new_body.get('required', False)
        
        if old_required != new_required:
            if new_required:
                self.report.add_change(Change(
                    change_type=ChangeType.BREAKING,
                    severity=ChangeSeverity.HIGH,
                    category="request_body",
                    path=base_path,
                    message="Request body is now required (was optional)",
                    old_value=old_required,
                    new_value=new_required,
                    migration_guide="Always include request body when calling this endpoint",
                    impact_description="Clients not providing request body will receive validation errors"
                ))
            else:
                self.report.add_change(Change(
                    change_type=ChangeType.NON_BREAKING,
                    severity=ChangeSeverity.INFO,
                    category="request_body",
                    path=base_path,
                    message="Request body is now optional (was required)",
                    old_value=old_required,
                    new_value=new_required,
                    impact_description="Request body is now optional, providing more flexibility"
                ))
        
        # Content type changes
        old_content = old_body.get('content', {})
        new_content = new_body.get('content', {})
        self._compare_content_types(base_path, old_content, new_content, "request body")
    
    def _compare_responses(self, base_path: str, old_responses: Dict, new_responses: Dict) -> None:
        """Compare response specifications."""
        responses_path = f"{base_path}/responses"
        
        old_status_codes = set(old_responses.keys())
        new_status_codes = set(new_responses.keys())
        
        # Removed status codes
        removed_codes = old_status_codes - new_status_codes
        for code in removed_codes:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.HIGH,
                category="responses",
                path=f"{responses_path}/{code}",
                message=f"Response status code {code} removed",
                old_value=old_responses[code],
                new_value=None,
                migration_guide=f"Handle alternative status codes: {list(new_status_codes)}",
                impact_description=f"Clients expecting status code {code} need to handle different responses"
            ))
        
        # Added status codes
        added_codes = new_status_codes - old_status_codes
        for code in added_codes:
            self.report.add_change(Change(
                change_type=ChangeType.NON_BREAKING,
                severity=ChangeSeverity.INFO,
                category="responses",
                path=f"{responses_path}/{code}",
                message=f"New response status code {code} added",
                old_value=None,
                new_value=new_responses[code],
                impact_description="New status code provides more specific response information"
            ))
        
        # Modified responses
        common_codes = old_status_codes & new_status_codes
        for code in common_codes:
            self._compare_response_details(responses_path, code, old_responses[code], new_responses[code])
    
    def _compare_response_details(self, base_path: str, status_code: str, 
                                old_response: Dict, new_response: Dict) -> None:
        """Compare individual response details."""
        response_path = f"{base_path}/{status_code}"
        
        # Compare content types and schemas
        old_content = old_response.get('content', {})
        new_content = new_response.get('content', {})
        
        self._compare_content_types(response_path, old_content, new_content, f"response {status_code}")
    
    def _compare_content_types(self, base_path: str, old_content: Dict, new_content: Dict, context: str) -> None:
        """Compare content types and their schemas."""
        old_types = set(old_content.keys())
        new_types = set(new_content.keys())
        
        # Removed content types
        removed_types = old_types - new_types
        for content_type in removed_types:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.HIGH,
                category="content_types",
                path=f"{base_path}/content",
                message=f"Content type '{content_type}' removed from {context}",
                old_value=content_type,
                new_value=None,
                migration_guide=f"Use alternative content types: {list(new_types)}",
                impact_description=f"Clients expecting '{content_type}' need to handle different formats"
            ))
        
        # Added content types
        added_types = new_types - old_types
        for content_type in added_types:
            self.report.add_change(Change(
                change_type=ChangeType.ENHANCEMENT,
                severity=ChangeSeverity.INFO,
                category="content_types",
                path=f"{base_path}/content",
                message=f"New content type '{content_type}' added to {context}",
                old_value=None,
                new_value=content_type,
                impact_description=f"Additional format option available for {context}"
            ))
        
        # Modified schemas for common content types
        common_types = old_types & new_types
        for content_type in common_types:
            old_media = old_content[content_type]
            new_media = new_content[content_type]
            
            old_schema = old_media.get('schema', {})
            new_schema = new_media.get('schema', {})
            
            if old_schema != new_schema:
                schema_path = f"{base_path}/content/{content_type}/schema"
                self._compare_schemas(schema_path, old_schema, new_schema, f"{context} ({content_type})")
    
    def _compare_schemas(self, base_path: str, old_schema: Dict, new_schema: Dict, context: str) -> None:
        """Compare schema definitions."""
        # Type changes
        old_type = old_schema.get('type')
        new_type = new_schema.get('type')
        
        if old_type != new_type and old_type is not None and new_type is not None:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.CRITICAL,
                category="schema",
                path=base_path,
                message=f"Schema type changed from '{old_type}' to '{new_type}' for {context}",
                old_value=old_type,
                new_value=new_type,
                migration_guide=f"Update client code to handle {new_type} instead of {old_type}",
                impact_description="Type change will break client parsing and validation"
            ))
        
        # Property changes for object types
        if old_schema.get('type') == 'object' and new_schema.get('type') == 'object':
            self._compare_object_properties(base_path, old_schema, new_schema, context)
        
        # Array item changes
        if old_schema.get('type') == 'array' and new_schema.get('type') == 'array':
            old_items = old_schema.get('items', {})
            new_items = new_schema.get('items', {})
            if old_items != new_items:
                self._compare_schemas(f"{base_path}/items", old_items, new_items, f"{context} items")
    
    def _compare_object_properties(self, base_path: str, old_schema: Dict, new_schema: Dict, context: str) -> None:
        """Compare object schema properties."""
        old_props = old_schema.get('properties', {})
        new_props = new_schema.get('properties', {})
        old_required = set(old_schema.get('required', []))
        new_required = set(new_schema.get('required', []))
        
        old_prop_names = set(old_props.keys())
        new_prop_names = set(new_props.keys())
        
        # Removed properties
        removed_props = old_prop_names - new_prop_names
        for prop_name in removed_props:
            severity = ChangeSeverity.CRITICAL if prop_name in old_required else ChangeSeverity.HIGH
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=severity,
                category="schema",
                path=f"{base_path}/properties",
                message=f"Property '{prop_name}' removed from {context}",
                old_value=old_props[prop_name],
                new_value=None,
                migration_guide=f"Remove references to '{prop_name}' property in client code",
                impact_description="Clients expecting this property will receive incomplete data"
            ))
        
        # Added properties
        added_props = new_prop_names - old_prop_names
        for prop_name in added_props:
            if prop_name in new_required:
                # This is handled separately in required field changes
                pass
            else:
                self.report.add_change(Change(
                    change_type=ChangeType.NON_BREAKING,
                    severity=ChangeSeverity.INFO,
                    category="schema",
                    path=f"{base_path}/properties",
                    message=f"New optional property '{prop_name}' added to {context}",
                    old_value=None,
                    new_value=new_props[prop_name],
                    impact_description="New property provides additional data without breaking existing clients"
                ))
        
        # Required field changes
        added_required = new_required - old_required
        removed_required = old_required - new_required
        
        for prop_name in added_required:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.CRITICAL,
                category="schema",
                path=f"{base_path}/properties",
                message=f"Property '{prop_name}' is now required in {context}",
                old_value=False,
                new_value=True,
                migration_guide=f"Ensure '{prop_name}' is always provided when sending {context}",
                impact_description="Clients not providing this property will receive validation errors"
            ))
        
        for prop_name in removed_required:
            self.report.add_change(Change(
                change_type=ChangeType.NON_BREAKING,
                severity=ChangeSeverity.INFO,
                category="schema",
                path=f"{base_path}/properties",
                message=f"Property '{prop_name}' is no longer required in {context}",
                old_value=True,
                new_value=False,
                impact_description="Property is now optional, providing more flexibility"
            ))
        
        # Modified properties
        common_props = old_prop_names & new_prop_names
        for prop_name in common_props:
            old_prop = old_props[prop_name]
            new_prop = new_props[prop_name]
            if old_prop != new_prop:
                self._compare_schemas(f"{base_path}/properties/{prop_name}", 
                                    old_prop, new_prop, f"{context}.{prop_name}")
    
    def _compare_security_requirements(self, base_path: str, old_security: Optional[List], 
                                     new_security: Optional[List]) -> None:
        """Compare security requirements."""
        # Simplified security comparison - could be expanded
        if old_security != new_security:
            severity = ChangeSeverity.HIGH if new_security else ChangeSeverity.CRITICAL
            change_type = ChangeType.BREAKING
            
            if old_security is None and new_security is not None:
                message = "Security requirements added"
                migration_guide = "Ensure proper authentication/authorization when calling this endpoint"
                impact = "Endpoint now requires authentication"
            elif old_security is not None and new_security is None:
                message = "Security requirements removed"
                migration_guide = "Authentication is no longer required for this endpoint"
                impact = "Endpoint is now publicly accessible"
                severity = ChangeSeverity.MEDIUM  # Less severe, more permissive
            else:
                message = "Security requirements modified"
                migration_guide = "Update authentication/authorization method for this endpoint"
                impact = "Different authentication method required"
            
            self.report.add_change(Change(
                change_type=change_type,
                severity=severity,
                category="security",
                path=f"{base_path}/security",
                message=message,
                old_value=old_security,
                new_value=new_security,
                migration_guide=migration_guide,
                impact_description=impact
            ))
    
    def _compare_components_section(self) -> None:
        """Compare components sections."""
        old_components = self.old_spec.get('components', {})
        new_components = self.new_spec.get('components', {})
        
        # Compare schemas
        old_schemas = old_components.get('schemas', {})
        new_schemas = new_components.get('schemas', {})
        
        old_schema_names = set(old_schemas.keys())
        new_schema_names = set(new_schemas.keys())
        
        # Removed schemas
        removed_schemas = old_schema_names - new_schema_names
        for schema_name in removed_schemas:
            self.report.add_change(Change(
                change_type=ChangeType.BREAKING,
                severity=ChangeSeverity.HIGH,
                category="components",
                path=f"/components/schemas/{schema_name}",
                message=f"Schema '{schema_name}' removed from components",
                old_value=old_schemas[schema_name],
                new_value=None,
                migration_guide=f"Remove references to schema '{schema_name}' or use alternative schemas",
                impact_description="References to this schema will fail validation"
            ))
        
        # Added schemas
        added_schemas = new_schema_names - old_schema_names
        for schema_name in added_schemas:
            self.report.add_change(Change(
                change_type=ChangeType.ENHANCEMENT,
                severity=ChangeSeverity.INFO,
                category="components",
                path=f"/components/schemas/{schema_name}",
                message=f"New schema '{schema_name}' added to components",
                old_value=None,
                new_value=new_schemas[schema_name],
                impact_description="New reusable schema available"
            ))
        
        # Modified schemas
        common_schemas = old_schema_names & new_schema_names
        for schema_name in common_schemas:
            old_schema = old_schemas[schema_name]
            new_schema = new_schemas[schema_name]
            if old_schema != new_schema:
                self._compare_schemas(f"/components/schemas/{schema_name}", 
                                    old_schema, new_schema, f"schema '{schema_name}'")
    
    def _compare_security_section(self) -> None:
        """Compare security definitions."""
        old_security_schemes = self.old_spec.get('components', {}).get('securitySchemes', {})
        new_security_schemes = self.new_spec.get('components', {}).get('securitySchemes', {})
        
        if old_security_schemes != new_security_schemes:
            # Simplified comparison - could be more detailed
            self.report.add_change(Change(
                change_type=ChangeType.POTENTIALLY_BREAKING,
                severity=ChangeSeverity.MEDIUM,
                category="security",
                path="/components/securitySchemes",
                message="Security scheme definitions changed",
                old_value=old_security_schemes,
                new_value=new_security_schemes,
                migration_guide="Review authentication implementation for compatibility with new security schemes",
                impact_description="Authentication mechanisms may have changed"
            ))
    
    def _generate_endpoint_removal_migration(self, removed_path: str, method: str, 
                                           remaining_paths: Dict[str, Any]) -> str:
        """Generate migration guide for removed endpoints."""
        # Look for similar endpoints
        similar_paths = []
        path_segments = removed_path.strip('/').split('/')
        
        for existing_path in remaining_paths.keys():
            existing_segments = existing_path.strip('/').split('/')
            if len(existing_segments) == len(path_segments):
                # Check similarity
                similarity = sum(1 for i, seg in enumerate(path_segments) 
                               if i < len(existing_segments) and seg == existing_segments[i])
                if similarity >= len(path_segments) * 0.5:  # At least 50% similar
                    similar_paths.append(existing_path)
        
        if similar_paths:
            return f"Consider using alternative endpoints: {', '.join(similar_paths[:3])}"
        else:
            return "No direct replacement available. Review API documentation for alternative approaches."
    
    def _generate_method_removal_migration(self, path: str, removed_method: str, 
                                         remaining_methods: Set[str]) -> str:
        """Generate migration guide for removed HTTP methods."""
        method_alternatives = {
            'get': ['head'],
            'post': ['put', 'patch'],
            'put': ['post', 'patch'],
            'patch': ['put', 'post'],
            'delete': []
        }
        
        alternatives = []
        for alt_method in method_alternatives.get(removed_method.lower(), []):
            if alt_method in remaining_methods:
                alternatives.append(alt_method.upper())
        
        if alternatives:
            return f"Use alternative methods: {', '.join(alternatives)}"
        else:
            return f"No alternative HTTP methods available for {path}"
    
    def generate_json_report(self) -> str:
        """Generate JSON format report."""
        report_data = {
            "summary": self.report.summary,
            "hasBreakingChanges": self.report.has_breaking_changes(),
            "changes": [change.to_dict() for change in self.report.changes]
        }
        
        return json.dumps(report_data, indent=2)
    
    def generate_text_report(self) -> str:
        """Generate human-readable text report."""
        lines = [
            "═══════════════════════════════════════════════════════════════",
            "                  BREAKING CHANGE ANALYSIS REPORT",
            "═══════════════════════════════════════════════════════════════",
            "",
            "SUMMARY:",
            f"  Total Changes: {self.report.summary.get('total_changes', 0)}",
            f"  🔴 Breaking Changes: {self.report.summary.get('breaking_changes', 0)}",
            f"  🟡 Potentially Breaking: {self.report.summary.get('potentially_breaking_changes', 0)}",
            f"  🟢 Non-Breaking Changes: {self.report.summary.get('non_breaking_changes', 0)}",
            f"  ✨ Enhancements: {self.report.summary.get('enhancements', 0)}",
            "",
            "SEVERITY BREAKDOWN:",
            f"  🚨 Critical: {self.report.summary.get('critical_severity', 0)}",
            f"  ⚠️  High: {self.report.summary.get('high_severity', 0)}",
            f"  ⚪ Medium: {self.report.summary.get('medium_severity', 0)}",
            f"  🔵 Low: {self.report.summary.get('low_severity', 0)}",
            f"  ℹ️  Info: {self.report.summary.get('info_severity', 0)}",
            ""
        ]
        
        if not self.report.changes:
            lines.extend([
                "🎉 No changes detected between the API versions!",
                ""
            ])
        else:
            # Group changes by type and severity
            breaking_changes = [c for c in self.report.changes if c.change_type == ChangeType.BREAKING]
            potentially_breaking = [c for c in self.report.changes if c.change_type == ChangeType.POTENTIALLY_BREAKING]
            non_breaking = [c for c in self.report.changes if c.change_type == ChangeType.NON_BREAKING]
            enhancements = [c for c in self.report.changes if c.change_type == ChangeType.ENHANCEMENT]
            
            # Breaking changes section
            if breaking_changes:
                lines.extend([
                    "🔴 BREAKING CHANGES:",
                    "═" * 60
                ])
                for change in sorted(breaking_changes, key=lambda x: x.severity.value):
                    self._add_change_to_report(lines, change)
                lines.append("")
            
            # Potentially breaking changes section
            if potentially_breaking:
                lines.extend([
                    "🟡 POTENTIALLY BREAKING CHANGES:",
                    "═" * 60
                ])
                for change in sorted(potentially_breaking, key=lambda x: x.severity.value):
                    self._add_change_to_report(lines, change)
                lines.append("")
            
            # Non-breaking changes section
            if non_breaking:
                lines.extend([
                    "🟢 NON-BREAKING CHANGES:",
                    "═" * 60
                ])
                for change in non_breaking:
                    self._add_change_to_report(lines, change)
                lines.append("")
            
            # Enhancements section
            if enhancements:
                lines.extend([
                    "✨ ENHANCEMENTS:",
                    "═" * 60
                ])
                for change in enhancements:
                    self._add_change_to_report(lines, change)
                lines.append("")
        
        # Add overall assessment
        lines.extend([
            "═══════════════════════════════════════════════════════════════",
            "OVERALL ASSESSMENT:",
            "═══════════════════════════════════════════════════════════════"
        ])
        
        if self.report.has_breaking_changes():
            breaking_count = self.report.summary.get('breaking_changes', 0)
            potentially_breaking_count = self.report.summary.get('potentially_breaking_changes', 0)
            
            if breaking_count > 0:
                lines.extend([
                    f"⛔ MAJOR VERSION BUMP REQUIRED",
                    f"   This API version contains {breaking_count} breaking changes that will",
                    f"   definitely break existing clients. A major version bump is required.",
                    ""
                ])
            elif potentially_breaking_count > 0:
                lines.extend([
                    f"⚠️  MINOR VERSION BUMP RECOMMENDED",
                    f"   This API version contains {potentially_breaking_count} potentially breaking",
                    f"   changes. Consider a minor version bump and communicate changes to clients.",
                    ""
                ])
        else:
            lines.extend([
                "✅ PATCH VERSION BUMP ACCEPTABLE",
                "   No breaking changes detected. This version is backward compatible",
                "   with existing clients.",
                ""
            ])
        
        return "\n".join(lines)
    
    def _add_change_to_report(self, lines: List[str], change: Change) -> None:
        """Add a change to the text report."""
        severity_icons = {
            ChangeSeverity.CRITICAL: "🚨",
            ChangeSeverity.HIGH: "⚠️ ",
            ChangeSeverity.MEDIUM: "⚪",
            ChangeSeverity.LOW: "🔵",
            ChangeSeverity.INFO: "ℹ️ "
        }
        
        icon = severity_icons.get(change.severity, "❓")
        
        lines.extend([
            f"{icon} {change.severity.value.upper()}: {change.message}",
            f"   Path: {change.path}",
            f"   Category: {change.category}"
        ])
        
        if change.impact_description:
            lines.append(f"   Impact: {change.impact_description}")
        
        if change.migration_guide:
            lines.append(f"   💡 Migration: {change.migration_guide}")
        
        lines.append("")


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Compare API specification versions to detect breaking changes",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python breaking_change_detector.py v1.json v2.json
  python breaking_change_detector.py --format json v1.json v2.json > changes.json
  python breaking_change_detector.py --output report.txt v1.json v2.json
        """
    )
    
    parser.add_argument(
        'old_spec',
        help='Old API specification file (JSON format)'
    )
    
    parser.add_argument(
        'new_spec',
        help='New API specification file (JSON format)'
    )
    
    parser.add_argument(
        '--format',
        choices=['text', 'json'],
        default='text',
        help='Output format (default: text)'
    )
    
    parser.add_argument(
        '--output',
        help='Output file (default: stdout)'
    )
    
    parser.add_argument(
        '--exit-on-breaking',
        action='store_true',
        help='Exit with code 1 if breaking changes are detected'
    )
    
    args = parser.parse_args()
    
    # Load specification files
    try:
        with open(args.old_spec, 'r') as f:
            old_spec = json.load(f)
    except FileNotFoundError:
        print(f"Error: Old specification file '{args.old_spec}' not found.", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.old_spec}': {e}", file=sys.stderr)
        return 1
    
    try:
        with open(args.new_spec, 'r') as f:
            new_spec = json.load(f)
    except FileNotFoundError:
        print(f"Error: New specification file '{args.new_spec}' not found.", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.new_spec}': {e}", file=sys.stderr)
        return 1
    
    # Initialize detector and compare specifications
    detector = BreakingChangeDetector()
    
    try:
        report = detector.compare_specs(old_spec, new_spec)
    except Exception as e:
        print(f"Error during comparison: {e}", file=sys.stderr)
        return 1
    
    # Generate report
    if args.format == 'json':
        output = detector.generate_json_report()
    else:
        output = detector.generate_text_report()
    
    # Write output
    if args.output:
        try:
            with open(args.output, 'w') as f:
                f.write(output)
            print(f"Breaking change report written to {args.output}")
        except IOError as e:
            print(f"Error writing to '{args.output}': {e}", file=sys.stderr)
            return 1
    else:
        print(output)
    
    # Exit with appropriate code
    if args.exit_on_breaking and report.has_breaking_changes():
        return 1
    
    return 0


if __name__ == '__main__':
    sys.exit(main())