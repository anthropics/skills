#!/usr/bin/env python3
"""
API Linter - Analyzes OpenAPI/Swagger specifications for REST conventions and best practices.

This script validates API designs against established conventions including:
- Resource naming conventions (kebab-case resources, camelCase fields)
- HTTP method usage patterns
- URL structure consistency
- Error response format standards
- Documentation completeness
- Pagination patterns
- Versioning compliance

Supports both OpenAPI JSON specifications and raw endpoint definition JSON.
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Tuple, Optional, Set
from urllib.parse import urlparse
from dataclasses import dataclass, field


@dataclass
class LintIssue:
    """Represents a linting issue found in the API specification."""
    severity: str  # 'error', 'warning', 'info'
    category: str
    message: str
    path: str
    suggestion: str = ""
    line_number: Optional[int] = None


@dataclass
class LintReport:
    """Complete linting report with issues and statistics."""
    issues: List[LintIssue] = field(default_factory=list)
    total_endpoints: int = 0
    endpoints_with_issues: int = 0
    score: float = 0.0
    
    def add_issue(self, issue: LintIssue) -> None:
        """Add an issue to the report."""
        self.issues.append(issue)
    
    def get_issues_by_severity(self) -> Dict[str, List[LintIssue]]:
        """Group issues by severity level."""
        grouped = {'error': [], 'warning': [], 'info': []}
        for issue in self.issues:
            if issue.severity in grouped:
                grouped[issue.severity].append(issue)
        return grouped
    
    def calculate_score(self) -> float:
        """Calculate overall API quality score (0-100)."""
        if self.total_endpoints == 0:
            return 100.0
        
        error_penalty = len([i for i in self.issues if i.severity == 'error']) * 10
        warning_penalty = len([i for i in self.issues if i.severity == 'warning']) * 3
        info_penalty = len([i for i in self.issues if i.severity == 'info']) * 1
        
        total_penalty = error_penalty + warning_penalty + info_penalty
        base_score = 100.0
        
        # Penalty per endpoint to normalize across API sizes
        penalty_per_endpoint = total_penalty / self.total_endpoints if self.total_endpoints > 0 else total_penalty
        
        self.score = max(0.0, base_score - penalty_per_endpoint)
        return self.score


class APILinter:
    """Main API linting engine."""
    
    def __init__(self):
        self.report = LintReport()
        self.openapi_spec: Optional[Dict] = None
        self.raw_endpoints: Optional[Dict] = None
        
        # Regex patterns for naming conventions
        self.kebab_case_pattern = re.compile(r'^[a-z]+(?:-[a-z0-9]+)*$')
        self.camel_case_pattern = re.compile(r'^[a-z][a-zA-Z0-9]*$')
        self.snake_case_pattern = re.compile(r'^[a-z]+(?:_[a-z0-9]+)*$')
        self.pascal_case_pattern = re.compile(r'^[A-Z][a-zA-Z0-9]*$')
        
        # Standard HTTP methods
        self.http_methods = {'GET', 'POST', 'PUT', 'PATCH', 'DELETE', 'HEAD', 'OPTIONS'}
        
        # Standard HTTP status codes by method
        self.standard_status_codes = {
            'GET': {200, 304, 404},
            'POST': {200, 201, 400, 409, 422},
            'PUT': {200, 204, 400, 404, 409},
            'PATCH': {200, 204, 400, 404, 409},
            'DELETE': {200, 204, 404},
            'HEAD': {200, 404},
            'OPTIONS': {200}
        }
        
        # Common error status codes
        self.common_error_codes = {400, 401, 403, 404, 405, 409, 422, 429, 500, 502, 503}

    def lint_openapi_spec(self, spec: Dict[str, Any]) -> LintReport:
        """Lint an OpenAPI/Swagger specification."""
        self.openapi_spec = spec
        self.report = LintReport()
        
        # Basic structure validation
        self._validate_openapi_structure()
        
        # Info section validation
        self._validate_info_section()
        
        # Server section validation
        self._validate_servers_section()
        
        # Paths validation (main linting logic)
        self._validate_paths_section()
        
        # Components validation
        self._validate_components_section()
        
        # Security validation
        self._validate_security_section()
        
        # Calculate final score
        self.report.calculate_score()
        
        return self.report

    def lint_raw_endpoints(self, endpoints: Dict[str, Any]) -> LintReport:
        """Lint raw endpoint definitions."""
        self.raw_endpoints = endpoints
        self.report = LintReport()
        
        # Validate raw endpoint structure
        self._validate_raw_endpoint_structure()
        
        # Lint each endpoint
        for endpoint_path, endpoint_data in endpoints.get('endpoints', {}).items():
            self._lint_raw_endpoint(endpoint_path, endpoint_data)
        
        self.report.calculate_score()
        return self.report

    def _validate_openapi_structure(self) -> None:
        """Validate basic OpenAPI document structure."""
        required_fields = ['openapi', 'info', 'paths']
        
        for field in required_fields:
            if field not in self.openapi_spec:
                self.report.add_issue(LintIssue(
                    severity='error',
                    category='structure',
                    message=f"Missing required field: {field}",
                    path=f"/{field}",
                    suggestion=f"Add the '{field}' field to the root of your OpenAPI specification"
                ))

    def _validate_info_section(self) -> None:
        """Validate the info section of OpenAPI spec."""
        if 'info' not in self.openapi_spec:
            return
            
        info = self.openapi_spec['info']
        required_info_fields = ['title', 'version']
        recommended_info_fields = ['description', 'contact']
        
        for field in required_info_fields:
            if field not in info:
                self.report.add_issue(LintIssue(
                    severity='error',
                    category='documentation',
                    message=f"Missing required info field: {field}",
                    path=f"/info/{field}",
                    suggestion=f"Add a '{field}' field to the info section"
                ))
        
        for field in recommended_info_fields:
            if field not in info:
                self.report.add_issue(LintIssue(
                    severity='warning',
                    category='documentation',
                    message=f"Missing recommended info field: {field}",
                    path=f"/info/{field}",
                    suggestion=f"Consider adding a '{field}' field to improve API documentation"
                ))
        
        # Validate version format
        if 'version' in info:
            version = info['version']
            if not re.match(r'^\d+\.\d+(\.\d+)?(-\w+)?$', version):
                self.report.add_issue(LintIssue(
                    severity='warning',
                    category='versioning',
                    message=f"Version format '{version}' doesn't follow semantic versioning",
                    path="/info/version",
                    suggestion="Use semantic versioning format (e.g., '1.0.0', '2.1.3-beta')"
                ))

    def _validate_servers_section(self) -> None:
        """Validate the servers section."""
        if 'servers' not in self.openapi_spec:
            self.report.add_issue(LintIssue(
                severity='warning',
                category='configuration',
                message="Missing servers section",
                path="/servers",
                suggestion="Add a servers section to specify API base URLs"
            ))
            return
        
        servers = self.openapi_spec['servers']
        if not isinstance(servers, list) or len(servers) == 0:
            self.report.add_issue(LintIssue(
                severity='warning',
                category='configuration',
                message="Empty servers section",
                path="/servers",
                suggestion="Add at least one server URL"
            ))

    def _validate_paths_section(self) -> None:
        """Validate all API paths and operations."""
        if 'paths' not in self.openapi_spec:
            return
            
        paths = self.openapi_spec['paths']
        if not paths:
            self.report.add_issue(LintIssue(
                severity='error',
                category='structure',
                message="No paths defined in API specification",
                path="/paths",
                suggestion="Define at least one API endpoint"
            ))
            return
        
        self.report.total_endpoints = sum(
            len([method for method in path_obj.keys() if method.upper() in self.http_methods])
            for path_obj in paths.values() if isinstance(path_obj, dict)
        )
        
        endpoints_with_issues = set()
        
        for path, path_obj in paths.items():
            if not isinstance(path_obj, dict):
                continue
                
            # Validate path structure
            path_issues = self._validate_path_structure(path)
            if path_issues:
                endpoints_with_issues.add(path)
            
            # Validate each operation in the path
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                    
                operation_issues = self._validate_operation(path, method.upper(), operation)
                if operation_issues:
                    endpoints_with_issues.add(path)
        
        self.report.endpoints_with_issues = len(endpoints_with_issues)

    def _validate_path_structure(self, path: str) -> bool:
        """Validate REST path structure and naming conventions."""
        has_issues = False
        
        # Check if path starts with slash
        if not path.startswith('/'):
            self.report.add_issue(LintIssue(
                severity='error',
                category='url_structure',
                message=f"Path must start with '/' character: {path}",
                path=f"/paths/{path}",
                suggestion=f"Change '{path}' to '/{path.lstrip('/')}'"
            ))
            has_issues = True
        
        # Split path into segments
        segments = [seg for seg in path.split('/') if seg]
        
        # Check for empty segments (double slashes)
        if '//' in path:
            self.report.add_issue(LintIssue(
                severity='error',
                category='url_structure',
                message=f"Path contains empty segments: {path}",
                path=f"/paths/{path}",
                suggestion="Remove double slashes from the path"
            ))
            has_issues = True
        
        # Validate each segment
        for i, segment in enumerate(segments):
            # Skip parameter segments
            if segment.startswith('{') and segment.endswith('}'):
                # Validate parameter naming
                param_name = segment[1:-1]
                if not self.camel_case_pattern.match(param_name) and not self.kebab_case_pattern.match(param_name):
                    self.report.add_issue(LintIssue(
                        severity='warning',
                        category='naming',
                        message=f"Path parameter '{param_name}' should use camelCase or kebab-case",
                        path=f"/paths/{path}",
                        suggestion=f"Use camelCase (e.g., 'userId') or kebab-case (e.g., 'user-id')"
                    ))
                    has_issues = True
                continue
            
            # Check for resource naming conventions
            if not self.kebab_case_pattern.match(segment):
                # Allow version segments like 'v1', 'v2'
                if not re.match(r'^v\d+$', segment):
                    self.report.add_issue(LintIssue(
                        severity='warning',
                        category='naming',
                        message=f"Resource segment '{segment}' should use kebab-case",
                        path=f"/paths/{path}",
                        suggestion=f"Use kebab-case for '{segment}' (e.g., 'user-profiles', 'order-items')"
                    ))
                    has_issues = True
            
            # Check for verb usage in URLs (anti-pattern)
            common_verbs = {'get', 'post', 'put', 'delete', 'create', 'update', 'remove', 'add'}
            if segment.lower() in common_verbs:
                self.report.add_issue(LintIssue(
                    severity='warning',
                    category='rest_conventions',
                    message=f"Avoid verbs in URLs: '{segment}' in {path}",
                    path=f"/paths/{path}",
                    suggestion="Use HTTP methods instead of verbs in URLs. Use nouns for resources."
                ))
                has_issues = True
        
        # Check path depth (avoid over-nesting)
        if len(segments) > 6:
            self.report.add_issue(LintIssue(
                severity='warning',
                category='url_structure',
                message=f"Path has excessive nesting ({len(segments)} levels): {path}",
                path=f"/paths/{path}",
                suggestion="Consider flattening the resource hierarchy or using query parameters"
            ))
            has_issues = True
        
        # Check for consistent versioning
        if any('v' + str(i) in segments for i in range(1, 10)):
            version_segments = [seg for seg in segments if re.match(r'^v\d+$', seg)]
            if len(version_segments) > 1:
                self.report.add_issue(LintIssue(
                    severity='error',
                    category='versioning',
                    message=f"Multiple version segments in path: {path}",
                    path=f"/paths/{path}",
                    suggestion="Use only one version segment per path"
                ))
                has_issues = True
        
        return has_issues

    def _validate_operation(self, path: str, method: str, operation: Dict[str, Any]) -> bool:
        """Validate individual operation (HTTP method + path combination)."""
        has_issues = False
        operation_path = f"/paths/{path}/{method.lower()}"
        
        # Check for required operation fields
        if 'responses' not in operation:
            self.report.add_issue(LintIssue(
                severity='error',
                category='structure',
                message=f"Missing responses section for {method} {path}",
                path=f"{operation_path}/responses",
                suggestion="Define expected responses for this operation"
            ))
            has_issues = True
        
        # Check for operation documentation
        if 'summary' not in operation:
            self.report.add_issue(LintIssue(
                severity='warning',
                category='documentation',
                message=f"Missing summary for {method} {path}",
                path=f"{operation_path}/summary",
                suggestion="Add a brief summary describing what this operation does"
            ))
            has_issues = True
        
        if 'description' not in operation:
            self.report.add_issue(LintIssue(
                severity='info',
                category='documentation',
                message=f"Missing description for {method} {path}",
                path=f"{operation_path}/description",
                suggestion="Add a detailed description for better API documentation"
            ))
            has_issues = True
        
        # Validate HTTP method usage patterns
        method_issues = self._validate_http_method_usage(path, method, operation)
        if method_issues:
            has_issues = True
        
        # Validate responses
        if 'responses' in operation:
            response_issues = self._validate_responses(path, method, operation['responses'])
            if response_issues:
                has_issues = True
        
        # Validate parameters
        if 'parameters' in operation:
            param_issues = self._validate_parameters(path, method, operation['parameters'])
            if param_issues:
                has_issues = True
        
        # Validate request body
        if 'requestBody' in operation:
            body_issues = self._validate_request_body(path, method, operation['requestBody'])
            if body_issues:
                has_issues = True
        
        return has_issues

    def _validate_http_method_usage(self, path: str, method: str, operation: Dict[str, Any]) -> bool:
        """Validate proper HTTP method usage patterns."""
        has_issues = False
        
        # GET requests should not have request body
        if method == 'GET' and 'requestBody' in operation:
            self.report.add_issue(LintIssue(
                severity='error',
                category='rest_conventions',
                message=f"GET request should not have request body: {method} {path}",
                path=f"/paths/{path}/{method.lower()}/requestBody",
                suggestion="Remove requestBody from GET request or use POST if body is needed"
            ))
            has_issues = True
        
        # DELETE requests typically should not have request body
        if method == 'DELETE' and 'requestBody' in operation:
            self.report.add_issue(LintIssue(
                severity='warning',
                category='rest_conventions',
                message=f"DELETE request typically should not have request body: {method} {path}",
                path=f"/paths/{path}/{method.lower()}/requestBody",
                suggestion="Consider using query parameters or path parameters instead"
            ))
            has_issues = True
        
        # POST/PUT/PATCH should typically have request body (except for actions)
        if method in ['POST', 'PUT', 'PATCH'] and 'requestBody' not in operation:
            # Check if this is an action endpoint
            if not any(action in path.lower() for action in ['activate', 'deactivate', 'reset', 'confirm']):
                self.report.add_issue(LintIssue(
                    severity='info',
                    category='rest_conventions',
                    message=f"{method} request typically should have request body: {method} {path}",
                    path=f"/paths/{path}/{method.lower()}",
                    suggestion=f"Consider adding requestBody for {method} operation or use GET if no data is being sent"
                ))
                has_issues = True
        
        return has_issues

    def _validate_responses(self, path: str, method: str, responses: Dict[str, Any]) -> bool:
        """Validate response definitions."""
        has_issues = False
        
        # Check for success response
        success_codes = {'200', '201', '202', '204'}
        has_success = any(code in responses for code in success_codes)
        
        if not has_success:
            self.report.add_issue(LintIssue(
                severity='error',
                category='responses',
                message=f"Missing success response for {method} {path}",
                path=f"/paths/{path}/{method.lower()}/responses",
                suggestion="Define at least one success response (200, 201, 202, or 204)"
            ))
            has_issues = True
        
        # Check for error responses
        has_error_responses = any(code.startswith('4') or code.startswith('5') for code in responses.keys())
        
        if not has_error_responses:
            self.report.add_issue(LintIssue(
                severity='warning',
                category='responses',
                message=f"Missing error responses for {method} {path}",
                path=f"/paths/{path}/{method.lower()}/responses",
                suggestion="Define common error responses (400, 404, 500, etc.)"
            ))
            has_issues = True
        
        # Validate individual response codes
        for status_code, response in responses.items():
            if status_code == 'default':
                continue
                
            try:
                code_int = int(status_code)
            except ValueError:
                self.report.add_issue(LintIssue(
                    severity='error',
                    category='responses',
                    message=f"Invalid status code '{status_code}' for {method} {path}",
                    path=f"/paths/{path}/{method.lower()}/responses/{status_code}",
                    suggestion="Use valid HTTP status codes (e.g., 200, 404, 500)"
                ))
                has_issues = True
                continue
            
            # Check if status code is appropriate for the method
            expected_codes = self.standard_status_codes.get(method, set())
            common_codes = {400, 401, 403, 404, 429, 500}  # Always acceptable
            
            if expected_codes and code_int not in expected_codes and code_int not in common_codes:
                self.report.add_issue(LintIssue(
                    severity='info',
                    category='responses',
                    message=f"Uncommon status code {status_code} for {method} {path}",
                    path=f"/paths/{path}/{method.lower()}/responses/{status_code}",
                    suggestion=f"Consider using standard codes for {method}: {sorted(expected_codes)}"
                ))
                has_issues = True
        
        return has_issues

    def _validate_parameters(self, path: str, method: str, parameters: List[Dict[str, Any]]) -> bool:
        """Validate parameter definitions."""
        has_issues = False
        
        for i, param in enumerate(parameters):
            param_path = f"/paths/{path}/{method.lower()}/parameters[{i}]"
            
            # Check required fields
            if 'name' not in param:
                self.report.add_issue(LintIssue(
                    severity='error',
                    category='parameters',
                    message=f"Parameter missing name field in {method} {path}",
                    path=f"{param_path}/name",
                    suggestion="Add a name field to the parameter"
                ))
                has_issues = True
                continue
            
            if 'in' not in param:
                self.report.add_issue(LintIssue(
                    severity='error',
                    category='parameters',
                    message=f"Parameter '{param['name']}' missing 'in' field in {method} {path}",
                    path=f"{param_path}/in",
                    suggestion="Specify parameter location (query, path, header, cookie)"
                ))
                has_issues = True
            
            # Validate parameter naming
            param_name = param['name']
            param_location = param.get('in', '')
            
            if param_location == 'query':
                # Query parameters should use camelCase or kebab-case
                if not self.camel_case_pattern.match(param_name) and not self.kebab_case_pattern.match(param_name):
                    self.report.add_issue(LintIssue(
                        severity='warning',
                        category='naming',
                        message=f"Query parameter '{param_name}' should use camelCase or kebab-case in {method} {path}",
                        path=f"{param_path}/name",
                        suggestion="Use camelCase (e.g., 'pageSize') or kebab-case (e.g., 'page-size')"
                    ))
                    has_issues = True
            
            elif param_location == 'path':
                # Path parameters should use camelCase or kebab-case
                if not self.camel_case_pattern.match(param_name) and not self.kebab_case_pattern.match(param_name):
                    self.report.add_issue(LintIssue(
                        severity='warning',
                        category='naming',
                        message=f"Path parameter '{param_name}' should use camelCase or kebab-case in {method} {path}",
                        path=f"{param_path}/name",
                        suggestion="Use camelCase (e.g., 'userId') or kebab-case (e.g., 'user-id')"
                    ))
                    has_issues = True
                
                # Path parameters must be required
                if not param.get('required', False):
                    self.report.add_issue(LintIssue(
                        severity='error',
                        category='parameters',
                        message=f"Path parameter '{param_name}' must be required in {method} {path}",
                        path=f"{param_path}/required",
                        suggestion="Set required: true for path parameters"
                    ))
                    has_issues = True
        
        return has_issues

    def _validate_request_body(self, path: str, method: str, request_body: Dict[str, Any]) -> bool:
        """Validate request body definition."""
        has_issues = False
        
        if 'content' not in request_body:
            self.report.add_issue(LintIssue(
                severity='error',
                category='request_body',
                message=f"Request body missing content for {method} {path}",
                path=f"/paths/{path}/{method.lower()}/requestBody/content",
                suggestion="Define content types for the request body"
            ))
            has_issues = True
        
        return has_issues

    def _validate_components_section(self) -> None:
        """Validate the components section."""
        if 'components' not in self.openapi_spec:
            self.report.add_issue(LintIssue(
                severity='info',
                category='structure',
                message="Missing components section",
                path="/components",
                suggestion="Consider defining reusable components (schemas, responses, parameters)"
            ))
            return
        
        components = self.openapi_spec['components']
        
        # Validate schemas
        if 'schemas' in components:
            self._validate_schemas(components['schemas'])

    def _validate_schemas(self, schemas: Dict[str, Any]) -> None:
        """Validate schema definitions."""
        for schema_name, schema in schemas.items():
            # Check schema naming (should be PascalCase)
            if not self.pascal_case_pattern.match(schema_name):
                self.report.add_issue(LintIssue(
                    severity='warning',
                    category='naming',
                    message=f"Schema name '{schema_name}' should use PascalCase",
                    path=f"/components/schemas/{schema_name}",
                    suggestion=f"Use PascalCase for schema names (e.g., 'UserProfile', 'OrderItem')"
                ))
            
            # Validate schema properties
            if isinstance(schema, dict) and 'properties' in schema:
                self._validate_schema_properties(schema_name, schema['properties'])

    def _validate_schema_properties(self, schema_name: str, properties: Dict[str, Any]) -> None:
        """Validate schema property naming."""
        for prop_name, prop_def in properties.items():
            # Properties should use camelCase
            if not self.camel_case_pattern.match(prop_name):
                self.report.add_issue(LintIssue(
                    severity='warning',
                    category='naming',
                    message=f"Property '{prop_name}' in schema '{schema_name}' should use camelCase",
                    path=f"/components/schemas/{schema_name}/properties/{prop_name}",
                    suggestion="Use camelCase for property names (e.g., 'firstName', 'createdAt')"
                ))

    def _validate_security_section(self) -> None:
        """Validate security definitions."""
        if 'security' not in self.openapi_spec and 'components' not in self.openapi_spec:
            self.report.add_issue(LintIssue(
                severity='warning',
                category='security',
                message="No security configuration found",
                path="/security",
                suggestion="Define security schemes and apply them to operations"
            ))

    def _validate_raw_endpoint_structure(self) -> None:
        """Validate structure of raw endpoint definitions."""
        if 'endpoints' not in self.raw_endpoints:
            self.report.add_issue(LintIssue(
                severity='error',
                category='structure',
                message="Missing 'endpoints' field in raw endpoint definition",
                path="/endpoints",
                suggestion="Provide an 'endpoints' object containing endpoint definitions"
            ))
            return
        
        endpoints = self.raw_endpoints['endpoints']
        self.report.total_endpoints = len(endpoints)

    def _lint_raw_endpoint(self, path: str, endpoint_data: Dict[str, Any]) -> None:
        """Lint individual raw endpoint definition."""
        # Validate path structure
        self._validate_path_structure(path)
        
        # Check for required fields
        if 'method' not in endpoint_data:
            self.report.add_issue(LintIssue(
                severity='error',
                category='structure',
                message=f"Missing method field for endpoint {path}",
                path=f"/endpoints/{path}/method",
                suggestion="Specify HTTP method (GET, POST, PUT, PATCH, DELETE)"
            ))
            return
        
        method = endpoint_data['method'].upper()
        if method not in self.http_methods:
            self.report.add_issue(LintIssue(
                severity='error',
                category='structure',
                message=f"Invalid HTTP method '{method}' for endpoint {path}",
                path=f"/endpoints/{path}/method",
                suggestion=f"Use valid HTTP methods: {', '.join(sorted(self.http_methods))}"
            ))

    def generate_json_report(self) -> str:
        """Generate JSON format report."""
        issues_by_severity = self.report.get_issues_by_severity()
        
        report_data = {
            "summary": {
                "total_endpoints": self.report.total_endpoints,
                "endpoints_with_issues": self.report.endpoints_with_issues,
                "total_issues": len(self.report.issues),
                "errors": len(issues_by_severity['error']),
                "warnings": len(issues_by_severity['warning']),
                "info": len(issues_by_severity['info']),
                "score": round(self.report.score, 2)
            },
            "issues": []
        }
        
        for issue in self.report.issues:
            report_data["issues"].append({
                "severity": issue.severity,
                "category": issue.category,
                "message": issue.message,
                "path": issue.path,
                "suggestion": issue.suggestion
            })
        
        return json.dumps(report_data, indent=2)

    def generate_text_report(self) -> str:
        """Generate human-readable text report."""
        issues_by_severity = self.report.get_issues_by_severity()
        
        report_lines = [
            "═══════════════════════════════════════════════════════════════",
            "                      API LINTING REPORT",
            "═══════════════════════════════════════════════════════════════",
            "",
            "SUMMARY:",
            f"  Total Endpoints: {self.report.total_endpoints}",
            f"  Endpoints with Issues: {self.report.endpoints_with_issues}",
            f"  Overall Score: {self.report.score:.1f}/100.0",
            "",
            "ISSUE BREAKDOWN:",
            f"  🔴 Errors: {len(issues_by_severity['error'])}",
            f"  🟡 Warnings: {len(issues_by_severity['warning'])}",
            f"  ℹ️  Info: {len(issues_by_severity['info'])}",
            "",
        ]
        
        if not self.report.issues:
            report_lines.extend([
                "🎉 Congratulations! No issues found in your API specification.",
                ""
            ])
        else:
            # Group issues by category
            issues_by_category = {}
            for issue in self.report.issues:
                if issue.category not in issues_by_category:
                    issues_by_category[issue.category] = []
                issues_by_category[issue.category].append(issue)
            
            for category, issues in issues_by_category.items():
                report_lines.append(f"{'═' * 60}")
                report_lines.append(f"CATEGORY: {category.upper().replace('_', ' ')}")
                report_lines.append(f"{'═' * 60}")
                
                for issue in issues:
                    severity_icon = {"error": "🔴", "warning": "🟡", "info": "ℹ️"}[issue.severity]
                    
                    report_lines.extend([
                        f"{severity_icon} {issue.severity.upper()}: {issue.message}",
                        f"   Path: {issue.path}",
                    ])
                    
                    if issue.suggestion:
                        report_lines.append(f"   💡 Suggestion: {issue.suggestion}")
                    
                    report_lines.append("")
        
        # Add scoring breakdown
        report_lines.extend([
            "═══════════════════════════════════════════════════════════════",
            "SCORING DETAILS:",
            "═══════════════════════════════════════════════════════════════",
            f"Base Score: 100.0",
            f"Errors Penalty: -{len(issues_by_severity['error']) * 10} (10 points per error)",
            f"Warnings Penalty: -{len(issues_by_severity['warning']) * 3} (3 points per warning)",
            f"Info Penalty: -{len(issues_by_severity['info']) * 1} (1 point per info)",
            f"Final Score: {self.report.score:.1f}/100.0",
            ""
        ])
        
        # Add recommendations based on score
        if self.report.score >= 90:
            report_lines.append("🏆 Excellent! Your API design follows best practices.")
        elif self.report.score >= 80:
            report_lines.append("✅ Good API design with minor areas for improvement.")
        elif self.report.score >= 70:
            report_lines.append("⚠️  Fair API design. Consider addressing warnings and errors.")
        elif self.report.score >= 50:
            report_lines.append("❌ Poor API design. Multiple issues need attention.")
        else:
            report_lines.append("🚨 Critical API design issues. Immediate attention required.")
        
        return "\n".join(report_lines)


# Embedded sample OpenAPI spec — intentionally imperfect (a verb in a URL, a
# snake_case property) so --sample produces a representative report.
SAMPLE_OPENAPI_SPEC = {
    "openapi": "3.0.0",
    "info": {"title": "Sample API", "version": "1.0.0"},
    "servers": [{"url": "https://api.example.com"}],
    "paths": {
        "/user-profiles/{userId}": {
            "get": {
                "summary": "Get a user profile",
                "responses": {"200": {"description": "OK"}, "404": {"description": "Not found"}},
                "parameters": [{"name": "userId", "in": "path", "required": True}],
            }
        },
        "/user-profiles/create": {
            "post": {
                "summary": "Create a user profile (verb-in-URL anti-pattern)",
                "responses": {"201": {"description": "Created"}},
            }
        },
    },
    "components": {
        "schemas": {
            "UserProfile": {"properties": {"first_name": {"type": "string"}}}
        }
    },
}


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze OpenAPI/Swagger specifications for REST conventions and best practices",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python api_linter.py openapi.json
  python api_linter.py --format json openapi.json > report.json
  python api_linter.py --raw-endpoints endpoints.json
  python api_linter.py --sample --format json
        """
    )

    parser.add_argument(
        'input_file',
        nargs='?',
        help='Input file: OpenAPI/Swagger JSON file or raw endpoints JSON'
    )

    parser.add_argument(
        '--sample',
        action='store_true',
        help='Lint an embedded sample OpenAPI spec (no input file needed)'
    )
    
    parser.add_argument(
        '--format',
        choices=['text', 'json'],
        default='text',
        help='Output format (default: text)'
    )
    
    parser.add_argument(
        '--raw-endpoints',
        action='store_true',
        help='Treat input as raw endpoint definitions instead of OpenAPI spec'
    )
    
    parser.add_argument(
        '--output',
        help='Output file (default: stdout)'
    )
    
    args = parser.parse_args()

    # Load input data — from the embedded sample or the input file
    if args.sample:
        input_data = SAMPLE_OPENAPI_SPEC
    else:
        if not args.input_file:
            parser.error("input_file is required (or use --sample)")
        try:
            with open(args.input_file, 'r') as f:
                input_data = json.load(f)
        except FileNotFoundError:
            print(f"Error: Input file '{args.input_file}' not found.", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in '{args.input_file}': {e}", file=sys.stderr)
            return 1
    
    # Initialize linter and run analysis
    linter = APILinter()
    
    try:
        if args.raw_endpoints:
            report = linter.lint_raw_endpoints(input_data)
        else:
            report = linter.lint_openapi_spec(input_data)
    except Exception as e:
        print(f"Error during linting: {e}", file=sys.stderr)
        return 1
    
    # Generate report
    if args.format == 'json':
        output = linter.generate_json_report()
    else:
        output = linter.generate_text_report()
    
    # Write output
    if args.output:
        try:
            with open(args.output, 'w') as f:
                f.write(output)
            print(f"Report written to {args.output}")
        except IOError as e:
            print(f"Error writing to '{args.output}': {e}", file=sys.stderr)
            return 1
    else:
        print(output)
    
    # Return appropriate exit code
    error_count = len([i for i in report.issues if i.severity == 'error'])
    return 1 if error_count > 0 else 0


if __name__ == '__main__':
    sys.exit(main())