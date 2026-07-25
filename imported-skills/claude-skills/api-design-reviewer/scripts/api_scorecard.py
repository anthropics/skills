#!/usr/bin/env python3
"""
API Scorecard - Comprehensive API design quality assessment tool.

This script evaluates API designs across multiple dimensions and generates
a detailed scorecard with letter grades and improvement recommendations.

Scoring Dimensions:
- Consistency (30%): Naming conventions, response patterns, structural consistency
- Documentation (20%): Completeness and clarity of API documentation  
- Security (20%): Authentication, authorization, and security best practices
- Usability (15%): Ease of use, discoverability, and developer experience
- Performance (15%): Caching, pagination, and efficiency patterns

Generates letter grades (A-F) with detailed breakdowns and actionable recommendations.
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, field
from enum import Enum
import math


class ScoreCategory(Enum):
    """Scoring categories."""
    CONSISTENCY = "consistency"
    DOCUMENTATION = "documentation"
    SECURITY = "security"
    USABILITY = "usability"
    PERFORMANCE = "performance"


@dataclass
class CategoryScore:
    """Score for a specific category."""
    category: ScoreCategory
    score: float  # 0-100
    max_score: float  # Usually 100
    weight: float  # Percentage weight in overall score
    issues: List[str] = field(default_factory=list)
    recommendations: List[str] = field(default_factory=list)
    
    @property
    def letter_grade(self) -> str:
        """Convert score to letter grade."""
        if self.score >= 90:
            return "A"
        elif self.score >= 80:
            return "B"
        elif self.score >= 70:
            return "C"
        elif self.score >= 60:
            return "D"
        else:
            return "F"
    
    @property
    def weighted_score(self) -> float:
        """Calculate weighted contribution to overall score."""
        return (self.score / 100.0) * self.weight


@dataclass
class APIScorecard:
    """Complete API scorecard with all category scores."""
    category_scores: Dict[ScoreCategory, CategoryScore] = field(default_factory=dict)
    overall_score: float = 0.0
    overall_grade: str = "F"
    total_endpoints: int = 0
    api_info: Dict[str, Any] = field(default_factory=dict)
    
    def calculate_overall_score(self) -> None:
        """Calculate overall weighted score and grade."""
        self.overall_score = sum(score.weighted_score for score in self.category_scores.values())
        
        if self.overall_score >= 90:
            self.overall_grade = "A"
        elif self.overall_score >= 80:
            self.overall_grade = "B"
        elif self.overall_score >= 70:
            self.overall_grade = "C"
        elif self.overall_score >= 60:
            self.overall_grade = "D"
        else:
            self.overall_grade = "F"
    
    def get_top_recommendations(self, limit: int = 5) -> List[str]:
        """Get top recommendations across all categories."""
        all_recommendations = []
        for category_score in self.category_scores.values():
            for rec in category_score.recommendations:
                all_recommendations.append(f"{category_score.category.value.title()}: {rec}")
        
        # Sort by category weight (highest impact first)
        weighted_recs = []
        for category_score in sorted(self.category_scores.values(), 
                                   key=lambda x: x.weight, reverse=True):
            for rec in category_score.recommendations[:2]:  # Top 2 per category
                weighted_recs.append(f"{category_score.category.value.title()}: {rec}")
        
        return weighted_recs[:limit]


class APIScoringEngine:
    """Main API scoring engine."""
    
    def __init__(self):
        self.scorecard = APIScorecard()
        self.spec: Optional[Dict] = None
        
        # Regex patterns for validation
        self.kebab_case_pattern = re.compile(r'^[a-z]+(?:-[a-z0-9]+)*$')
        self.camel_case_pattern = re.compile(r'^[a-z][a-zA-Z0-9]*$')
        self.pascal_case_pattern = re.compile(r'^[A-Z][a-zA-Z0-9]*$')
        
        # HTTP methods
        self.http_methods = {'GET', 'POST', 'PUT', 'PATCH', 'DELETE', 'HEAD', 'OPTIONS'}
        
        # Category weights (must sum to 100)
        self.category_weights = {
            ScoreCategory.CONSISTENCY: 30.0,
            ScoreCategory.DOCUMENTATION: 20.0,
            ScoreCategory.SECURITY: 20.0,
            ScoreCategory.USABILITY: 15.0,
            ScoreCategory.PERFORMANCE: 15.0
        }
    
    def score_api(self, spec: Dict[str, Any]) -> APIScorecard:
        """Generate comprehensive API scorecard."""
        self.spec = spec
        self.scorecard = APIScorecard()
        
        # Extract basic API info
        self._extract_api_info()
        
        # Score each category
        self._score_consistency()
        self._score_documentation()
        self._score_security()
        self._score_usability()
        self._score_performance()
        
        # Calculate overall score
        self.scorecard.calculate_overall_score()
        
        return self.scorecard
    
    def _extract_api_info(self) -> None:
        """Extract basic API information."""
        info = self.spec.get('info', {})
        paths = self.spec.get('paths', {})
        
        self.scorecard.api_info = {
            'title': info.get('title', 'Unknown API'),
            'version': info.get('version', ''),
            'description': info.get('description', ''),
            'total_paths': len(paths),
            'openapi_version': self.spec.get('openapi', self.spec.get('swagger', ''))
        }
        
        # Count total endpoints
        endpoint_count = 0
        for path_obj in paths.values():
            if isinstance(path_obj, dict):
                endpoint_count += len([m for m in path_obj.keys() 
                                     if m.upper() in self.http_methods])
        
        self.scorecard.total_endpoints = endpoint_count
    
    def _score_consistency(self) -> None:
        """Score API consistency (30% weight)."""
        category = ScoreCategory.CONSISTENCY
        score = CategoryScore(
            category=category,
            score=0.0,
            max_score=100.0,
            weight=self.category_weights[category]
        )
        
        consistency_checks = [
            self._check_naming_consistency(),
            self._check_response_consistency(),
            self._check_error_format_consistency(),
            self._check_parameter_consistency(),
            self._check_url_structure_consistency(),
            self._check_http_method_consistency(),
            self._check_status_code_consistency()
        ]
        
        # Average the consistency scores
        valid_scores = [s for s in consistency_checks if s is not None]
        if valid_scores:
            score.score = sum(valid_scores) / len(valid_scores)
        
        # Add specific recommendations based on low scores
        if score.score < 70:
            score.recommendations.extend([
                "Review naming conventions across all endpoints and schemas",
                "Standardize response formats and error structures",
                "Ensure consistent HTTP method usage patterns"
            ])
        elif score.score < 85:
            score.recommendations.extend([
                "Minor consistency improvements needed in naming or response formats",
                "Consider creating API design guidelines document"
            ])
        
        self.scorecard.category_scores[category] = score
    
    def _check_naming_consistency(self) -> float:
        """Check naming convention consistency."""
        paths = self.spec.get('paths', {})
        schemas = self.spec.get('components', {}).get('schemas', {})
        
        total_checks = 0
        passed_checks = 0
        
        # Check path naming (should be kebab-case)
        for path in paths.keys():
            segments = [seg for seg in path.split('/') if seg and not seg.startswith('{')]
            for segment in segments:
                total_checks += 1
                if self.kebab_case_pattern.match(segment) or re.match(r'^v\d+$', segment):
                    passed_checks += 1
        
        # Check schema naming (should be PascalCase)
        for schema_name in schemas.keys():
            total_checks += 1
            if self.pascal_case_pattern.match(schema_name):
                passed_checks += 1
        
        # Check property naming within schemas
        for schema in schemas.values():
            if isinstance(schema, dict) and 'properties' in schema:
                for prop_name in schema['properties'].keys():
                    total_checks += 1
                    if self.camel_case_pattern.match(prop_name):
                        passed_checks += 1
        
        return (passed_checks / total_checks * 100) if total_checks > 0 else 100
    
    def _check_response_consistency(self) -> float:
        """Check response format consistency."""
        paths = self.spec.get('paths', {})
        
        response_patterns = []
        total_responses = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods or not isinstance(operation, dict):
                    continue
                
                responses = operation.get('responses', {})
                for status_code, response in responses.items():
                    if not isinstance(response, dict):
                        continue
                        
                    total_responses += 1
                    content = response.get('content', {})
                    
                    # Analyze response structure
                    for media_type, media_obj in content.items():
                        schema = media_obj.get('schema', {})
                        pattern = self._extract_schema_pattern(schema)
                        response_patterns.append(pattern)
        
        # Calculate consistency by comparing patterns
        if not response_patterns:
            return 100
        
        pattern_counts = {}
        for pattern in response_patterns:
            pattern_key = json.dumps(pattern, sort_keys=True)
            pattern_counts[pattern_key] = pattern_counts.get(pattern_key, 0) + 1
        
        # Most common pattern should dominate for good consistency
        max_count = max(pattern_counts.values()) if pattern_counts else 0
        consistency_ratio = max_count / len(response_patterns) if response_patterns else 1
        
        return consistency_ratio * 100
    
    def _extract_schema_pattern(self, schema: Dict[str, Any]) -> Dict[str, Any]:
        """Extract a pattern from a schema for consistency checking."""
        if not isinstance(schema, dict):
            return {}
        
        pattern = {
            'type': schema.get('type'),
            'has_properties': 'properties' in schema,
            'has_items': 'items' in schema,
            'required_count': len(schema.get('required', [])),
            'property_count': len(schema.get('properties', {}))
        }
        
        return pattern
    
    def _check_error_format_consistency(self) -> float:
        """Check error response format consistency."""
        paths = self.spec.get('paths', {})
        error_responses = []
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                responses = operation.get('responses', {})
                for status_code, response in responses.items():
                    try:
                        code_int = int(status_code)
                        if code_int >= 400:  # Error responses
                            content = response.get('content', {})
                            for media_type, media_obj in content.items():
                                schema = media_obj.get('schema', {})
                                error_responses.append(self._extract_schema_pattern(schema))
                    except ValueError:
                        continue
        
        if not error_responses:
            return 80  # No error responses defined - somewhat concerning
        
        # Check consistency of error response formats
        pattern_counts = {}
        for pattern in error_responses:
            pattern_key = json.dumps(pattern, sort_keys=True)
            pattern_counts[pattern_key] = pattern_counts.get(pattern_key, 0) + 1
        
        max_count = max(pattern_counts.values()) if pattern_counts else 0
        consistency_ratio = max_count / len(error_responses) if error_responses else 1
        
        return consistency_ratio * 100
    
    def _check_parameter_consistency(self) -> float:
        """Check parameter naming and usage consistency."""
        paths = self.spec.get('paths', {})
        
        query_params = []
        path_params = []
        header_params = []
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                parameters = operation.get('parameters', [])
                for param in parameters:
                    if not isinstance(param, dict):
                        continue
                        
                    param_name = param.get('name', '')
                    param_in = param.get('in', '')
                    
                    if param_in == 'query':
                        query_params.append(param_name)
                    elif param_in == 'path':
                        path_params.append(param_name)
                    elif param_in == 'header':
                        header_params.append(param_name)
        
        # Check naming consistency for each parameter type
        scores = []
        
        # Query parameters should be camelCase or kebab-case
        if query_params:
            valid_query = sum(1 for p in query_params 
                            if self.camel_case_pattern.match(p) or self.kebab_case_pattern.match(p))
            scores.append((valid_query / len(query_params)) * 100)
        
        # Path parameters should be camelCase or kebab-case
        if path_params:
            valid_path = sum(1 for p in path_params 
                           if self.camel_case_pattern.match(p) or self.kebab_case_pattern.match(p))
            scores.append((valid_path / len(path_params)) * 100)
        
        return sum(scores) / len(scores) if scores else 100
    
    def _check_url_structure_consistency(self) -> float:
        """Check URL structure and pattern consistency."""
        paths = self.spec.get('paths', {})
        
        total_paths = len(paths)
        if total_paths == 0:
            return 0
        
        structure_score = 0
        
        # Check for consistent versioning
        versioned_paths = 0
        for path in paths.keys():
            if re.search(r'/v\d+/', path):
                versioned_paths += 1
        
        # Either all or none should be versioned for consistency
        if versioned_paths == 0 or versioned_paths == total_paths:
            structure_score += 25
        elif versioned_paths > total_paths * 0.8:
            structure_score += 20
        
        # Check for reasonable path depth
        reasonable_depth = 0
        for path in paths.keys():
            segments = [seg for seg in path.split('/') if seg]
            if 2 <= len(segments) <= 5:  # Reasonable depth
                reasonable_depth += 1
        
        structure_score += (reasonable_depth / total_paths) * 25
        
        # Check for RESTful resource patterns
        restful_patterns = 0
        for path in paths.keys():
            # Look for patterns like /resources/{id} or /resources
            if re.match(r'^/[a-z-]+(/\{[^}]+\})?(/[a-z-]+)*$', path):
                restful_patterns += 1
        
        structure_score += (restful_patterns / total_paths) * 30
        
        # Check for consistent trailing slash usage
        with_slash = sum(1 for path in paths.keys() if path.endswith('/'))
        without_slash = total_paths - with_slash
        
        # Either all or none should have trailing slashes
        if with_slash == 0 or without_slash == 0:
            structure_score += 20
        elif min(with_slash, without_slash) < total_paths * 0.1:
            structure_score += 15
        
        return min(structure_score, 100)
    
    def _check_http_method_consistency(self) -> float:
        """Check HTTP method usage consistency."""
        paths = self.spec.get('paths', {})
        
        method_usage = {}
        total_operations = 0
        
        for path, path_obj in paths.items():
            if not isinstance(path_obj, dict):
                continue
                
            for method in path_obj.keys():
                if method.upper() in self.http_methods:
                    method_upper = method.upper()
                    total_operations += 1
                    
                    # Analyze method usage patterns
                    if method_upper not in method_usage:
                        method_usage[method_upper] = {'count': 0, 'appropriate': 0}
                    
                    method_usage[method_upper]['count'] += 1
                    
                    # Check if method usage seems appropriate
                    if self._is_method_usage_appropriate(path, method_upper, path_obj[method]):
                        method_usage[method_upper]['appropriate'] += 1
        
        if total_operations == 0:
            return 0
        
        # Calculate appropriateness score
        total_appropriate = sum(data['appropriate'] for data in method_usage.values())
        return (total_appropriate / total_operations) * 100
    
    def _is_method_usage_appropriate(self, path: str, method: str, operation: Dict) -> bool:
        """Check if HTTP method usage is appropriate for the endpoint."""
        # Simple heuristics for method appropriateness
        has_request_body = 'requestBody' in operation
        path_has_id = '{' in path and '}' in path
        
        if method == 'GET':
            return not has_request_body  # GET should not have body
        elif method == 'POST':
            return not path_has_id  # POST typically for collections
        elif method == 'PUT':
            return path_has_id and has_request_body  # PUT for specific resources
        elif method == 'PATCH':
            return path_has_id  # PATCH for specific resources
        elif method == 'DELETE':
            return path_has_id  # DELETE for specific resources
        
        return True  # Default to appropriate for other methods
    
    def _check_status_code_consistency(self) -> float:
        """Check HTTP status code usage consistency."""
        paths = self.spec.get('paths', {})
        
        method_status_patterns = {}
        total_operations = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                total_operations += 1
                responses = operation.get('responses', {})
                status_codes = set(responses.keys())
                
                if method.upper() not in method_status_patterns:
                    method_status_patterns[method.upper()] = []
                
                method_status_patterns[method.upper()].append(status_codes)
        
        if total_operations == 0:
            return 0
        
        # Check consistency within each method type
        consistency_scores = []
        
        for method, status_patterns in method_status_patterns.items():
            if not status_patterns:
                continue
            
            # Find common status codes for this method
            all_codes = set()
            for pattern in status_patterns:
                all_codes.update(pattern)
            
            # Calculate how many operations use the most common codes
            code_usage = {}
            for code in all_codes:
                code_usage[code] = sum(1 for pattern in status_patterns if code in pattern)
            
            # Score based on consistency of common status codes
            if status_patterns:
                avg_consistency = sum(
                    len([code for code in pattern if code_usage.get(code, 0) > len(status_patterns) * 0.5]) 
                    for pattern in status_patterns
                ) / len(status_patterns)
                
                method_consistency = min(avg_consistency / 3.0 * 100, 100)  # Expect ~3 common codes
                consistency_scores.append(method_consistency)
        
        return sum(consistency_scores) / len(consistency_scores) if consistency_scores else 100
    
    def _score_documentation(self) -> None:
        """Score API documentation quality (20% weight)."""
        category = ScoreCategory.DOCUMENTATION
        score = CategoryScore(
            category=category,
            score=0.0,
            max_score=100.0,
            weight=self.category_weights[category]
        )
        
        documentation_checks = [
            self._check_api_level_documentation(),
            self._check_endpoint_documentation(),
            self._check_schema_documentation(),
            self._check_parameter_documentation(),
            self._check_response_documentation(),
            self._check_example_coverage()
        ]
        
        valid_scores = [s for s in documentation_checks if s is not None]
        if valid_scores:
            score.score = sum(valid_scores) / len(valid_scores)
        
        # Add recommendations based on score
        if score.score < 60:
            score.recommendations.extend([
                "Add comprehensive descriptions to all API components",
                "Include examples for complex operations and schemas",
                "Document all parameters and response fields"
            ])
        elif score.score < 80:
            score.recommendations.extend([
                "Improve documentation completeness for some endpoints",
                "Add more examples to enhance developer experience"
            ])
        
        self.scorecard.category_scores[category] = score
    
    def _check_api_level_documentation(self) -> float:
        """Check API-level documentation completeness."""
        info = self.spec.get('info', {})
        score = 0
        
        # Required fields
        if info.get('title'):
            score += 20
        if info.get('version'):
            score += 20
        if info.get('description') and len(info['description']) > 20:
            score += 30
        
        # Optional but recommended fields
        if info.get('contact'):
            score += 15
        if info.get('license'):
            score += 15
        
        return score
    
    def _check_endpoint_documentation(self) -> float:
        """Check endpoint-level documentation completeness."""
        paths = self.spec.get('paths', {})
        
        total_operations = 0
        documented_operations = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                total_operations += 1
                doc_score = 0
                
                if operation.get('summary'):
                    doc_score += 1
                if operation.get('description') and len(operation['description']) > 20:
                    doc_score += 1
                if operation.get('operationId'):
                    doc_score += 1
                
                # Consider it documented if it has at least 2/3 elements
                if doc_score >= 2:
                    documented_operations += 1
        
        return (documented_operations / total_operations * 100) if total_operations > 0 else 100
    
    def _check_schema_documentation(self) -> float:
        """Check schema documentation completeness."""
        schemas = self.spec.get('components', {}).get('schemas', {})
        
        if not schemas:
            return 80  # No schemas to document
        
        total_schemas = len(schemas)
        documented_schemas = 0
        
        for schema_name, schema in schemas.items():
            if not isinstance(schema, dict):
                continue
            
            doc_elements = 0
            
            # Schema-level description
            if schema.get('description'):
                doc_elements += 1
            
            # Property descriptions
            properties = schema.get('properties', {})
            if properties:
                described_props = sum(1 for prop in properties.values() 
                                    if isinstance(prop, dict) and prop.get('description'))
                if described_props > len(properties) * 0.5:  # At least 50% documented
                    doc_elements += 1
            
            # Examples
            if schema.get('example') or any(
                isinstance(prop, dict) and prop.get('example') 
                for prop in properties.values()
            ):
                doc_elements += 1
            
            if doc_elements >= 2:
                documented_schemas += 1
        
        return (documented_schemas / total_schemas * 100) if total_schemas > 0 else 100
    
    def _check_parameter_documentation(self) -> float:
        """Check parameter documentation completeness."""
        paths = self.spec.get('paths', {})
        
        total_params = 0
        documented_params = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                parameters = operation.get('parameters', [])
                for param in parameters:
                    if not isinstance(param, dict):
                        continue
                    
                    total_params += 1
                    
                    doc_score = 0
                    if param.get('description'):
                        doc_score += 1
                    if param.get('example') or (param.get('schema', {}).get('example')):
                        doc_score += 1
                    
                    if doc_score >= 1:  # At least description
                        documented_params += 1
        
        return (documented_params / total_params * 100) if total_params > 0 else 100
    
    def _check_response_documentation(self) -> float:
        """Check response documentation completeness."""
        paths = self.spec.get('paths', {})
        
        total_responses = 0
        documented_responses = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                responses = operation.get('responses', {})
                for status_code, response in responses.items():
                    if not isinstance(response, dict):
                        continue
                    
                    total_responses += 1
                    
                    if response.get('description'):
                        documented_responses += 1
        
        return (documented_responses / total_responses * 100) if total_responses > 0 else 100
    
    def _check_example_coverage(self) -> float:
        """Check example coverage across the API."""
        paths = self.spec.get('paths', {})
        schemas = self.spec.get('components', {}).get('schemas', {})
        
        # Check examples in operations
        total_operations = 0
        operations_with_examples = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                total_operations += 1
                
                has_example = False
                
                # Check request body examples
                request_body = operation.get('requestBody', {})
                if self._has_examples(request_body.get('content', {})):
                    has_example = True
                
                # Check response examples
                responses = operation.get('responses', {})
                for response in responses.values():
                    if isinstance(response, dict) and self._has_examples(response.get('content', {})):
                        has_example = True
                        break
                
                if has_example:
                    operations_with_examples += 1
        
        # Check examples in schemas
        total_schemas = len(schemas)
        schemas_with_examples = 0
        
        for schema in schemas.values():
            if isinstance(schema, dict) and self._schema_has_examples(schema):
                schemas_with_examples += 1
        
        # Combine scores
        operation_score = (operations_with_examples / total_operations * 100) if total_operations > 0 else 100
        schema_score = (schemas_with_examples / total_schemas * 100) if total_schemas > 0 else 100
        
        return (operation_score + schema_score) / 2
    
    def _has_examples(self, content: Dict[str, Any]) -> bool:
        """Check if content has examples."""
        for media_type, media_obj in content.items():
            if isinstance(media_obj, dict):
                if media_obj.get('example') or media_obj.get('examples'):
                    return True
        return False
    
    def _schema_has_examples(self, schema: Dict[str, Any]) -> bool:
        """Check if schema has examples."""
        if schema.get('example'):
            return True
        
        properties = schema.get('properties', {})
        for prop in properties.values():
            if isinstance(prop, dict) and prop.get('example'):
                return True
        
        return False
    
    def _score_security(self) -> None:
        """Score API security implementation (20% weight)."""
        category = ScoreCategory.SECURITY
        score = CategoryScore(
            category=category,
            score=0.0,
            max_score=100.0,
            weight=self.category_weights[category]
        )
        
        security_checks = [
            self._check_security_schemes(),
            self._check_security_requirements(),
            self._check_https_usage(),
            self._check_authentication_patterns(),
            self._check_sensitive_data_handling()
        ]
        
        valid_scores = [s for s in security_checks if s is not None]
        if valid_scores:
            score.score = sum(valid_scores) / len(valid_scores)
        
        # Add recommendations
        if score.score < 50:
            score.recommendations.extend([
                "Implement comprehensive security schemes (OAuth2, API keys, etc.)",
                "Ensure all endpoints have appropriate security requirements",
                "Add input validation and rate limiting patterns"
            ])
        elif score.score < 80:
            score.recommendations.extend([
                "Review security coverage for all endpoints",
                "Consider additional security measures for sensitive operations"
            ])
        
        self.scorecard.category_scores[category] = score
    
    def _check_security_schemes(self) -> float:
        """Check security scheme definitions."""
        security_schemes = self.spec.get('components', {}).get('securitySchemes', {})
        
        if not security_schemes:
            return 20  # Very low score for no security
        
        score = 40  # Base score for having security schemes
        
        scheme_types = set()
        for scheme in security_schemes.values():
            if isinstance(scheme, dict):
                scheme_type = scheme.get('type')
                scheme_types.add(scheme_type)
        
        # Bonus for modern security schemes
        if 'oauth2' in scheme_types:
            score += 30
        if 'apiKey' in scheme_types:
            score += 15
        if 'http' in scheme_types:
            score += 15
        
        return min(score, 100)
    
    def _check_security_requirements(self) -> float:
        """Check security requirement coverage."""
        paths = self.spec.get('paths', {})
        global_security = self.spec.get('security', [])
        
        total_operations = 0
        secured_operations = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                total_operations += 1
                
                # Check if operation has security requirements
                operation_security = operation.get('security')
                
                if operation_security is not None:
                    secured_operations += 1
                elif global_security:
                    secured_operations += 1
        
        return (secured_operations / total_operations * 100) if total_operations > 0 else 0
    
    def _check_https_usage(self) -> float:
        """Check HTTPS enforcement."""
        servers = self.spec.get('servers', [])
        
        if not servers:
            return 60  # No servers defined - assume HTTPS
        
        https_servers = 0
        for server in servers:
            if isinstance(server, dict):
                url = server.get('url', '')
                if url.startswith('https://') or not url.startswith('http://'):
                    https_servers += 1
        
        return (https_servers / len(servers) * 100) if servers else 100
    
    def _check_authentication_patterns(self) -> float:
        """Check authentication pattern quality."""
        security_schemes = self.spec.get('components', {}).get('securitySchemes', {})
        
        if not security_schemes:
            return 0
        
        pattern_scores = []
        
        for scheme in security_schemes.values():
            if not isinstance(scheme, dict):
                continue
            
            scheme_type = scheme.get('type', '').lower()
            
            if scheme_type == 'oauth2':
                # OAuth2 is highly recommended
                flows = scheme.get('flows', {})
                if flows:
                    pattern_scores.append(95)
                else:
                    pattern_scores.append(80)
            elif scheme_type == 'http':
                scheme_scheme = scheme.get('scheme', '').lower()
                if scheme_scheme == 'bearer':
                    pattern_scores.append(85)
                elif scheme_scheme == 'basic':
                    pattern_scores.append(60)  # Less secure
                else:
                    pattern_scores.append(70)
            elif scheme_type == 'apikey':
                location = scheme.get('in', '').lower()
                if location == 'header':
                    pattern_scores.append(75)
                else:
                    pattern_scores.append(60)  # Query/cookie less secure
            else:
                pattern_scores.append(50)  # Unknown scheme
        
        return sum(pattern_scores) / len(pattern_scores) if pattern_scores else 0
    
    def _check_sensitive_data_handling(self) -> float:
        """Check sensitive data handling patterns."""
        # This is a simplified check - in reality would need more sophisticated analysis
        schemas = self.spec.get('components', {}).get('schemas', {})
        
        score = 80  # Default good score
        
        # Look for potential sensitive fields without proper handling
        sensitive_field_names = {'password', 'secret', 'token', 'key', 'ssn', 'credit_card'}
        
        for schema in schemas.values():
            if not isinstance(schema, dict):
                continue
            
            properties = schema.get('properties', {})
            for prop_name, prop_def in properties.items():
                if not isinstance(prop_def, dict):
                    continue
                
                # Check for sensitive field names
                if any(sensitive in prop_name.lower() for sensitive in sensitive_field_names):
                    # Check if it's marked as sensitive (writeOnly, format: password, etc.)
                    if not (prop_def.get('writeOnly') or 
                           prop_def.get('format') == 'password' or
                           'password' in prop_def.get('description', '').lower()):
                        score -= 10  # Penalty for exposed sensitive field
        
        return max(score, 0)
    
    def _score_usability(self) -> None:
        """Score API usability and developer experience (15% weight)."""
        category = ScoreCategory.USABILITY
        score = CategoryScore(
            category=category,
            score=0.0,
            max_score=100.0,
            weight=self.category_weights[category]
        )
        
        usability_checks = [
            self._check_discoverability(),
            self._check_error_handling(),
            self._check_filtering_and_searching(),
            self._check_resource_relationships(),
            self._check_developer_experience()
        ]
        
        valid_scores = [s for s in usability_checks if s is not None]
        if valid_scores:
            score.score = sum(valid_scores) / len(valid_scores)
        
        # Add recommendations
        if score.score < 60:
            score.recommendations.extend([
                "Improve error messages with actionable guidance",
                "Add filtering and search capabilities to list endpoints",
                "Enhance resource discoverability with better linking"
            ])
        elif score.score < 80:
            score.recommendations.extend([
                "Consider adding HATEOAS links for better discoverability",
                "Enhance developer experience with better examples"
            ])
        
        self.scorecard.category_scores[category] = score
    
    def _check_discoverability(self) -> float:
        """Check API discoverability features."""
        paths = self.spec.get('paths', {})
        
        # Look for root/discovery endpoints
        has_root = '/' in paths or any(path == '/api' or path.startswith('/api/') for path in paths)
        
        # Look for HATEOAS patterns in responses
        hateoas_score = 0
        total_responses = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                responses = operation.get('responses', {})
                for response in responses.values():
                    if not isinstance(response, dict):
                        continue
                    
                    total_responses += 1
                    
                    # Look for link-like properties in response schemas
                    content = response.get('content', {})
                    for media_obj in content.values():
                        schema = media_obj.get('schema', {})
                        if self._has_link_properties(schema):
                            hateoas_score += 1
                            break
        
        discovery_score = 50 if has_root else 30
        if total_responses > 0:
            hateoas_ratio = hateoas_score / total_responses
            discovery_score += hateoas_ratio * 50
        
        return min(discovery_score, 100)
    
    def _has_link_properties(self, schema: Dict[str, Any]) -> bool:
        """Check if schema has link-like properties."""
        if not isinstance(schema, dict):
            return False
        
        properties = schema.get('properties', {})
        link_indicators = {'links', '_links', 'href', 'url', 'self', 'next', 'prev'}
        
        return any(prop_name.lower() in link_indicators for prop_name in properties.keys())
    
    def _check_error_handling(self) -> float:
        """Check error handling quality."""
        paths = self.spec.get('paths', {})
        
        total_operations = 0
        operations_with_errors = 0
        detailed_error_responses = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                total_operations += 1
                responses = operation.get('responses', {})
                
                # Check for error responses
                has_error_responses = any(
                    status_code.startswith('4') or status_code.startswith('5')
                    for status_code in responses.keys()
                )
                
                if has_error_responses:
                    operations_with_errors += 1
                    
                    # Check for detailed error schemas
                    for status_code, response in responses.items():
                        if (status_code.startswith('4') or status_code.startswith('5')) and isinstance(response, dict):
                            content = response.get('content', {})
                            for media_obj in content.values():
                                schema = media_obj.get('schema', {})
                                if self._has_detailed_error_schema(schema):
                                    detailed_error_responses += 1
                                    break
                            break
        
        if total_operations == 0:
            return 0
        
        error_coverage = (operations_with_errors / total_operations) * 60
        error_detail = (detailed_error_responses / operations_with_errors * 40) if operations_with_errors > 0 else 0
        
        return error_coverage + error_detail
    
    def _has_detailed_error_schema(self, schema: Dict[str, Any]) -> bool:
        """Check if error schema has detailed information."""
        if not isinstance(schema, dict):
            return False
        
        properties = schema.get('properties', {})
        error_fields = {'error', 'message', 'details', 'code', 'timestamp'}
        
        matching_fields = sum(1 for field in error_fields if field in properties)
        return matching_fields >= 2  # At least 2 standard error fields
    
    def _check_filtering_and_searching(self) -> float:
        """Check filtering and search capabilities."""
        paths = self.spec.get('paths', {})
        
        collection_endpoints = 0
        endpoints_with_filtering = 0
        
        for path, path_obj in paths.items():
            if not isinstance(path_obj, dict):
                continue
            
            # Identify collection endpoints (no path parameters)
            if '{' not in path:
                get_operation = path_obj.get('get')
                if get_operation:
                    collection_endpoints += 1
                    
                    # Check for filtering/search parameters
                    parameters = get_operation.get('parameters', [])
                    filter_params = {'filter', 'search', 'q', 'query', 'limit', 'page', 'offset'}
                    
                    has_filtering = any(
                        isinstance(param, dict) and param.get('name', '').lower() in filter_params
                        for param in parameters
                    )
                    
                    if has_filtering:
                        endpoints_with_filtering += 1
        
        return (endpoints_with_filtering / collection_endpoints * 100) if collection_endpoints > 0 else 100
    
    def _check_resource_relationships(self) -> float:
        """Check resource relationship handling."""
        paths = self.spec.get('paths', {})
        schemas = self.spec.get('components', {}).get('schemas', {})
        
        # Look for nested resource patterns
        nested_resources = 0
        total_resource_paths = 0
        
        for path in paths.keys():
            # Skip root paths
            if path.count('/') >= 3:  # e.g., /api/users/123/orders
                total_resource_paths += 1
                if '{' in path:
                    nested_resources += 1
        
        # Look for relationship fields in schemas
        schemas_with_relations = 0
        for schema in schemas.values():
            if not isinstance(schema, dict):
                continue
            
            properties = schema.get('properties', {})
            relation_indicators = {'id', '_id', 'ref', 'link', 'relationship'}
            
            has_relations = any(
                any(indicator in prop_name.lower() for indicator in relation_indicators)
                for prop_name in properties.keys()
            )
            
            if has_relations:
                schemas_with_relations += 1
        
        nested_score = (nested_resources / total_resource_paths * 50) if total_resource_paths > 0 else 25
        schema_score = (schemas_with_relations / len(schemas) * 50) if schemas else 25
        
        return nested_score + schema_score
    
    def _check_developer_experience(self) -> float:
        """Check overall developer experience factors."""
        # This is a composite score based on various DX factors
        factors = []
        
        # Factor 1: Consistent response structure
        factors.append(self._check_response_consistency())
        
        # Factor 2: Clear operation IDs
        paths = self.spec.get('paths', {})
        total_operations = 0
        operations_with_ids = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
                
            for method, operation in path_obj.items():
                if method.upper() not in self.http_methods:
                    continue
                
                total_operations += 1
                if isinstance(operation, dict) and operation.get('operationId'):
                    operations_with_ids += 1
        
        operation_id_score = (operations_with_ids / total_operations * 100) if total_operations > 0 else 100
        factors.append(operation_id_score)
        
        # Factor 3: Reasonable path complexity
        avg_path_complexity = 0
        if paths:
            complexities = []
            for path in paths.keys():
                segments = [seg for seg in path.split('/') if seg]
                complexities.append(len(segments))
            
            avg_complexity = sum(complexities) / len(complexities)
            # Optimal complexity is 3-4 segments
            if 3 <= avg_complexity <= 4:
                avg_path_complexity = 100
            elif 2 <= avg_complexity <= 5:
                avg_path_complexity = 80
            else:
                avg_path_complexity = 60
        
        factors.append(avg_path_complexity)
        
        return sum(factors) / len(factors) if factors else 0
    
    def _score_performance(self) -> None:
        """Score API performance patterns (15% weight)."""
        category = ScoreCategory.PERFORMANCE
        score = CategoryScore(
            category=category,
            score=0.0,
            max_score=100.0,
            weight=self.category_weights[category]
        )
        
        performance_checks = [
            self._check_caching_headers(),
            self._check_pagination_patterns(),
            self._check_compression_support(),
            self._check_efficiency_patterns(),
            self._check_batch_operations()
        ]
        
        valid_scores = [s for s in performance_checks if s is not None]
        if valid_scores:
            score.score = sum(valid_scores) / len(valid_scores)
        
        # Add recommendations
        if score.score < 60:
            score.recommendations.extend([
                "Implement pagination for list endpoints",
                "Add caching headers for cacheable responses",
                "Consider batch operations for bulk updates"
            ])
        elif score.score < 80:
            score.recommendations.extend([
                "Review caching strategies for better performance",
                "Consider field selection parameters for large responses"
            ])
        
        self.scorecard.category_scores[category] = score
    
    def _check_caching_headers(self) -> float:
        """Check caching header implementation."""
        paths = self.spec.get('paths', {})
        
        get_operations = 0
        cacheable_operations = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
            
            get_operation = path_obj.get('get')
            if get_operation and isinstance(get_operation, dict):
                get_operations += 1
                
                # Check for caching-related headers in responses
                responses = get_operation.get('responses', {})
                for response in responses.values():
                    if not isinstance(response, dict):
                        continue
                    
                    headers = response.get('headers', {})
                    cache_headers = {'cache-control', 'etag', 'last-modified', 'expires'}
                    
                    if any(header.lower() in cache_headers for header in headers.keys()):
                        cacheable_operations += 1
                        break
        
        return (cacheable_operations / get_operations * 100) if get_operations > 0 else 50
    
    def _check_pagination_patterns(self) -> float:
        """Check pagination implementation."""
        paths = self.spec.get('paths', {})
        
        collection_endpoints = 0
        paginated_endpoints = 0
        
        for path, path_obj in paths.items():
            if not isinstance(path_obj, dict):
                continue
            
            # Identify collection endpoints
            if '{' not in path:  # No path parameters = collection
                get_operation = path_obj.get('get')
                if get_operation and isinstance(get_operation, dict):
                    collection_endpoints += 1
                    
                    # Check for pagination parameters
                    parameters = get_operation.get('parameters', [])
                    pagination_params = {'limit', 'offset', 'page', 'pagesize', 'per_page', 'cursor'}
                    
                    has_pagination = any(
                        isinstance(param, dict) and param.get('name', '').lower() in pagination_params
                        for param in parameters
                    )
                    
                    if has_pagination:
                        paginated_endpoints += 1
        
        return (paginated_endpoints / collection_endpoints * 100) if collection_endpoints > 0 else 100
    
    def _check_compression_support(self) -> float:
        """Check compression support indicators."""
        # This is speculative - OpenAPI doesn't directly specify compression
        # Look for indicators that compression is considered
        
        servers = self.spec.get('servers', [])
        
        # Check if any server descriptions mention compression
        compression_mentions = 0
        for server in servers:
            if isinstance(server, dict):
                description = server.get('description', '').lower()
                if any(term in description for term in ['gzip', 'compress', 'deflate']):
                    compression_mentions += 1
        
        # Base score - assume compression is handled at server level
        base_score = 70
        
        if compression_mentions > 0:
            return min(base_score + (compression_mentions * 10), 100)
        
        return base_score
    
    def _check_efficiency_patterns(self) -> float:
        """Check efficiency patterns like field selection."""
        paths = self.spec.get('paths', {})
        
        total_get_operations = 0
        operations_with_selection = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
            
            get_operation = path_obj.get('get')
            if get_operation and isinstance(get_operation, dict):
                total_get_operations += 1
                
                # Check for field selection parameters
                parameters = get_operation.get('parameters', [])
                selection_params = {'fields', 'select', 'include', 'exclude'}
                
                has_selection = any(
                    isinstance(param, dict) and param.get('name', '').lower() in selection_params
                    for param in parameters
                )
                
                if has_selection:
                    operations_with_selection += 1
        
        return (operations_with_selection / total_get_operations * 100) if total_get_operations > 0 else 60
    
    def _check_batch_operations(self) -> float:
        """Check for batch operation support."""
        paths = self.spec.get('paths', {})
        
        # Look for batch endpoints
        batch_indicators = ['batch', 'bulk', 'multi']
        batch_endpoints = 0
        
        for path in paths.keys():
            if any(indicator in path.lower() for indicator in batch_indicators):
                batch_endpoints += 1
        
        # Look for array-based request bodies (indicating batch operations)
        array_operations = 0
        total_post_put_operations = 0
        
        for path_obj in paths.values():
            if not isinstance(path_obj, dict):
                continue
            
            for method in ['post', 'put', 'patch']:
                operation = path_obj.get(method)
                if operation and isinstance(operation, dict):
                    total_post_put_operations += 1
                    
                    request_body = operation.get('requestBody', {})
                    content = request_body.get('content', {})
                    
                    for media_obj in content.values():
                        schema = media_obj.get('schema', {})
                        if schema.get('type') == 'array':
                            array_operations += 1
                            break
        
        # Score based on presence of batch patterns
        batch_score = min(batch_endpoints * 20, 60)  # Up to 60 points for explicit batch endpoints
        
        if total_post_put_operations > 0:
            array_score = (array_operations / total_post_put_operations) * 40
            batch_score += array_score
        
        return min(batch_score, 100)
    
    def generate_json_report(self) -> str:
        """Generate JSON format scorecard."""
        report_data = {
            "overall": {
                "score": round(self.scorecard.overall_score, 2),
                "grade": self.scorecard.overall_grade,
                "totalEndpoints": self.scorecard.total_endpoints
            },
            "api_info": self.scorecard.api_info,
            "categories": {},
            "topRecommendations": self.scorecard.get_top_recommendations()
        }
        
        for category, score in self.scorecard.category_scores.items():
            report_data["categories"][category.value] = {
                "score": round(score.score, 2),
                "grade": score.letter_grade,
                "weight": score.weight,
                "weightedScore": round(score.weighted_score, 2),
                "issues": score.issues,
                "recommendations": score.recommendations
            }
        
        return json.dumps(report_data, indent=2)
    
    def generate_text_report(self) -> str:
        """Generate human-readable scorecard report."""
        lines = [
            "═══════════════════════════════════════════════════════════════",
            "                      API DESIGN SCORECARD",
            "═══════════════════════════════════════════════════════════════",
            f"API: {self.scorecard.api_info.get('title', 'Unknown')}",
            f"Version: {self.scorecard.api_info.get('version', 'Unknown')}",
            f"Total Endpoints: {self.scorecard.total_endpoints}",
            "",
            f"🏆 OVERALL GRADE: {self.scorecard.overall_grade} ({self.scorecard.overall_score:.1f}/100.0)",
            "",
            "═══════════════════════════════════════════════════════════════",
            "DETAILED BREAKDOWN:",
            "═══════════════════════════════════════════════════════════════"
        ]
        
        # Sort categories by weight (most important first)
        sorted_categories = sorted(
            self.scorecard.category_scores.items(),
            key=lambda x: x[1].weight,
            reverse=True
        )
        
        for category, score in sorted_categories:
            category_name = category.value.title().replace('_', ' ')
            
            lines.extend([
                "",
                f"📊 {category_name.upper()} - Grade: {score.letter_grade} ({score.score:.1f}/100)",
                f"   Weight: {score.weight}% | Contribution: {score.weighted_score:.1f} points",
                "   " + "─" * 50
            ])
            
            if score.recommendations:
                lines.append("   💡 Recommendations:")
                for rec in score.recommendations[:3]:  # Top 3 recommendations
                    lines.append(f"      • {rec}")
            else:
                lines.append("   ✅ No specific recommendations - performing well!")
        
        # Overall assessment
        lines.extend([
            "",
            "═══════════════════════════════════════════════════════════════",
            "OVERALL ASSESSMENT:",
            "═══════════════════════════════════════════════════════════════"
        ])
        
        if self.scorecard.overall_grade == "A":
            lines.extend([
                "🏆 EXCELLENT! Your API demonstrates outstanding design quality.",
                "   Continue following these best practices and consider sharing",
                "   your approach as a reference for other teams."
            ])
        elif self.scorecard.overall_grade == "B":
            lines.extend([
                "✅ GOOD! Your API follows most best practices with room for",
                "   minor improvements. Focus on the recommendations above",
                "   to achieve excellence."
            ])
        elif self.scorecard.overall_grade == "C":
            lines.extend([
                "⚠️  FAIR! Your API has a solid foundation but several areas",
                "   need improvement. Prioritize the high-weight categories",
                "   for maximum impact."
            ])
        elif self.scorecard.overall_grade == "D":
            lines.extend([
                "❌ NEEDS IMPROVEMENT! Your API has significant issues that",
                "   may impact developer experience and maintainability.",
                "   Focus on consistency and documentation first."
            ])
        else:  # Grade F
            lines.extend([
                "🚨 CRITICAL ISSUES! Your API requires major redesign to meet",
                "   basic quality standards. Consider comprehensive review",
                "   of design principles and best practices."
            ])
        
        # Top recommendations
        top_recs = self.scorecard.get_top_recommendations(3)
        if top_recs:
            lines.extend([
                "",
                "🎯 TOP PRIORITY RECOMMENDATIONS:",
                ""
            ])
            for i, rec in enumerate(top_recs, 1):
                lines.append(f"   {i}. {rec}")
        
        lines.extend([
            "",
            "═══════════════════════════════════════════════════════════════",
            f"Generated by API Scorecard Tool | Score: {self.scorecard.overall_grade} ({self.scorecard.overall_score:.1f}%)",
            "═══════════════════════════════════════════════════════════════"
        ])
        
        return "\n".join(lines)


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Generate comprehensive API design quality scorecard",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python api_scorecard.py openapi.json
  python api_scorecard.py --format json openapi.json > scorecard.json
  python api_scorecard.py --output scorecard.txt openapi.json
        """
    )
    
    parser.add_argument(
        'spec_file',
        help='OpenAPI/Swagger specification file (JSON format)'
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
        '--min-grade',
        choices=['A', 'B', 'C', 'D', 'F'],
        help='Exit with code 1 if grade is below minimum'
    )
    
    args = parser.parse_args()
    
    # Load specification file
    try:
        with open(args.spec_file, 'r') as f:
            spec = json.load(f)
    except FileNotFoundError:
        print(f"Error: Specification file '{args.spec_file}' not found.", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.spec_file}': {e}", file=sys.stderr)
        return 1
    
    # Initialize scoring engine and generate scorecard
    engine = APIScoringEngine()
    
    try:
        scorecard = engine.score_api(spec)
    except Exception as e:
        print(f"Error during scoring: {e}", file=sys.stderr)
        return 1
    
    # Generate report
    if args.format == 'json':
        output = engine.generate_json_report()
    else:
        output = engine.generate_text_report()
    
    # Write output
    if args.output:
        try:
            with open(args.output, 'w') as f:
                f.write(output)
            print(f"Scorecard written to {args.output}")
        except IOError as e:
            print(f"Error writing to '{args.output}': {e}", file=sys.stderr)
            return 1
    else:
        print(output)
    
    # Check minimum grade requirement
    if args.min_grade:
        grade_order = ['F', 'D', 'C', 'B', 'A']
        current_grade_index = grade_order.index(scorecard.overall_grade)
        min_grade_index = grade_order.index(args.min_grade)
        
        if current_grade_index < min_grade_index:
            print(f"Grade {scorecard.overall_grade} is below minimum required grade {args.min_grade}", file=sys.stderr)
            return 1
    
    return 0


if __name__ == '__main__':
    sys.exit(main())