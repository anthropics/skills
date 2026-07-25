#!/usr/bin/env python3
"""
Data Quality Validator
Comprehensive data quality validation tool for data engineering workflows.

Features:
- Schema validation (types, nullability, constraints)
- Data profiling (statistics, distributions, patterns)
- Great Expectations suite generation
- Data contract validation
- Anomaly detection
- Quality scoring and reporting

Usage:
    python data_quality_validator.py validate data.csv --schema schema.json
    python data_quality_validator.py profile data.csv --output profile.json
    python data_quality_validator.py generate-suite data.csv --output expectations.json
    python data_quality_validator.py contract data.csv --contract contract.yaml
"""

import os
import sys
import json
import csv
import re
import argparse
import logging
import statistics
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple, Set
from dataclasses import dataclass, field, asdict
from datetime import datetime
from collections import Counter
from abc import ABC, abstractmethod

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


# =============================================================================
# Data Classes
# =============================================================================

@dataclass
class ColumnSchema:
    """Schema definition for a column"""
    name: str
    data_type: str  # string, integer, float, boolean, date, datetime, email, uuid
    nullable: bool = True
    unique: bool = False
    min_value: Optional[float] = None
    max_value: Optional[float] = None
    min_length: Optional[int] = None
    max_length: Optional[int] = None
    pattern: Optional[str] = None  # regex pattern
    allowed_values: Optional[List[str]] = None
    description: str = ""


@dataclass
class DataSchema:
    """Complete schema for a dataset"""
    name: str
    version: str
    columns: List[ColumnSchema]
    primary_key: Optional[List[str]] = None
    row_count_min: Optional[int] = None
    row_count_max: Optional[int] = None


@dataclass
class ValidationResult:
    """Result of a single validation check"""
    check_name: str
    column: Optional[str]
    passed: bool
    expected: Any
    actual: Any
    severity: str = "error"  # error, warning, info
    message: str = ""
    failed_rows: List[int] = field(default_factory=list)


@dataclass
class ColumnProfile:
    """Statistical profile of a column"""
    name: str
    data_type: str
    total_count: int
    null_count: int
    null_percentage: float
    unique_count: int
    unique_percentage: float
    # Numeric stats
    min_value: Optional[float] = None
    max_value: Optional[float] = None
    mean: Optional[float] = None
    median: Optional[float] = None
    std_dev: Optional[float] = None
    percentile_25: Optional[float] = None
    percentile_75: Optional[float] = None
    # String stats
    min_length: Optional[int] = None
    max_length: Optional[int] = None
    avg_length: Optional[float] = None
    # Pattern detection
    detected_pattern: Optional[str] = None
    top_values: List[Tuple[str, int]] = field(default_factory=list)


@dataclass
class DataProfile:
    """Complete profile of a dataset"""
    name: str
    row_count: int
    column_count: int
    columns: List[ColumnProfile]
    duplicate_rows: int
    memory_size_bytes: int
    profile_timestamp: str


@dataclass
class QualityScore:
    """Overall quality score for a dataset"""
    completeness: float  # % of non-null values
    uniqueness: float    # % of unique values where expected
    validity: float      # % passing validation rules
    consistency: float   # % passing cross-column checks
    accuracy: float      # % matching expected patterns
    overall: float       # weighted average


# =============================================================================
# Type Detection
# =============================================================================

class TypeDetector:
    """Detect and infer data types from values"""

    PATTERNS = {
        'email': r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$',
        'uuid': r'^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$',
        'phone': r'^\+?[\d\s\-\(\)]{10,}$',
        'url': r'^https?://[^\s]+$',
        'ipv4': r'^(\d{1,3}\.){3}\d{1,3}$',
        'date_iso': r'^\d{4}-\d{2}-\d{2}$',
        'datetime_iso': r'^\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}:\d{2}',
        'credit_card': r'^\d{4}[\s\-]?\d{4}[\s\-]?\d{4}[\s\-]?\d{4}$',
    }

    @classmethod
    def detect_type(cls, values: List[str]) -> str:
        """Detect the most likely data type from a sample of values"""
        non_empty = [v for v in values if v and v.strip()]
        if not non_empty:
            return "string"

        # Check for patterns first
        for pattern_name, pattern in cls.PATTERNS.items():
            regex = re.compile(pattern, re.IGNORECASE)
            matches = sum(1 for v in non_empty if regex.match(v.strip()))
            if matches / len(non_empty) > 0.9:
                return pattern_name

        # Check for numeric types
        int_count = 0
        float_count = 0
        bool_count = 0

        for v in non_empty:
            v = v.strip()
            if v.lower() in ('true', 'false', 'yes', 'no', '1', '0'):
                bool_count += 1
            try:
                int(v)
                int_count += 1
            except ValueError:
                try:
                    float(v)
                    float_count += 1
                except ValueError:
                    pass

        if bool_count / len(non_empty) > 0.9:
            return "boolean"
        if int_count / len(non_empty) > 0.9:
            return "integer"
        if (int_count + float_count) / len(non_empty) > 0.9:
            return "float"

        return "string"

    @classmethod
    def detect_pattern(cls, values: List[str]) -> Optional[str]:
        """Try to detect a common pattern in string values"""
        non_empty = [v for v in values if v and v.strip()]
        if not non_empty or len(non_empty) < 10:
            return None

        for pattern_name, pattern in cls.PATTERNS.items():
            regex = re.compile(pattern, re.IGNORECASE)
            matches = sum(1 for v in non_empty if regex.match(v.strip()))
            if matches / len(non_empty) > 0.8:
                return pattern_name

        return None


# =============================================================================
# Validators
# =============================================================================

class BaseValidator(ABC):
    """Base class for validators"""

    @abstractmethod
    def validate(self, data: List[Dict], schema: Optional[DataSchema] = None) -> List[ValidationResult]:
        pass


class SchemaValidator(BaseValidator):
    """Validate data against a schema"""

    def validate(self, data: List[Dict], schema: DataSchema) -> List[ValidationResult]:
        results = []

        if not data:
            results.append(ValidationResult(
                check_name="data_not_empty",
                column=None,
                passed=False,
                expected="non-empty dataset",
                actual="empty dataset",
                severity="error",
                message="Dataset is empty"
            ))
            return results

        # Validate row count
        row_count = len(data)
        if schema.row_count_min and row_count < schema.row_count_min:
            results.append(ValidationResult(
                check_name="row_count_min",
                column=None,
                passed=False,
                expected=f">= {schema.row_count_min}",
                actual=row_count,
                severity="error",
                message=f"Row count {row_count} is below minimum {schema.row_count_min}"
            ))

        if schema.row_count_max and row_count > schema.row_count_max:
            results.append(ValidationResult(
                check_name="row_count_max",
                column=None,
                passed=False,
                expected=f"<= {schema.row_count_max}",
                actual=row_count,
                severity="warning",
                message=f"Row count {row_count} exceeds maximum {schema.row_count_max}"
            ))

        # Validate each column
        for col_schema in schema.columns:
            col_results = self._validate_column(data, col_schema)
            results.extend(col_results)

        # Validate primary key uniqueness
        if schema.primary_key:
            pk_results = self._validate_primary_key(data, schema.primary_key)
            results.extend(pk_results)

        return results

    def _validate_column(self, data: List[Dict], col_schema: ColumnSchema) -> List[ValidationResult]:
        results = []
        col_name = col_schema.name

        # Check column exists
        if data and col_name not in data[0]:
            results.append(ValidationResult(
                check_name="column_exists",
                column=col_name,
                passed=False,
                expected="column present",
                actual="column missing",
                severity="error",
                message=f"Column '{col_name}' not found in data"
            ))
            return results

        values = [row.get(col_name) for row in data]
        failed_rows = []

        # Null check
        null_count = sum(1 for v in values if v is None or v == '')
        if not col_schema.nullable and null_count > 0:
            failed_rows = [i for i, v in enumerate(values) if v is None or v == '']
            results.append(ValidationResult(
                check_name="not_null",
                column=col_name,
                passed=False,
                expected="no nulls",
                actual=f"{null_count} nulls",
                severity="error",
                message=f"Column '{col_name}' has {null_count} null values but is not nullable",
                failed_rows=failed_rows[:100]  # Limit to first 100
            ))

        non_null_values = [v for v in values if v is not None and v != '']

        # Uniqueness check
        if col_schema.unique and non_null_values:
            unique_count = len(set(non_null_values))
            if unique_count != len(non_null_values):
                duplicate_values = [v for v, count in Counter(non_null_values).items() if count > 1]
                results.append(ValidationResult(
                    check_name="unique",
                    column=col_name,
                    passed=False,
                    expected="all unique",
                    actual=f"{len(non_null_values) - unique_count} duplicates",
                    severity="error",
                    message=f"Column '{col_name}' has duplicate values: {duplicate_values[:5]}"
                ))

        # Type validation
        type_failures = self._validate_type(non_null_values, col_schema.data_type)
        if type_failures:
            results.append(ValidationResult(
                check_name="data_type",
                column=col_name,
                passed=False,
                expected=col_schema.data_type,
                actual=f"{len(type_failures)} invalid values",
                severity="error",
                message=f"Column '{col_name}' has {len(type_failures)} values not matching type {col_schema.data_type}",
                failed_rows=type_failures[:100]
            ))

        # Range validation for numeric columns
        if col_schema.min_value is not None or col_schema.max_value is not None:
            range_failures = self._validate_range(non_null_values, col_schema)
            if range_failures:
                results.append(ValidationResult(
                    check_name="value_range",
                    column=col_name,
                    passed=False,
                    expected=f"[{col_schema.min_value}, {col_schema.max_value}]",
                    actual=f"{len(range_failures)} out of range",
                    severity="error",
                    message=f"Column '{col_name}' has values outside range",
                    failed_rows=range_failures[:100]
                ))

        # Length validation for string columns
        if col_schema.min_length is not None or col_schema.max_length is not None:
            length_failures = self._validate_length(non_null_values, col_schema)
            if length_failures:
                results.append(ValidationResult(
                    check_name="string_length",
                    column=col_name,
                    passed=False,
                    expected=f"length [{col_schema.min_length}, {col_schema.max_length}]",
                    actual=f"{len(length_failures)} out of range",
                    severity="warning",
                    message=f"Column '{col_name}' has values with invalid length",
                    failed_rows=length_failures[:100]
                ))

        # Pattern validation
        if col_schema.pattern:
            pattern_failures = self._validate_pattern(non_null_values, col_schema.pattern)
            if pattern_failures:
                results.append(ValidationResult(
                    check_name="pattern_match",
                    column=col_name,
                    passed=False,
                    expected=f"matches {col_schema.pattern}",
                    actual=f"{len(pattern_failures)} non-matching",
                    severity="error",
                    message=f"Column '{col_name}' has values not matching pattern",
                    failed_rows=pattern_failures[:100]
                ))

        # Allowed values validation
        if col_schema.allowed_values:
            allowed_set = set(col_schema.allowed_values)
            invalid = [i for i, v in enumerate(non_null_values) if str(v) not in allowed_set]
            if invalid:
                results.append(ValidationResult(
                    check_name="allowed_values",
                    column=col_name,
                    passed=False,
                    expected=f"one of {col_schema.allowed_values}",
                    actual=f"{len(invalid)} invalid values",
                    severity="error",
                    message=f"Column '{col_name}' has values not in allowed list",
                    failed_rows=invalid[:100]
                ))

        return results

    def _validate_type(self, values: List[Any], expected_type: str) -> List[int]:
        """Return indices of values that don't match expected type"""
        failures = []

        for i, v in enumerate(values):
            v_str = str(v)
            valid = False

            if expected_type == "integer":
                try:
                    int(v_str)
                    valid = True
                except ValueError:
                    pass
            elif expected_type == "float":
                try:
                    float(v_str)
                    valid = True
                except ValueError:
                    pass
            elif expected_type == "boolean":
                valid = v_str.lower() in ('true', 'false', 'yes', 'no', '1', '0')
            elif expected_type == "email":
                valid = bool(re.match(TypeDetector.PATTERNS['email'], v_str, re.IGNORECASE))
            elif expected_type == "uuid":
                valid = bool(re.match(TypeDetector.PATTERNS['uuid'], v_str, re.IGNORECASE))
            elif expected_type in ("date", "date_iso"):
                valid = bool(re.match(TypeDetector.PATTERNS['date_iso'], v_str))
            elif expected_type in ("datetime", "datetime_iso"):
                valid = bool(re.match(TypeDetector.PATTERNS['datetime_iso'], v_str))
            else:
                valid = True  # string accepts anything

            if not valid:
                failures.append(i)

        return failures

    def _validate_range(self, values: List[Any], col_schema: ColumnSchema) -> List[int]:
        """Return indices of values outside the specified range"""
        failures = []
        for i, v in enumerate(values):
            try:
                num = float(v)
                if col_schema.min_value is not None and num < col_schema.min_value:
                    failures.append(i)
                elif col_schema.max_value is not None and num > col_schema.max_value:
                    failures.append(i)
            except (ValueError, TypeError):
                pass
        return failures

    def _validate_length(self, values: List[Any], col_schema: ColumnSchema) -> List[int]:
        """Return indices of values with invalid string length"""
        failures = []
        for i, v in enumerate(values):
            length = len(str(v))
            if col_schema.min_length is not None and length < col_schema.min_length:
                failures.append(i)
            elif col_schema.max_length is not None and length > col_schema.max_length:
                failures.append(i)
        return failures

    def _validate_pattern(self, values: List[Any], pattern: str) -> List[int]:
        """Return indices of values not matching the pattern"""
        regex = re.compile(pattern)
        return [i for i, v in enumerate(values) if not regex.match(str(v))]

    def _validate_primary_key(self, data: List[Dict], pk_columns: List[str]) -> List[ValidationResult]:
        """Validate primary key uniqueness"""
        results = []
        pk_values = []

        for row in data:
            pk = tuple(row.get(col) for col in pk_columns)
            pk_values.append(pk)

        pk_counts = Counter(pk_values)
        duplicates = {pk: count for pk, count in pk_counts.items() if count > 1}

        if duplicates:
            results.append(ValidationResult(
                check_name="primary_key_unique",
                column=",".join(pk_columns),
                passed=False,
                expected="all unique",
                actual=f"{len(duplicates)} duplicate keys",
                severity="error",
                message=f"Primary key has {len(duplicates)} duplicate combinations"
            ))

        return results


class AnomalyDetector(BaseValidator):
    """Detect anomalies in data"""

    def __init__(self, z_threshold: float = 3.0, iqr_multiplier: float = 1.5):
        self.z_threshold = z_threshold
        self.iqr_multiplier = iqr_multiplier

    def validate(self, data: List[Dict], schema: Optional[DataSchema] = None) -> List[ValidationResult]:
        results = []

        if not data:
            return results

        # Get numeric columns
        numeric_columns = []
        for col in data[0].keys():
            values = [row.get(col) for row in data]
            non_null = [v for v in values if v is not None and v != '']
            try:
                [float(v) for v in non_null[:100]]
                numeric_columns.append(col)
            except (ValueError, TypeError):
                pass

        for col in numeric_columns:
            col_results = self._detect_numeric_anomalies(data, col)
            results.extend(col_results)

        return results

    def _detect_numeric_anomalies(self, data: List[Dict], column: str) -> List[ValidationResult]:
        results = []

        values = []
        for row in data:
            v = row.get(column)
            if v is not None and v != '':
                try:
                    values.append(float(v))
                except (ValueError, TypeError):
                    pass

        if len(values) < 10:
            return results

        # Z-score method
        mean = statistics.mean(values)
        std = statistics.stdev(values) if len(values) > 1 else 0

        if std > 0:
            z_outliers = []
            for i, v in enumerate(values):
                z_score = abs((v - mean) / std)
                if z_score > self.z_threshold:
                    z_outliers.append((i, v, z_score))

            if z_outliers:
                results.append(ValidationResult(
                    check_name="z_score_outlier",
                    column=column,
                    passed=len(z_outliers) == 0,
                    expected=f"z-score <= {self.z_threshold}",
                    actual=f"{len(z_outliers)} outliers",
                    severity="warning",
                    message=f"Column '{column}' has {len(z_outliers)} statistical outliers (z-score method)",
                    failed_rows=[o[0] for o in z_outliers[:100]]
                ))

        # IQR method
        sorted_values = sorted(values)
        q1_idx = len(sorted_values) // 4
        q3_idx = (3 * len(sorted_values)) // 4
        q1 = sorted_values[q1_idx]
        q3 = sorted_values[q3_idx]
        iqr = q3 - q1

        lower_bound = q1 - self.iqr_multiplier * iqr
        upper_bound = q3 + self.iqr_multiplier * iqr

        iqr_outliers = [(i, v) for i, v in enumerate(values) if v < lower_bound or v > upper_bound]

        if iqr_outliers:
            results.append(ValidationResult(
                check_name="iqr_outlier",
                column=column,
                passed=len(iqr_outliers) == 0,
                expected=f"value in [{lower_bound:.2f}, {upper_bound:.2f}]",
                actual=f"{len(iqr_outliers)} outliers",
                severity="warning",
                message=f"Column '{column}' has {len(iqr_outliers)} outliers (IQR method)",
                failed_rows=[o[0] for o in iqr_outliers[:100]]
            ))

        return results


# =============================================================================
# Data Profiler
# =============================================================================

class DataProfiler:
    """Generate statistical profiles of datasets"""

    def profile(self, data: List[Dict], name: str = "dataset") -> DataProfile:
        """Generate a complete profile of the dataset"""
        if not data:
            return DataProfile(
                name=name,
                row_count=0,
                column_count=0,
                columns=[],
                duplicate_rows=0,
                memory_size_bytes=0,
                profile_timestamp=datetime.now().isoformat()
            )

        columns = list(data[0].keys())
        column_profiles = []

        for col in columns:
            profile = self._profile_column(data, col)
            column_profiles.append(profile)

        # Count duplicates
        row_tuples = [tuple(sorted(row.items())) for row in data]
        duplicate_count = len(row_tuples) - len(set(row_tuples))

        # Estimate memory size
        memory_size = sys.getsizeof(data) + sum(
            sys.getsizeof(row) + sum(sys.getsizeof(v) for v in row.values())
            for row in data
        )

        return DataProfile(
            name=name,
            row_count=len(data),
            column_count=len(columns),
            columns=column_profiles,
            duplicate_rows=duplicate_count,
            memory_size_bytes=memory_size,
            profile_timestamp=datetime.now().isoformat()
        )

    def _profile_column(self, data: List[Dict], column: str) -> ColumnProfile:
        """Generate profile for a single column"""
        values = [row.get(column) for row in data]
        non_null = [v for v in values if v is not None and v != '']

        total_count = len(values)
        null_count = total_count - len(non_null)
        null_pct = (null_count / total_count * 100) if total_count > 0 else 0

        unique_values = set(str(v) for v in non_null)
        unique_count = len(unique_values)
        unique_pct = (unique_count / len(non_null) * 100) if non_null else 0

        # Detect type
        sample = [str(v) for v in non_null[:1000]]
        detected_type = TypeDetector.detect_type(sample)
        detected_pattern = TypeDetector.detect_pattern(sample)

        # Top values
        value_counts = Counter(str(v) for v in non_null)
        top_values = value_counts.most_common(10)

        profile = ColumnProfile(
            name=column,
            data_type=detected_type,
            total_count=total_count,
            null_count=null_count,
            null_percentage=null_pct,
            unique_count=unique_count,
            unique_percentage=unique_pct,
            detected_pattern=detected_pattern,
            top_values=top_values
        )

        # Add numeric stats if applicable
        if detected_type in ('integer', 'float'):
            numeric_values = []
            for v in non_null:
                try:
                    numeric_values.append(float(v))
                except (ValueError, TypeError):
                    pass

            if numeric_values:
                sorted_vals = sorted(numeric_values)
                profile.min_value = min(numeric_values)
                profile.max_value = max(numeric_values)
                profile.mean = statistics.mean(numeric_values)
                profile.median = statistics.median(numeric_values)
                if len(numeric_values) > 1:
                    profile.std_dev = statistics.stdev(numeric_values)
                profile.percentile_25 = sorted_vals[len(sorted_vals) // 4]
                profile.percentile_75 = sorted_vals[(3 * len(sorted_vals)) // 4]

        # Add string stats
        if detected_type == 'string':
            lengths = [len(str(v)) for v in non_null]
            if lengths:
                profile.min_length = min(lengths)
                profile.max_length = max(lengths)
                profile.avg_length = statistics.mean(lengths)

        return profile


# =============================================================================
# Great Expectations Suite Generator
# =============================================================================

class GreatExpectationsGenerator:
    """Generate Great Expectations validation suites"""

    def generate_suite(self, profile: DataProfile) -> Dict:
        """Generate a Great Expectations suite from a data profile"""
        expectations = []

        for col_profile in profile.columns:
            col_expectations = self._generate_column_expectations(col_profile)
            expectations.extend(col_expectations)

        # Table-level expectations
        expectations.append({
            "expectation_type": "expect_table_row_count_to_be_between",
            "kwargs": {
                "min_value": max(1, int(profile.row_count * 0.5)),
                "max_value": int(profile.row_count * 2)
            }
        })

        expectations.append({
            "expectation_type": "expect_table_column_count_to_equal",
            "kwargs": {
                "value": profile.column_count
            }
        })

        suite = {
            "expectation_suite_name": f"{profile.name}_suite",
            "expectations": expectations,
            "meta": {
                "generated_at": datetime.now().isoformat(),
                "generator": "data_quality_validator",
                "source_profile": profile.name
            }
        }

        return suite

    def _generate_column_expectations(self, col_profile: ColumnProfile) -> List[Dict]:
        """Generate expectations for a single column"""
        expectations = []
        col_name = col_profile.name

        # Column exists
        expectations.append({
            "expectation_type": "expect_column_to_exist",
            "kwargs": {"column": col_name}
        })

        # Null percentage
        if col_profile.null_percentage < 1:
            expectations.append({
                "expectation_type": "expect_column_values_to_not_be_null",
                "kwargs": {"column": col_name}
            })
        elif col_profile.null_percentage < 50:
            expectations.append({
                "expectation_type": "expect_column_values_to_not_be_null",
                "kwargs": {
                    "column": col_name,
                    "mostly": 1 - (col_profile.null_percentage / 100 * 1.5)
                }
            })

        # Uniqueness
        if col_profile.unique_percentage > 99:
            expectations.append({
                "expectation_type": "expect_column_values_to_be_unique",
                "kwargs": {"column": col_name}
            })

        # Type-specific expectations
        if col_profile.data_type == 'integer':
            expectations.append({
                "expectation_type": "expect_column_values_to_be_in_type_list",
                "kwargs": {
                    "column": col_name,
                    "type_list": ["int", "int64", "INTEGER", "BIGINT"]
                }
            })
            if col_profile.min_value is not None:
                expectations.append({
                    "expectation_type": "expect_column_values_to_be_between",
                    "kwargs": {
                        "column": col_name,
                        "min_value": col_profile.min_value,
                        "max_value": col_profile.max_value
                    }
                })

        elif col_profile.data_type == 'float':
            expectations.append({
                "expectation_type": "expect_column_values_to_be_in_type_list",
                "kwargs": {
                    "column": col_name,
                    "type_list": ["float", "float64", "FLOAT", "DOUBLE"]
                }
            })
            if col_profile.min_value is not None:
                expectations.append({
                    "expectation_type": "expect_column_values_to_be_between",
                    "kwargs": {
                        "column": col_name,
                        "min_value": col_profile.min_value,
                        "max_value": col_profile.max_value
                    }
                })

        elif col_profile.data_type == 'email':
            expectations.append({
                "expectation_type": "expect_column_values_to_match_regex",
                "kwargs": {
                    "column": col_name,
                    "regex": r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$"
                }
            })

        elif col_profile.data_type in ('date_iso', 'date'):
            expectations.append({
                "expectation_type": "expect_column_values_to_match_strftime_format",
                "kwargs": {
                    "column": col_name,
                    "strftime_format": "%Y-%m-%d"
                }
            })

        # String length expectations
        if col_profile.min_length is not None:
            expectations.append({
                "expectation_type": "expect_column_value_lengths_to_be_between",
                "kwargs": {
                    "column": col_name,
                    "min_value": max(1, col_profile.min_length),
                    "max_value": col_profile.max_length * 2 if col_profile.max_length else None
                }
            })

        # Categorical (low cardinality) columns
        if col_profile.unique_count <= 20 and col_profile.unique_percentage < 10:
            top_values = [v[0] for v in col_profile.top_values if v[1] > col_profile.total_count * 0.01]
            if top_values:
                expectations.append({
                    "expectation_type": "expect_column_values_to_be_in_set",
                    "kwargs": {
                        "column": col_name,
                        "value_set": top_values,
                        "mostly": 0.95
                    }
                })

        return expectations


# =============================================================================
# Quality Score Calculator
# =============================================================================

class QualityScoreCalculator:
    """Calculate overall data quality scores"""

    def calculate(self, profile: DataProfile, validation_results: List[ValidationResult]) -> QualityScore:
        """Calculate quality score from profile and validation results"""
        # Completeness: average non-null percentage
        completeness = 100 - statistics.mean([c.null_percentage for c in profile.columns]) if profile.columns else 0

        # Uniqueness: average unique percentage for columns expected to be unique
        unique_cols = [c for c in profile.columns if c.unique_percentage > 90]
        uniqueness = statistics.mean([c.unique_percentage for c in unique_cols]) if unique_cols else 100

        # Validity: percentage of passed checks
        total_checks = len(validation_results)
        passed_checks = sum(1 for r in validation_results if r.passed)
        validity = (passed_checks / total_checks * 100) if total_checks > 0 else 100

        # Consistency: percentage of non-error results
        error_checks = sum(1 for r in validation_results if not r.passed and r.severity == "error")
        consistency = ((total_checks - error_checks) / total_checks * 100) if total_checks > 0 else 100

        # Accuracy: based on pattern matching and type detection
        pattern_detected = sum(1 for c in profile.columns if c.detected_pattern)
        accuracy = min(100, 50 + (pattern_detected / len(profile.columns) * 50)) if profile.columns else 50

        # Overall: weighted average
        overall = (
            completeness * 0.25 +
            uniqueness * 0.15 +
            validity * 0.30 +
            consistency * 0.20 +
            accuracy * 0.10
        )

        return QualityScore(
            completeness=round(completeness, 2),
            uniqueness=round(uniqueness, 2),
            validity=round(validity, 2),
            consistency=round(consistency, 2),
            accuracy=round(accuracy, 2),
            overall=round(overall, 2)
        )


# =============================================================================
# Data Contract Validator
# =============================================================================

class DataContractValidator:
    """Validate data against a data contract"""

    def load_contract(self, contract_path: str) -> Dict:
        """Load a data contract from file"""
        with open(contract_path, 'r') as f:
            content = f.read()

        # Support both YAML and JSON
        if contract_path.endswith('.yaml') or contract_path.endswith('.yml'):
            # Simple YAML parsing (for basic contracts)
            contract = self._parse_simple_yaml(content)
        else:
            contract = json.loads(content)

        return contract

    def _parse_simple_yaml(self, content: str) -> Dict:
        """Parse simple YAML-like format"""
        result = {}
        current_section = result
        section_stack = [(result, -1)]

        for line in content.split('\n'):
            if not line.strip() or line.strip().startswith('#'):
                continue

            # Calculate indentation
            indent = len(line) - len(line.lstrip())
            line = line.strip()

            # Pop sections with greater or equal indentation
            while section_stack and section_stack[-1][1] >= indent:
                section_stack.pop()

            current_section = section_stack[-1][0]

            if ':' in line:
                key, value = line.split(':', 1)
                key = key.strip()
                value = value.strip()

                if value:
                    # Handle lists
                    if value.startswith('[') and value.endswith(']'):
                        current_section[key] = [v.strip().strip('"\'') for v in value[1:-1].split(',')]
                    elif value.lower() in ('true', 'false'):
                        current_section[key] = value.lower() == 'true'
                    elif value.isdigit():
                        current_section[key] = int(value)
                    else:
                        current_section[key] = value.strip('"\'')
                else:
                    current_section[key] = {}
                    section_stack.append((current_section[key], indent))
            elif line.startswith('- '):
                # List item
                if not isinstance(current_section, list):
                    # Convert to list
                    parent = section_stack[-2][0] if len(section_stack) > 1 else result
                    for k, v in parent.items():
                        if v is current_section:
                            parent[k] = [current_section] if current_section else []
                            current_section = parent[k]
                            section_stack[-1] = (current_section, section_stack[-1][1])
                            break
                current_section.append(line[2:].strip())

        return result

    def validate_contract(self, data: List[Dict], contract: Dict) -> List[ValidationResult]:
        """Validate data against contract"""
        results = []

        # Validate schema section
        if 'schema' in contract:
            schema_def = contract['schema']
            columns = schema_def.get('columns', schema_def.get('fields', []))

            for col_def in columns:
                col_name = col_def.get('name', col_def.get('column', ''))
                if not col_name:
                    continue

                # Check column exists
                if data and col_name not in data[0]:
                    results.append(ValidationResult(
                        check_name="contract_column_exists",
                        column=col_name,
                        passed=False,
                        expected="column present",
                        actual="column missing",
                        severity="error",
                        message=f"Contract requires column '{col_name}' but it's missing"
                    ))
                    continue

                # Check data type
                expected_type = col_def.get('type', col_def.get('data_type', 'string'))
                values = [row.get(col_name) for row in data]
                non_null = [str(v) for v in values if v is not None and v != '']

                if non_null:
                    detected_type = TypeDetector.detect_type(non_null[:1000])
                    type_compatible = self._types_compatible(detected_type, expected_type)

                    if not type_compatible:
                        results.append(ValidationResult(
                            check_name="contract_data_type",
                            column=col_name,
                            passed=False,
                            expected=expected_type,
                            actual=detected_type,
                            severity="error",
                            message=f"Contract expects type '{expected_type}' but detected '{detected_type}'"
                        ))

                # Check nullable
                if not col_def.get('nullable', True):
                    null_count = sum(1 for v in values if v is None or v == '')
                    if null_count > 0:
                        results.append(ValidationResult(
                            check_name="contract_not_null",
                            column=col_name,
                            passed=False,
                            expected="no nulls",
                            actual=f"{null_count} nulls",
                            severity="error",
                            message=f"Contract requires non-null but found {null_count} nulls"
                        ))

        # Validate SLA section
        if 'sla' in contract:
            sla = contract['sla']

            # Row count bounds
            min_rows = sla.get('min_rows', sla.get('minimum_records'))
            max_rows = sla.get('max_rows', sla.get('maximum_records'))

            row_count = len(data)
            if min_rows and row_count < min_rows:
                results.append(ValidationResult(
                    check_name="contract_min_rows",
                    column=None,
                    passed=False,
                    expected=f">= {min_rows} rows",
                    actual=f"{row_count} rows",
                    severity="error",
                    message=f"Contract requires at least {min_rows} rows"
                ))

            if max_rows and row_count > max_rows:
                results.append(ValidationResult(
                    check_name="contract_max_rows",
                    column=None,
                    passed=False,
                    expected=f"<= {max_rows} rows",
                    actual=f"{row_count} rows",
                    severity="warning",
                    message=f"Contract allows at most {max_rows} rows"
                ))

        return results

    def _types_compatible(self, detected: str, expected: str) -> bool:
        """Check if detected type is compatible with expected type"""
        expected = expected.lower()
        detected = detected.lower()

        type_groups = {
            'numeric': ['integer', 'int', 'float', 'double', 'decimal', 'number'],
            'string': ['string', 'varchar', 'char', 'text'],
            'boolean': ['boolean', 'bool'],
            'date': ['date', 'date_iso'],
            'datetime': ['datetime', 'datetime_iso', 'timestamp'],
        }

        for group, types in type_groups.items():
            if expected in types and detected in types:
                return True

        return detected == expected


# =============================================================================
# Report Generator
# =============================================================================

class ReportGenerator:
    """Generate validation reports"""

    def generate_text_report(self,
                            profile: DataProfile,
                            results: List[ValidationResult],
                            score: QualityScore) -> str:
        """Generate a text report"""
        lines = []
        lines.append("=" * 80)
        lines.append("DATA QUALITY VALIDATION REPORT")
        lines.append("=" * 80)
        lines.append(f"\nDataset: {profile.name}")
        lines.append(f"Generated: {datetime.now().isoformat()}")
        lines.append(f"Rows: {profile.row_count:,}")
        lines.append(f"Columns: {profile.column_count}")
        lines.append(f"Duplicate Rows: {profile.duplicate_rows:,}")

        # Quality Score
        lines.append("\n" + "-" * 40)
        lines.append("QUALITY SCORES")
        lines.append("-" * 40)
        lines.append(f"  Overall:      {score.overall:>6.1f}% {'✓' if score.overall >= 80 else '✗'}")
        lines.append(f"  Completeness: {score.completeness:>6.1f}%")
        lines.append(f"  Uniqueness:   {score.uniqueness:>6.1f}%")
        lines.append(f"  Validity:     {score.validity:>6.1f}%")
        lines.append(f"  Consistency:  {score.consistency:>6.1f}%")
        lines.append(f"  Accuracy:     {score.accuracy:>6.1f}%")

        # Validation Results Summary
        passed = sum(1 for r in results if r.passed)
        failed = len(results) - passed
        errors = sum(1 for r in results if not r.passed and r.severity == "error")
        warnings = sum(1 for r in results if not r.passed and r.severity == "warning")

        lines.append("\n" + "-" * 40)
        lines.append("VALIDATION SUMMARY")
        lines.append("-" * 40)
        lines.append(f"  Total Checks: {len(results)}")
        lines.append(f"  Passed:       {passed} ✓")
        lines.append(f"  Failed:       {failed} ✗")
        lines.append(f"    Errors:     {errors}")
        lines.append(f"    Warnings:   {warnings}")

        # Failed checks details
        if failed > 0:
            lines.append("\n" + "-" * 40)
            lines.append("FAILED CHECKS")
            lines.append("-" * 40)

            for r in results:
                if not r.passed:
                    severity_icon = "❌" if r.severity == "error" else "⚠️"
                    col_str = f"[{r.column}]" if r.column else ""
                    lines.append(f"\n{severity_icon} {r.check_name} {col_str}")
                    lines.append(f"   Expected: {r.expected}")
                    lines.append(f"   Actual:   {r.actual}")
                    if r.message:
                        lines.append(f"   Message:  {r.message}")

        # Column profiles
        lines.append("\n" + "-" * 40)
        lines.append("COLUMN PROFILES")
        lines.append("-" * 40)

        for col in profile.columns:
            lines.append(f"\n  {col.name}")
            lines.append(f"    Type: {col.data_type}")
            lines.append(f"    Nulls: {col.null_count:,} ({col.null_percentage:.1f}%)")
            lines.append(f"    Unique: {col.unique_count:,} ({col.unique_percentage:.1f}%)")

            if col.min_value is not None:
                lines.append(f"    Range: [{col.min_value:.2f}, {col.max_value:.2f}]")
                lines.append(f"    Mean: {col.mean:.2f}, Median: {col.median:.2f}")

            if col.min_length is not None:
                lines.append(f"    Length: [{col.min_length}, {col.max_length}] (avg: {col.avg_length:.1f})")

            if col.detected_pattern:
                lines.append(f"    Pattern: {col.detected_pattern}")

            if col.top_values:
                top_3 = col.top_values[:3]
                lines.append(f"    Top values: {', '.join(f'{v[0]} ({v[1]})' for v in top_3)}")

        lines.append("\n" + "=" * 80)

        return "\n".join(lines)

    def generate_json_report(self,
                            profile: DataProfile,
                            results: List[ValidationResult],
                            score: QualityScore) -> Dict:
        """Generate a JSON report"""
        return {
            "report_type": "data_quality_validation",
            "generated_at": datetime.now().isoformat(),
            "dataset": {
                "name": profile.name,
                "row_count": profile.row_count,
                "column_count": profile.column_count,
                "duplicate_rows": profile.duplicate_rows,
                "memory_bytes": profile.memory_size_bytes
            },
            "quality_score": asdict(score),
            "validation_summary": {
                "total_checks": len(results),
                "passed": sum(1 for r in results if r.passed),
                "failed": sum(1 for r in results if not r.passed),
                "errors": sum(1 for r in results if not r.passed and r.severity == "error"),
                "warnings": sum(1 for r in results if not r.passed and r.severity == "warning")
            },
            "validation_results": [
                {
                    "check": r.check_name,
                    "column": r.column,
                    "passed": r.passed,
                    "severity": r.severity,
                    "expected": str(r.expected),
                    "actual": str(r.actual),
                    "message": r.message
                }
                for r in results
            ],
            "column_profiles": [asdict(c) for c in profile.columns]
        }


# =============================================================================
# Data Loader
# =============================================================================

class DataLoader:
    """Load data from various formats"""

    @staticmethod
    def load(file_path: str) -> List[Dict]:
        """Load data from file"""
        path = Path(file_path)

        if not path.exists():
            raise FileNotFoundError(f"File not found: {file_path}")

        suffix = path.suffix.lower()

        if suffix == '.csv':
            return DataLoader._load_csv(file_path)
        elif suffix == '.json':
            return DataLoader._load_json(file_path)
        elif suffix == '.jsonl':
            return DataLoader._load_jsonl(file_path)
        else:
            raise ValueError(f"Unsupported file format: {suffix}")

    @staticmethod
    def _load_csv(file_path: str) -> List[Dict]:
        """Load CSV file"""
        data = []
        with open(file_path, 'r', newline='', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                data.append(dict(row))
        return data

    @staticmethod
    def _load_json(file_path: str) -> List[Dict]:
        """Load JSON file"""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = json.load(f)

        if isinstance(content, list):
            return content
        elif isinstance(content, dict):
            # Check for common data keys
            for key in ['data', 'records', 'rows', 'items']:
                if key in content and isinstance(content[key], list):
                    return content[key]
            return [content]
        else:
            raise ValueError("JSON must contain array or object with data key")

    @staticmethod
    def _load_jsonl(file_path: str) -> List[Dict]:
        """Load JSON Lines file"""
        data = []
        with open(file_path, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line:
                    data.append(json.loads(line))
        return data


# =============================================================================
# Schema Loader
# =============================================================================

class SchemaLoader:
    """Load schema definitions"""

    @staticmethod
    def load(file_path: str) -> DataSchema:
        """Load schema from JSON file"""
        with open(file_path, 'r', encoding='utf-8') as f:
            schema_dict = json.load(f)

        columns = []
        for col_def in schema_dict.get('columns', []):
            columns.append(ColumnSchema(
                name=col_def['name'],
                data_type=col_def.get('type', col_def.get('data_type', 'string')),
                nullable=col_def.get('nullable', True),
                unique=col_def.get('unique', False),
                min_value=col_def.get('min_value'),
                max_value=col_def.get('max_value'),
                min_length=col_def.get('min_length'),
                max_length=col_def.get('max_length'),
                pattern=col_def.get('pattern'),
                allowed_values=col_def.get('allowed_values'),
                description=col_def.get('description', '')
            ))

        return DataSchema(
            name=schema_dict.get('name', 'unknown'),
            version=schema_dict.get('version', '1.0'),
            columns=columns,
            primary_key=schema_dict.get('primary_key'),
            row_count_min=schema_dict.get('row_count_min'),
            row_count_max=schema_dict.get('row_count_max')
        )


# =============================================================================
# CLI Interface
# =============================================================================

def cmd_validate(args):
    """Run validation against schema"""
    logger.info(f"Loading data from {args.input}")
    data = DataLoader.load(args.input)

    results = []

    if args.schema:
        logger.info(f"Loading schema from {args.schema}")
        schema = SchemaLoader.load(args.schema)

        validator = SchemaValidator()
        results = validator.validate(data, schema)

    if args.detect_anomalies:
        logger.info("Running anomaly detection")
        anomaly_detector = AnomalyDetector()
        anomaly_results = anomaly_detector.validate(data)
        results.extend(anomaly_results)

    # Profile data
    profiler = DataProfiler()
    profile = profiler.profile(data, name=Path(args.input).stem)

    # Calculate score
    score_calc = QualityScoreCalculator()
    score = score_calc.calculate(profile, results)

    # Generate report
    reporter = ReportGenerator()

    if args.json:
        report = reporter.generate_json_report(profile, results, score)
        output = json.dumps(report, indent=2)
    else:
        output = reporter.generate_text_report(profile, results, score)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        logger.info(f"Report saved to {args.output}")
    else:
        print(output)

    # Exit with error if validation failed
    errors = sum(1 for r in results if not r.passed and r.severity == "error")
    if errors > 0:
        sys.exit(1)


def cmd_profile(args):
    """Generate data profile"""
    logger.info(f"Loading data from {args.input}")
    data = DataLoader.load(args.input)

    profiler = DataProfiler()
    profile = profiler.profile(data, name=Path(args.input).stem)

    if args.json or args.output:
        output = json.dumps(asdict(profile), indent=2, default=str)
    else:
        # Text output
        lines = []
        lines.append(f"Dataset: {profile.name}")
        lines.append(f"Rows: {profile.row_count:,}")
        lines.append(f"Columns: {profile.column_count}")
        lines.append(f"Duplicate rows: {profile.duplicate_rows:,}")
        lines.append(f"\nColumn Profiles:")

        for col in profile.columns:
            lines.append(f"\n  {col.name} ({col.data_type})")
            lines.append(f"    Nulls: {col.null_percentage:.1f}%")
            lines.append(f"    Unique: {col.unique_percentage:.1f}%")
            if col.mean is not None:
                lines.append(f"    Stats: min={col.min_value}, max={col.max_value}, mean={col.mean:.2f}")

        output = "\n".join(lines)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        logger.info(f"Profile saved to {args.output}")
    else:
        print(output)


def cmd_generate_suite(args):
    """Generate Great Expectations suite"""
    logger.info(f"Loading data from {args.input}")
    data = DataLoader.load(args.input)

    # Profile first
    profiler = DataProfiler()
    profile = profiler.profile(data, name=Path(args.input).stem)

    # Generate suite
    generator = GreatExpectationsGenerator()
    suite = generator.generate_suite(profile)

    output = json.dumps(suite, indent=2)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        logger.info(f"Expectation suite saved to {args.output}")
    else:
        print(output)


def cmd_contract(args):
    """Validate against data contract"""
    logger.info(f"Loading data from {args.input}")
    data = DataLoader.load(args.input)

    logger.info(f"Loading contract from {args.contract}")
    contract_validator = DataContractValidator()
    contract = contract_validator.load_contract(args.contract)

    results = contract_validator.validate_contract(data, contract)

    # Profile data
    profiler = DataProfiler()
    profile = profiler.profile(data, name=Path(args.input).stem)

    # Calculate score
    score_calc = QualityScoreCalculator()
    score = score_calc.calculate(profile, results)

    # Generate report
    reporter = ReportGenerator()

    if args.json:
        report = reporter.generate_json_report(profile, results, score)
        output = json.dumps(report, indent=2)
    else:
        output = reporter.generate_text_report(profile, results, score)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        logger.info(f"Report saved to {args.output}")
    else:
        print(output)

    # Exit with error if contract validation failed
    errors = sum(1 for r in results if not r.passed and r.severity == "error")
    if errors > 0:
        sys.exit(1)


def cmd_schema(args):
    """Generate schema from data"""
    logger.info(f"Loading data from {args.input}")
    data = DataLoader.load(args.input)

    if not data:
        logger.error("Empty dataset")
        sys.exit(1)

    # Profile to detect types
    profiler = DataProfiler()
    profile = profiler.profile(data, name=Path(args.input).stem)

    # Generate schema
    schema = {
        "name": profile.name,
        "version": "1.0",
        "columns": []
    }

    for col in profile.columns:
        col_schema = {
            "name": col.name,
            "type": col.data_type,
            "nullable": col.null_percentage > 0,
            "description": ""
        }

        if col.unique_percentage > 99:
            col_schema["unique"] = True

        if col.min_value is not None:
            col_schema["min_value"] = col.min_value
            col_schema["max_value"] = col.max_value

        if col.min_length is not None:
            col_schema["min_length"] = col.min_length
            col_schema["max_length"] = col.max_length

        if col.detected_pattern:
            col_schema["pattern"] = col.detected_pattern

        # Add allowed values for low-cardinality columns
        if col.unique_count <= 20 and col.unique_percentage < 10:
            col_schema["allowed_values"] = [v[0] for v in col.top_values]

        schema["columns"].append(col_schema)

    output = json.dumps(schema, indent=2)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        logger.info(f"Schema saved to {args.output}")
    else:
        print(output)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Data Quality Validator - Comprehensive data quality validation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Validate data against schema
  python data_quality_validator.py validate data.csv --schema schema.json

  # Profile data
  python data_quality_validator.py profile data.csv --output profile.json

  # Generate Great Expectations suite
  python data_quality_validator.py generate-suite data.csv --output expectations.json

  # Validate against data contract
  python data_quality_validator.py contract data.csv --contract contract.yaml

  # Generate schema from data
  python data_quality_validator.py schema data.csv --output schema.json
        """
    )

    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')

    subparsers = parser.add_subparsers(dest='command', help='Command to run')

    # Validate command
    validate_parser = subparsers.add_parser('validate', help='Validate data against schema')
    validate_parser.add_argument('input', help='Input data file (CSV, JSON, JSONL)')
    validate_parser.add_argument('--schema', '-s', help='Schema file (JSON)')
    validate_parser.add_argument('--output', '-o', help='Output report file')
    validate_parser.add_argument('--json', action='store_true', help='Output as JSON')
    validate_parser.add_argument('--detect-anomalies', action='store_true', help='Detect statistical anomalies')
    validate_parser.set_defaults(func=cmd_validate)

    # Profile command
    profile_parser = subparsers.add_parser('profile', help='Generate data profile')
    profile_parser.add_argument('input', help='Input data file')
    profile_parser.add_argument('--output', '-o', help='Output profile file')
    profile_parser.add_argument('--json', action='store_true', help='Output as JSON')
    profile_parser.set_defaults(func=cmd_profile)

    # Generate suite command
    suite_parser = subparsers.add_parser('generate-suite', help='Generate Great Expectations suite')
    suite_parser.add_argument('input', help='Input data file')
    suite_parser.add_argument('--output', '-o', help='Output expectations file')
    suite_parser.set_defaults(func=cmd_generate_suite)

    # Contract command
    contract_parser = subparsers.add_parser('contract', help='Validate against data contract')
    contract_parser.add_argument('input', help='Input data file')
    contract_parser.add_argument('--contract', '-c', required=True, help='Data contract file (YAML or JSON)')
    contract_parser.add_argument('--output', '-o', help='Output report file')
    contract_parser.add_argument('--json', action='store_true', help='Output as JSON')
    contract_parser.set_defaults(func=cmd_contract)

    # Schema command
    schema_parser = subparsers.add_parser('schema', help='Generate schema from data')
    schema_parser.add_argument('input', help='Input data file')
    schema_parser.add_argument('--output', '-o', help='Output schema file')
    schema_parser.set_defaults(func=cmd_schema)

    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    if not args.command:
        parser.print_help()
        sys.exit(1)

    try:
        args.func(args)
    except Exception as e:
        logger.error(f"Error: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == '__main__':
    main()
