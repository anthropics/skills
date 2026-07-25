#!/usr/bin/env python3
"""
ETL Performance Optimizer
Comprehensive ETL/ELT performance analysis and optimization tool.

Features:
- SQL query analysis and optimization recommendations
- Spark job configuration analysis
- Data skew detection and mitigation
- Partition strategy recommendations
- Join optimization suggestions
- Memory and shuffle analysis
- Cost estimation for cloud warehouses

Usage:
    python etl_performance_optimizer.py analyze-sql query.sql
    python etl_performance_optimizer.py analyze-spark spark-history.json
    python etl_performance_optimizer.py optimize-partition data_stats.json
    python etl_performance_optimizer.py estimate-cost query.sql --warehouse snowflake
"""

import os
import sys
import json
import re
import argparse
import logging
import math
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple, Set
from dataclasses import dataclass, field, asdict
from datetime import datetime
from collections import defaultdict
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
class SQLQueryInfo:
    """Parsed information about a SQL query"""
    query_type: str  # SELECT, INSERT, UPDATE, DELETE, MERGE, CREATE
    tables: List[str]
    columns: List[str]
    joins: List[Dict[str, str]]
    where_conditions: List[str]
    group_by: List[str]
    order_by: List[str]
    aggregations: List[str]
    subqueries: int
    distinct: bool
    limit: Optional[int]
    ctes: List[str]
    window_functions: List[str]
    estimated_complexity: str  # low, medium, high, very_high


@dataclass
class OptimizationRecommendation:
    """A single optimization recommendation"""
    category: str  # index, partition, join, filter, aggregation, memory, shuffle
    severity: str  # critical, high, medium, low
    title: str
    description: str
    current_issue: str
    recommendation: str
    expected_improvement: str
    implementation: str
    priority: int = 1


@dataclass
class SparkJobMetrics:
    """Metrics from a Spark job"""
    job_id: str
    duration_ms: int
    stages: int
    tasks: int
    shuffle_read_bytes: int
    shuffle_write_bytes: int
    input_bytes: int
    output_bytes: int
    peak_memory_bytes: int
    gc_time_ms: int
    failed_tasks: int
    speculative_tasks: int
    skew_ratio: float  # max_task_time / median_task_time


@dataclass
class PartitionStrategy:
    """Recommended partition strategy"""
    column: str
    partition_type: str  # range, hash, list
    num_partitions: Optional[int]
    partition_size_mb: float
    reasoning: str
    implementation: str


@dataclass
class CostEstimate:
    """Cost estimate for a query"""
    warehouse: str
    compute_cost: float
    storage_cost: float
    data_transfer_cost: float
    total_cost: float
    currency: str = "USD"
    assumptions: List[str] = field(default_factory=list)


# =============================================================================
# SQL Parser
# =============================================================================

class SQLParser:
    """Parse and analyze SQL queries"""

    # Common SQL patterns
    PATTERNS = {
        'select': re.compile(r'\bSELECT\b', re.IGNORECASE),
        'from': re.compile(r'\bFROM\b', re.IGNORECASE),
        'join': re.compile(r'\b(INNER|LEFT|RIGHT|FULL|CROSS)?\s*JOIN\b', re.IGNORECASE),
        'where': re.compile(r'\bWHERE\b', re.IGNORECASE),
        'group_by': re.compile(r'\bGROUP\s+BY\b', re.IGNORECASE),
        'order_by': re.compile(r'\bORDER\s+BY\b', re.IGNORECASE),
        'having': re.compile(r'\bHAVING\b', re.IGNORECASE),
        'distinct': re.compile(r'\bDISTINCT\b', re.IGNORECASE),
        'limit': re.compile(r'\bLIMIT\s+(\d+)', re.IGNORECASE),
        'cte': re.compile(r'\bWITH\b', re.IGNORECASE),
        'subquery': re.compile(r'\(\s*SELECT\b', re.IGNORECASE),
        'window': re.compile(r'\bOVER\s*\(', re.IGNORECASE),
        'aggregation': re.compile(r'\b(COUNT|SUM|AVG|MIN|MAX|STDDEV|VARIANCE)\s*\(', re.IGNORECASE),
        'insert': re.compile(r'\bINSERT\s+INTO\b', re.IGNORECASE),
        'update': re.compile(r'\bUPDATE\b', re.IGNORECASE),
        'delete': re.compile(r'\bDELETE\s+FROM\b', re.IGNORECASE),
        'merge': re.compile(r'\bMERGE\s+INTO\b', re.IGNORECASE),
        'create': re.compile(r'\bCREATE\s+(TABLE|VIEW|INDEX)\b', re.IGNORECASE),
    }

    def parse(self, sql: str) -> SQLQueryInfo:
        """Parse a SQL query and extract information"""
        # Clean up the query
        sql = self._clean_sql(sql)

        # Determine query type
        query_type = self._detect_query_type(sql)

        # Extract tables
        tables = self._extract_tables(sql)

        # Extract columns (for SELECT queries)
        columns = self._extract_columns(sql) if query_type == 'SELECT' else []

        # Extract joins
        joins = self._extract_joins(sql)

        # Extract WHERE conditions
        where_conditions = self._extract_where_conditions(sql)

        # Extract GROUP BY
        group_by = self._extract_group_by(sql)

        # Extract ORDER BY
        order_by = self._extract_order_by(sql)

        # Extract aggregations
        aggregations = self._extract_aggregations(sql)

        # Count subqueries
        subqueries = len(self.PATTERNS['subquery'].findall(sql))

        # Check for DISTINCT
        distinct = bool(self.PATTERNS['distinct'].search(sql))

        # Extract LIMIT
        limit_match = self.PATTERNS['limit'].search(sql)
        limit = int(limit_match.group(1)) if limit_match else None

        # Extract CTEs
        ctes = self._extract_ctes(sql)

        # Extract window functions
        window_functions = self._extract_window_functions(sql)

        # Estimate complexity
        complexity = self._estimate_complexity(
            tables, joins, subqueries, aggregations, window_functions
        )

        return SQLQueryInfo(
            query_type=query_type,
            tables=tables,
            columns=columns,
            joins=joins,
            where_conditions=where_conditions,
            group_by=group_by,
            order_by=order_by,
            aggregations=aggregations,
            subqueries=subqueries,
            distinct=distinct,
            limit=limit,
            ctes=ctes,
            window_functions=window_functions,
            estimated_complexity=complexity
        )

    def _clean_sql(self, sql: str) -> str:
        """Clean and normalize SQL"""
        # Remove comments
        sql = re.sub(r'--.*$', '', sql, flags=re.MULTILINE)
        sql = re.sub(r'/\*.*?\*/', '', sql, flags=re.DOTALL)
        # Normalize whitespace
        sql = ' '.join(sql.split())
        return sql

    def _detect_query_type(self, sql: str) -> str:
        """Detect the type of SQL query"""
        sql_upper = sql.upper().strip()

        if sql_upper.startswith('WITH') or sql_upper.startswith('SELECT'):
            return 'SELECT'
        elif self.PATTERNS['insert'].search(sql):
            return 'INSERT'
        elif self.PATTERNS['update'].search(sql):
            return 'UPDATE'
        elif self.PATTERNS['delete'].search(sql):
            return 'DELETE'
        elif self.PATTERNS['merge'].search(sql):
            return 'MERGE'
        elif self.PATTERNS['create'].search(sql):
            return 'CREATE'
        else:
            return 'UNKNOWN'

    def _extract_tables(self, sql: str) -> List[str]:
        """Extract table names from SQL"""
        tables = []

        # FROM clause tables
        from_pattern = re.compile(
            r'\bFROM\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)?)',
            re.IGNORECASE
        )
        tables.extend(from_pattern.findall(sql))

        # JOIN clause tables
        join_pattern = re.compile(
            r'\bJOIN\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)?)',
            re.IGNORECASE
        )
        tables.extend(join_pattern.findall(sql))

        # INSERT INTO table
        insert_pattern = re.compile(
            r'\bINSERT\s+INTO\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)?)',
            re.IGNORECASE
        )
        tables.extend(insert_pattern.findall(sql))

        # UPDATE table
        update_pattern = re.compile(
            r'\bUPDATE\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)?)',
            re.IGNORECASE
        )
        tables.extend(update_pattern.findall(sql))

        return list(set(tables))

    def _extract_columns(self, sql: str) -> List[str]:
        """Extract column references from SELECT clause"""
        # Find SELECT ... FROM
        match = re.search(r'\bSELECT\s+(.*?)\s+FROM\b', sql, re.IGNORECASE | re.DOTALL)
        if not match:
            return []

        select_clause = match.group(1)

        # Handle SELECT *
        if '*' in select_clause and 'COUNT(*)' not in select_clause.upper():
            return ['*']

        # Extract column names (simplified)
        columns = []
        for part in select_clause.split(','):
            part = part.strip()
            # Handle aliases
            alias_match = re.search(r'\bAS\s+(\w+)\s*$', part, re.IGNORECASE)
            if alias_match:
                columns.append(alias_match.group(1))
            else:
                # Get the last identifier
                col_match = re.search(r'([a-zA-Z_][a-zA-Z0-9_]*)(?:\s*$|\s+AS\b)', part, re.IGNORECASE)
                if col_match:
                    columns.append(col_match.group(1))

        return columns

    def _extract_joins(self, sql: str) -> List[Dict[str, str]]:
        """Extract join information"""
        joins = []

        join_pattern = re.compile(
            r'\b(INNER|LEFT\s+OUTER?|RIGHT\s+OUTER?|FULL\s+OUTER?|CROSS)?\s*JOIN\s+'
            r'([a-zA-Z_][a-zA-Z0-9_.]*)\s*(?:AS\s+)?(\w+)?\s*'
            r'(?:ON\s+(.+?))?(?=\s+(?:INNER|LEFT|RIGHT|FULL|CROSS|WHERE|GROUP|ORDER|HAVING|LIMIT|$))',
            re.IGNORECASE | re.DOTALL
        )

        for match in join_pattern.finditer(sql):
            join_type = match.group(1) or 'INNER'
            table = match.group(2)
            alias = match.group(3)
            condition = match.group(4)

            joins.append({
                'type': join_type.strip().upper(),
                'table': table,
                'alias': alias,
                'condition': condition.strip() if condition else None
            })

        return joins

    def _extract_where_conditions(self, sql: str) -> List[str]:
        """Extract WHERE clause conditions"""
        # Find WHERE ... (GROUP BY | ORDER BY | HAVING | LIMIT | end)
        match = re.search(
            r'\bWHERE\s+(.*?)(?=\s+(?:GROUP\s+BY|ORDER\s+BY|HAVING|LIMIT)|$)',
            sql, re.IGNORECASE | re.DOTALL
        )
        if not match:
            return []

        where_clause = match.group(1).strip()

        # Split by AND/OR (simplified)
        conditions = re.split(r'\s+AND\s+|\s+OR\s+', where_clause, flags=re.IGNORECASE)
        return [c.strip() for c in conditions if c.strip()]

    def _extract_group_by(self, sql: str) -> List[str]:
        """Extract GROUP BY columns"""
        match = re.search(
            r'\bGROUP\s+BY\s+(.*?)(?=\s+(?:HAVING|ORDER\s+BY|LIMIT)|$)',
            sql, re.IGNORECASE | re.DOTALL
        )
        if not match:
            return []

        group_clause = match.group(1).strip()
        columns = [c.strip() for c in group_clause.split(',')]
        return columns

    def _extract_order_by(self, sql: str) -> List[str]:
        """Extract ORDER BY columns"""
        match = re.search(
            r'\bORDER\s+BY\s+(.*?)(?=\s+LIMIT|$)',
            sql, re.IGNORECASE | re.DOTALL
        )
        if not match:
            return []

        order_clause = match.group(1).strip()
        columns = [c.strip() for c in order_clause.split(',')]
        return columns

    def _extract_aggregations(self, sql: str) -> List[str]:
        """Extract aggregation functions used"""
        agg_pattern = re.compile(
            r'\b(COUNT|SUM|AVG|MIN|MAX|STDDEV|VARIANCE|MEDIAN|PERCENTILE_CONT|PERCENTILE_DISC)\s*\(',
            re.IGNORECASE
        )
        return list(set(m.upper() for m in agg_pattern.findall(sql)))

    def _extract_ctes(self, sql: str) -> List[str]:
        """Extract CTE names"""
        cte_pattern = re.compile(
            r'\bWITH\s+(\w+)\s+AS\s*\(|,\s*(\w+)\s+AS\s*\(',
            re.IGNORECASE
        )
        ctes = []
        for match in cte_pattern.finditer(sql):
            cte_name = match.group(1) or match.group(2)
            if cte_name:
                ctes.append(cte_name)
        return ctes

    def _extract_window_functions(self, sql: str) -> List[str]:
        """Extract window function patterns"""
        window_pattern = re.compile(
            r'\b(\w+)\s*\([^)]*\)\s+OVER\s*\(',
            re.IGNORECASE
        )
        return list(set(m.upper() for m in window_pattern.findall(sql)))

    def _estimate_complexity(self, tables: List[str], joins: List[Dict],
                            subqueries: int, aggregations: List[str],
                            window_functions: List[str]) -> str:
        """Estimate query complexity"""
        score = 0

        # Table count
        score += len(tables) * 10

        # Join count and types
        for join in joins:
            if join['type'] in ('CROSS', 'FULL OUTER'):
                score += 30
            elif join['type'] in ('LEFT OUTER', 'RIGHT OUTER'):
                score += 20
            else:
                score += 15

        # Subqueries
        score += subqueries * 25

        # Aggregations
        score += len(aggregations) * 5

        # Window functions
        score += len(window_functions) * 15

        if score < 30:
            return 'low'
        elif score < 60:
            return 'medium'
        elif score < 100:
            return 'high'
        else:
            return 'very_high'


# =============================================================================
# SQL Optimizer
# =============================================================================

class SQLOptimizer:
    """Analyze SQL queries and provide optimization recommendations"""

    def analyze(self, query_info: SQLQueryInfo, sql: str) -> List[OptimizationRecommendation]:
        """Analyze a SQL query and generate optimization recommendations"""
        recommendations = []

        # Check for SELECT *
        if '*' in query_info.columns:
            recommendations.append(self._recommend_explicit_columns())

        # Check for missing WHERE clause on large tables
        if not query_info.where_conditions and query_info.tables:
            recommendations.append(self._recommend_add_filters())

        # Check for inefficient joins
        join_recs = self._analyze_joins(query_info)
        recommendations.extend(join_recs)

        # Check for DISTINCT usage
        if query_info.distinct:
            recommendations.append(self._recommend_distinct_alternative())

        # Check for ORDER BY without LIMIT
        if query_info.order_by and not query_info.limit:
            recommendations.append(self._recommend_add_limit())

        # Check for subquery optimization
        if query_info.subqueries > 0:
            recommendations.append(self._recommend_cte_conversion())

        # Check for index opportunities
        index_recs = self._analyze_index_opportunities(query_info)
        recommendations.extend(index_recs)

        # Check for partition pruning
        partition_recs = self._analyze_partition_pruning(query_info, sql)
        recommendations.extend(partition_recs)

        # Check for aggregation optimization
        if query_info.aggregations and query_info.group_by:
            agg_recs = self._analyze_aggregation(query_info)
            recommendations.extend(agg_recs)

        # Sort by priority
        recommendations.sort(key=lambda r: r.priority)

        return recommendations

    def _recommend_explicit_columns(self) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="query_structure",
            severity="medium",
            title="Avoid SELECT *",
            description="Using SELECT * retrieves all columns, increasing I/O and memory usage.",
            current_issue="Query uses SELECT * which fetches unnecessary columns",
            recommendation="Specify only the columns you need",
            expected_improvement="10-50% reduction in data scanned depending on table width",
            implementation="Replace SELECT * with SELECT col1, col2, col3 ...",
            priority=2
        )

    def _recommend_add_filters(self) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="filter",
            severity="high",
            title="Add WHERE Clause Filters",
            description="Query scans entire tables without filtering, causing full table scans.",
            current_issue="No WHERE clause filters found - full table scan required",
            recommendation="Add appropriate WHERE conditions to filter data early",
            expected_improvement="Up to 90%+ reduction in data processed if highly selective",
            implementation="Add WHERE column = value or WHERE date_column >= '2024-01-01'",
            priority=1
        )

    def _analyze_joins(self, query_info: SQLQueryInfo) -> List[OptimizationRecommendation]:
        """Analyze joins for optimization opportunities"""
        recommendations = []

        for join in query_info.joins:
            # Check for CROSS JOIN
            if join['type'] == 'CROSS':
                recommendations.append(OptimizationRecommendation(
                    category="join",
                    severity="critical",
                    title="Avoid CROSS JOIN",
                    description="CROSS JOIN creates a Cartesian product, which can explode data volume.",
                    current_issue=f"CROSS JOIN with table {join['table']} detected",
                    recommendation="Replace with appropriate INNER/LEFT JOIN with ON condition",
                    expected_improvement="Exponential reduction in intermediate data",
                    implementation=f"Convert CROSS JOIN {join['table']} to INNER JOIN {join['table']} ON ...",
                    priority=1
                ))

            # Check for missing join condition
            if not join.get('condition'):
                recommendations.append(OptimizationRecommendation(
                    category="join",
                    severity="high",
                    title="Missing Join Condition",
                    description="Join without explicit ON condition may cause Cartesian product.",
                    current_issue=f"JOIN with {join['table']} has no explicit ON condition",
                    recommendation="Add explicit ON condition to the join",
                    expected_improvement="Prevents accidental Cartesian products",
                    implementation=f"Add ON {join['table']}.id = other_table.foreign_key",
                    priority=1
                ))

        # Check for many joins
        if len(query_info.joins) > 5:
            recommendations.append(OptimizationRecommendation(
                category="join",
                severity="medium",
                title="High Number of Joins",
                description="Many joins can lead to complex execution plans and performance issues.",
                current_issue=f"{len(query_info.joins)} joins detected in single query",
                recommendation="Consider breaking into smaller queries or pre-aggregating",
                expected_improvement="Better plan optimization and memory usage",
                implementation="Use CTEs to materialize intermediate results, or denormalize frequently joined data",
                priority=3
            ))

        return recommendations

    def _recommend_distinct_alternative(self) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="query_structure",
            severity="medium",
            title="Consider Alternatives to DISTINCT",
            description="DISTINCT requires sorting/hashing all rows which can be expensive.",
            current_issue="DISTINCT used - may indicate data quality or join issues",
            recommendation="Review if DISTINCT is necessary or if joins produce duplicates",
            expected_improvement="Eliminates expensive deduplication step if not needed",
            implementation="Review join conditions, or use GROUP BY if aggregating anyway",
            priority=3
        )

    def _recommend_add_limit(self) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="query_structure",
            severity="low",
            title="Add LIMIT to ORDER BY",
            description="ORDER BY without LIMIT sorts entire result set unnecessarily.",
            current_issue="ORDER BY present without LIMIT clause",
            recommendation="Add LIMIT if only top N rows are needed",
            expected_improvement="Significant reduction in sorting overhead for large results",
            implementation="Add LIMIT 100 (or appropriate number) after ORDER BY",
            priority=4
        )

    def _recommend_cte_conversion(self) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="query_structure",
            severity="medium",
            title="Convert Subqueries to CTEs",
            description="Subqueries can be harder to optimize and maintain than CTEs.",
            current_issue="Subqueries detected in the query",
            recommendation="Convert correlated subqueries to CTEs or JOINs",
            expected_improvement="Better query plan optimization and readability",
            implementation="WITH subquery_name AS (SELECT ...) SELECT ... FROM main_table JOIN subquery_name",
            priority=3
        )

    def _analyze_index_opportunities(self, query_info: SQLQueryInfo) -> List[OptimizationRecommendation]:
        """Identify potential index opportunities"""
        recommendations = []

        # Columns in WHERE clause are index candidates
        where_columns = set()
        for condition in query_info.where_conditions:
            # Extract column names from conditions
            col_pattern = re.compile(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:=|>|<|>=|<=|<>|!=|LIKE|IN|BETWEEN)', re.IGNORECASE)
            where_columns.update(col_pattern.findall(condition))

        if where_columns:
            recommendations.append(OptimizationRecommendation(
                category="index",
                severity="medium",
                title="Consider Indexes on Filter Columns",
                description="Columns used in WHERE clauses benefit from indexes.",
                current_issue=f"Filter columns detected: {', '.join(where_columns)}",
                recommendation="Create indexes on frequently filtered columns",
                expected_improvement="Orders of magnitude faster for selective queries",
                implementation=f"CREATE INDEX idx_name ON table ({', '.join(list(where_columns)[:3])})",
                priority=2
            ))

        # JOIN columns are index candidates
        join_columns = set()
        for join in query_info.joins:
            if join.get('condition'):
                col_pattern = re.compile(r'\.([a-zA-Z_][a-zA-Z0-9_]*)\s*=', re.IGNORECASE)
                join_columns.update(col_pattern.findall(join['condition']))

        if join_columns:
            recommendations.append(OptimizationRecommendation(
                category="index",
                severity="high",
                title="Index Join Columns",
                description="Join columns without indexes cause expensive full table scans.",
                current_issue=f"Join columns detected: {', '.join(join_columns)}",
                recommendation="Ensure indexes exist on join key columns",
                expected_improvement="Dramatic improvement in join performance",
                implementation=f"CREATE INDEX idx_join ON table ({list(join_columns)[0]})",
                priority=1
            ))

        return recommendations

    def _analyze_partition_pruning(self, query_info: SQLQueryInfo, sql: str) -> List[OptimizationRecommendation]:
        """Check for partition pruning opportunities"""
        recommendations = []

        # Look for date/time columns in WHERE clause
        date_pattern = re.compile(
            r'\b(date|time|timestamp|created|updated|modified)_?\w*\s*(?:=|>|<|>=|<=|BETWEEN)',
            re.IGNORECASE
        )

        if date_pattern.search(sql):
            recommendations.append(OptimizationRecommendation(
                category="partition",
                severity="medium",
                title="Leverage Partition Pruning",
                description="Date-based filters can leverage partitioned tables for massive speedups.",
                current_issue="Date/time filter detected - ensure table is partitioned",
                recommendation="Partition table by date column and ensure filter format matches",
                expected_improvement="90%+ reduction in data scanned for time-bounded queries",
                implementation="CREATE TABLE ... PARTITION BY RANGE (date_column) or use dynamic partitioning",
                priority=2
            ))

        return recommendations

    def _analyze_aggregation(self, query_info: SQLQueryInfo) -> List[OptimizationRecommendation]:
        """Analyze aggregation patterns"""
        recommendations = []

        # High cardinality GROUP BY warning
        if len(query_info.group_by) > 3:
            recommendations.append(OptimizationRecommendation(
                category="aggregation",
                severity="medium",
                title="High Cardinality GROUP BY",
                description="Grouping by many columns increases memory usage and reduces aggregation benefit.",
                current_issue=f"GROUP BY with {len(query_info.group_by)} columns detected",
                recommendation="Review if all group by columns are necessary",
                expected_improvement="Reduced memory and faster aggregation",
                implementation="Remove non-essential GROUP BY columns or pre-aggregate",
                priority=3
            ))

        # COUNT DISTINCT optimization
        if 'COUNT' in query_info.aggregations and query_info.distinct:
            recommendations.append(OptimizationRecommendation(
                category="aggregation",
                severity="medium",
                title="Optimize COUNT DISTINCT",
                description="COUNT DISTINCT can be expensive for high cardinality columns.",
                current_issue="COUNT DISTINCT pattern detected",
                recommendation="Consider HyperLogLog approximation for very large datasets",
                expected_improvement="Massive speedup with ~2% error tolerance",
                implementation="Use APPROX_COUNT_DISTINCT() if available in your warehouse",
                priority=3
            ))

        return recommendations


# =============================================================================
# Spark Job Analyzer
# =============================================================================

class SparkJobAnalyzer:
    """Analyze Spark job metrics and provide optimization recommendations"""

    def analyze(self, metrics: SparkJobMetrics) -> List[OptimizationRecommendation]:
        """Analyze Spark job metrics"""
        recommendations = []

        # Check for data skew
        if metrics.skew_ratio > 5:
            recommendations.append(self._recommend_skew_mitigation(metrics))

        # Check for excessive shuffle
        shuffle_ratio = metrics.shuffle_write_bytes / max(metrics.input_bytes, 1)
        if shuffle_ratio > 1.5:
            recommendations.append(self._recommend_reduce_shuffle(metrics, shuffle_ratio))

        # Check for GC overhead
        gc_ratio = metrics.gc_time_ms / max(metrics.duration_ms, 1)
        if gc_ratio > 0.1:
            recommendations.append(self._recommend_memory_tuning(metrics, gc_ratio))

        # Check for failed tasks
        if metrics.failed_tasks > 0:
            fail_ratio = metrics.failed_tasks / max(metrics.tasks, 1)
            recommendations.append(self._recommend_failure_handling(metrics, fail_ratio))

        # Check for speculative execution overhead
        if metrics.speculative_tasks > metrics.tasks * 0.1:
            recommendations.append(self._recommend_reduce_speculation(metrics))

        # Check task count
        if metrics.tasks > 10000:
            recommendations.append(self._recommend_reduce_tasks(metrics))
        elif metrics.tasks < 10 and metrics.input_bytes > 1e9:
            recommendations.append(self._recommend_increase_parallelism(metrics))

        return recommendations

    def _recommend_skew_mitigation(self, metrics: SparkJobMetrics) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="skew",
            severity="critical",
            title="Severe Data Skew Detected",
            description=f"Skew ratio of {metrics.skew_ratio:.1f}x indicates uneven data distribution.",
            current_issue=f"Task execution time varies by {metrics.skew_ratio:.1f}x, causing stragglers",
            recommendation="Apply skew handling techniques to rebalance data",
            expected_improvement="Up to 80% reduction in job time by eliminating stragglers",
            implementation="""Options:
1. Salting: Add random prefix to skewed keys
   df.withColumn("salted_key", concat(col("key"), lit("_"), (rand() * 10).cast("int")))
2. Broadcast join for small tables:
   df1.join(broadcast(df2), "key")
3. Adaptive Query Execution (Spark 3.0+):
   spark.conf.set("spark.sql.adaptive.enabled", "true")
   spark.conf.set("spark.sql.adaptive.skewJoin.enabled", "true")""",
            priority=1
        )

    def _recommend_reduce_shuffle(self, metrics: SparkJobMetrics, ratio: float) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="shuffle",
            severity="high",
            title="Excessive Shuffle Data",
            description=f"Shuffle writes {ratio:.1f}x the input data size.",
            current_issue=f"Shuffle write: {metrics.shuffle_write_bytes / 1e9:.2f} GB vs input: {metrics.input_bytes / 1e9:.2f} GB",
            recommendation="Reduce shuffle through partitioning and early aggregation",
            expected_improvement="Significant network I/O and storage reduction",
            implementation="""Options:
1. Pre-aggregate before shuffle:
   df.groupBy("key").agg(sum("value")).repartition("key")
2. Use map-side combining:
   df.reduceByKey((a, b) => a + b)
3. Optimize partition count:
   spark.conf.set("spark.sql.shuffle.partitions", optimal_count)
4. Use bucketing for repeated joins:
   df.write.bucketBy(200, "key").saveAsTable("bucketed_table")""",
            priority=1
        )

    def _recommend_memory_tuning(self, metrics: SparkJobMetrics, gc_ratio: float) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="memory",
            severity="high",
            title="High GC Overhead",
            description=f"GC time is {gc_ratio * 100:.1f}% of total execution time.",
            current_issue=f"GC time: {metrics.gc_time_ms / 1000:.1f}s out of {metrics.duration_ms / 1000:.1f}s total",
            recommendation="Tune memory settings to reduce garbage collection",
            expected_improvement="20-50% faster execution with proper memory config",
            implementation="""Memory tuning options:
1. Increase executor memory:
   --executor-memory 8g
2. Adjust memory fractions:
   spark.memory.fraction=0.6
   spark.memory.storageFraction=0.5
3. Use off-heap memory:
   spark.memory.offHeap.enabled=true
   spark.memory.offHeap.size=4g
4. Reduce cached data:
   df.unpersist() when no longer needed
5. Use Kryo serialization:
   spark.serializer=org.apache.spark.serializer.KryoSerializer""",
            priority=2
        )

    def _recommend_failure_handling(self, metrics: SparkJobMetrics, fail_ratio: float) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="reliability",
            severity="high" if fail_ratio > 0.1 else "medium",
            title="Task Failures Detected",
            description=f"{metrics.failed_tasks} tasks failed ({fail_ratio * 100:.1f}% failure rate).",
            current_issue="Task failures increase job time and resource usage due to retries",
            recommendation="Investigate failure causes and add resilience",
            expected_improvement="Reduced retries and more predictable job times",
            implementation="""Failure handling options:
1. Check executor logs for OOM:
   spark.executor.memoryOverhead=2g
2. Handle data issues:
   df.filter(col("value").isNotNull())
3. Increase task retries:
   spark.task.maxFailures=4
4. Add checkpointing for long jobs:
   df.checkpoint()
5. Check for network timeouts:
   spark.network.timeout=300s""",
            priority=1
        )

    def _recommend_reduce_speculation(self, metrics: SparkJobMetrics) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="execution",
            severity="medium",
            title="High Speculative Execution",
            description=f"{metrics.speculative_tasks} speculative tasks launched.",
            current_issue="Excessive speculation wastes resources and indicates underlying issues",
            recommendation="Address root cause of slow tasks instead of speculation",
            expected_improvement="Better resource utilization",
            implementation="""Options:
1. Disable speculation if not needed:
   spark.speculation=false
2. Or tune speculation settings:
   spark.speculation.multiplier=1.5
   spark.speculation.quantile=0.9
3. Fix underlying skew/memory issues first""",
            priority=3
        )

    def _recommend_reduce_tasks(self, metrics: SparkJobMetrics) -> OptimizationRecommendation:
        return OptimizationRecommendation(
            category="parallelism",
            severity="medium",
            title="Too Many Tasks",
            description=f"{metrics.tasks} tasks may cause excessive scheduling overhead.",
            current_issue="Very high task count increases driver overhead",
            recommendation="Reduce partition count for better efficiency",
            expected_improvement="Reduced scheduling overhead and driver memory usage",
            implementation=f"""
1. Reduce shuffle partitions:
   spark.sql.shuffle.partitions={max(200, metrics.tasks // 10)}
2. Coalesce partitions:
   df.coalesce({max(200, metrics.tasks // 10)})
3. Use adaptive partitioning (Spark 3.0+):
   spark.sql.adaptive.enabled=true""",
            priority=3
        )

    def _recommend_increase_parallelism(self, metrics: SparkJobMetrics) -> OptimizationRecommendation:
        recommended_partitions = max(200, int(metrics.input_bytes / (128 * 1e6)))  # 128MB per partition
        return OptimizationRecommendation(
            category="parallelism",
            severity="high",
            title="Low Parallelism",
            description=f"Only {metrics.tasks} tasks for {metrics.input_bytes / 1e9:.2f} GB of data.",
            current_issue="Under-utilization of cluster resources",
            recommendation="Increase parallelism to better utilize cluster",
            expected_improvement="Linear speedup with added parallelism",
            implementation=f"""
1. Increase shuffle partitions:
   spark.sql.shuffle.partitions={recommended_partitions}
2. Repartition input:
   df.repartition({recommended_partitions})
3. Adjust default parallelism:
   spark.default.parallelism={recommended_partitions}""",
            priority=2
        )


# =============================================================================
# Partition Strategy Advisor
# =============================================================================

class PartitionAdvisor:
    """Recommend partitioning strategies based on data characteristics"""

    def recommend(self, data_stats: Dict) -> List[PartitionStrategy]:
        """Generate partition recommendations from data statistics"""
        recommendations = []

        columns = data_stats.get('columns', {})
        total_size_bytes = data_stats.get('total_size_bytes', 0)
        row_count = data_stats.get('row_count', 0)

        for col_name, col_stats in columns.items():
            strategy = self._evaluate_column(col_name, col_stats, total_size_bytes, row_count)
            if strategy:
                recommendations.append(strategy)

        # Sort by partition effectiveness
        recommendations.sort(key=lambda s: s.partition_size_mb)

        return recommendations[:3]  # Top 3 recommendations

    def _evaluate_column(self, col_name: str, col_stats: Dict,
                        total_size_bytes: int, row_count: int) -> Optional[PartitionStrategy]:
        """Evaluate a column for partitioning potential"""
        cardinality = col_stats.get('cardinality', 0)
        data_type = col_stats.get('data_type', 'string')
        null_percentage = col_stats.get('null_percentage', 0)

        # Skip high-null columns
        if null_percentage > 20:
            return None

        # Date/timestamp columns are ideal for range partitioning
        if data_type in ('date', 'timestamp', 'datetime'):
            return self._recommend_date_partition(col_name, col_stats, total_size_bytes, row_count)

        # Low cardinality columns are good for list partitioning
        if cardinality and cardinality <= 100:
            return self._recommend_list_partition(col_name, col_stats, total_size_bytes, cardinality)

        # Medium cardinality columns can use hash partitioning
        if cardinality and 100 < cardinality <= 10000:
            return self._recommend_hash_partition(col_name, col_stats, total_size_bytes)

        return None

    def _recommend_date_partition(self, col_name: str, col_stats: Dict,
                                  total_size_bytes: int, row_count: int) -> PartitionStrategy:
        # Estimate daily partition size (assume 365 days of data)
        estimated_days = 365
        partition_size_mb = (total_size_bytes / estimated_days) / (1024 * 1024)

        return PartitionStrategy(
            column=col_name,
            partition_type="range",
            num_partitions=None,  # Dynamic based on date range
            partition_size_mb=partition_size_mb,
            reasoning=f"Date column '{col_name}' is ideal for range partitioning. "
                     f"Estimated daily partition size: {partition_size_mb:.1f} MB",
            implementation=f"""
-- BigQuery
CREATE TABLE table_name
PARTITION BY DATE({col_name})
AS SELECT * FROM source_table;

-- Snowflake
CREATE TABLE table_name
CLUSTER BY (DATE_TRUNC('DAY', {col_name}));

-- Spark/Hive
df.write.partitionBy("{col_name}").parquet("path")

-- PostgreSQL
CREATE TABLE table_name (...)
PARTITION BY RANGE ({col_name});"""
        )

    def _recommend_list_partition(self, col_name: str, col_stats: Dict,
                                  total_size_bytes: int, cardinality: int) -> PartitionStrategy:
        partition_size_mb = (total_size_bytes / cardinality) / (1024 * 1024)

        return PartitionStrategy(
            column=col_name,
            partition_type="list",
            num_partitions=cardinality,
            partition_size_mb=partition_size_mb,
            reasoning=f"Column '{col_name}' has {cardinality} distinct values - ideal for list partitioning. "
                     f"Estimated partition size: {partition_size_mb:.1f} MB",
            implementation=f"""
-- Spark/Hive
df.write.partitionBy("{col_name}").parquet("path")

-- PostgreSQL
CREATE TABLE table_name (...)
PARTITION BY LIST ({col_name});

-- Note: List partitioning works best with stable, low-cardinality values"""
        )

    def _recommend_hash_partition(self, col_name: str, col_stats: Dict,
                                  total_size_bytes: int) -> PartitionStrategy:
        # Target ~128MB partitions
        target_partition_size = 128 * 1024 * 1024
        num_partitions = max(1, int(total_size_bytes / target_partition_size))

        # Round to power of 2 for better distribution
        num_partitions = 2 ** int(math.log2(num_partitions) + 0.5)
        partition_size_mb = (total_size_bytes / num_partitions) / (1024 * 1024)

        return PartitionStrategy(
            column=col_name,
            partition_type="hash",
            num_partitions=num_partitions,
            partition_size_mb=partition_size_mb,
            reasoning=f"Column '{col_name}' has medium cardinality - hash partitioning provides even distribution. "
                     f"Recommended {num_partitions} partitions (~{partition_size_mb:.1f} MB each)",
            implementation=f"""
-- Spark
df.repartition({num_partitions}, col("{col_name}"))

-- PostgreSQL
CREATE TABLE table_name (...)
PARTITION BY HASH ({col_name});

-- Snowflake (clustering)
ALTER TABLE table_name CLUSTER BY ({col_name});"""
        )


# =============================================================================
# Cost Estimator
# =============================================================================

class CostEstimator:
    """Estimate query costs for cloud data warehouses"""

    # Pricing (approximate, varies by region and contract)
    PRICING = {
        'snowflake': {
            'compute_per_credit': 2.00,  # USD per credit
            'credits_per_hour': {
                'x-small': 1,
                'small': 2,
                'medium': 4,
                'large': 8,
                'x-large': 16,
            },
            'storage_per_tb_month': 23.00,
        },
        'bigquery': {
            'on_demand_per_tb': 5.00,  # USD per TB scanned
            'storage_per_tb_month': 20.00,
            'streaming_insert_per_gb': 0.01,
        },
        'redshift': {
            'dc2_large_per_hour': 0.25,
            'ra3_xlarge_per_hour': 1.086,
            'storage_per_gb_month': 0.024,
        },
        'databricks': {
            'dbu_per_hour_sql': 0.22,
            'dbu_per_hour_jobs': 0.15,
        }
    }

    def estimate(self, query_info: SQLQueryInfo, warehouse: str,
                data_stats: Optional[Dict] = None) -> CostEstimate:
        """Estimate query cost"""
        warehouse = warehouse.lower()

        if warehouse not in self.PRICING:
            raise ValueError(f"Unknown warehouse: {warehouse}. Supported: {list(self.PRICING.keys())}")

        # Estimate data scanned
        data_scanned_bytes = self._estimate_data_scanned(query_info, data_stats)
        data_scanned_tb = data_scanned_bytes / (1024 ** 4)

        if warehouse == 'bigquery':
            return self._estimate_bigquery(query_info, data_scanned_tb, data_stats)
        elif warehouse == 'snowflake':
            return self._estimate_snowflake(query_info, data_scanned_tb, data_stats)
        elif warehouse == 'redshift':
            return self._estimate_redshift(query_info, data_scanned_tb, data_stats)
        elif warehouse == 'databricks':
            return self._estimate_databricks(query_info, data_scanned_tb, data_stats)

    def _estimate_data_scanned(self, query_info: SQLQueryInfo,
                               data_stats: Optional[Dict]) -> int:
        """Estimate bytes of data that will be scanned"""
        if data_stats and 'total_size_bytes' in data_stats:
            base_size = data_stats['total_size_bytes']
        else:
            # Default assumption: 1GB per table
            base_size = len(query_info.tables) * 1e9

        # Adjust for filters
        filter_factor = 1.0
        if query_info.where_conditions:
            # Assume each filter reduces data by 50% (very rough)
            filter_factor = 0.5 ** min(len(query_info.where_conditions), 3)

        # Adjust for column projection
        if '*' not in query_info.columns and query_info.columns:
            # Assume selecting specific columns reduces scan by 50%
            filter_factor *= 0.5

        return int(base_size * filter_factor)

    def _estimate_bigquery(self, query_info: SQLQueryInfo,
                          data_scanned_tb: float, data_stats: Optional[Dict]) -> CostEstimate:
        pricing = self.PRICING['bigquery']

        compute_cost = data_scanned_tb * pricing['on_demand_per_tb']

        # Minimum billing of 10MB
        if data_scanned_tb < 10 / (1024 ** 2):
            compute_cost = 10 / (1024 ** 2) * pricing['on_demand_per_tb']

        return CostEstimate(
            warehouse='BigQuery',
            compute_cost=compute_cost,
            storage_cost=0,  # Storage cost separate
            data_transfer_cost=0,
            total_cost=compute_cost,
            assumptions=[
                f"Estimated {data_scanned_tb * 1024:.2f} GB data scanned",
                "Using on-demand pricing ($5/TB)",
                "Assumes no slot reservations",
                "Actual cost depends on partitioning and clustering"
            ]
        )

    def _estimate_snowflake(self, query_info: SQLQueryInfo,
                           data_scanned_tb: float, data_stats: Optional[Dict]) -> CostEstimate:
        pricing = self.PRICING['snowflake']

        # Estimate warehouse size and time
        complexity_to_size = {
            'low': 'x-small',
            'medium': 'small',
            'high': 'medium',
            'very_high': 'large'
        }
        warehouse_size = complexity_to_size.get(query_info.estimated_complexity, 'small')
        credits_per_hour = pricing['credits_per_hour'][warehouse_size]

        # Estimate runtime (very rough)
        estimated_seconds = max(1, data_scanned_tb * 1024 * 10)  # 10 seconds per GB
        estimated_hours = estimated_seconds / 3600

        credits_used = credits_per_hour * estimated_hours
        compute_cost = credits_used * pricing['compute_per_credit']

        # Minimum 1 minute billing
        min_cost = (credits_per_hour / 60) * pricing['compute_per_credit']
        compute_cost = max(compute_cost, min_cost)

        return CostEstimate(
            warehouse='Snowflake',
            compute_cost=compute_cost,
            storage_cost=0,
            data_transfer_cost=0,
            total_cost=compute_cost,
            assumptions=[
                f"Warehouse size: {warehouse_size}",
                f"Estimated runtime: {estimated_seconds:.1f} seconds",
                f"Credits used: {credits_used:.4f}",
                "Minimum 1-minute billing applies",
                "Actual cost depends on warehouse auto-suspend settings"
            ]
        )

    def _estimate_redshift(self, query_info: SQLQueryInfo,
                          data_scanned_tb: float, data_stats: Optional[Dict]) -> CostEstimate:
        pricing = self.PRICING['redshift']

        # Assume RA3 xl node type
        hourly_rate = pricing['ra3_xlarge_per_hour']

        # Estimate runtime
        estimated_seconds = max(1, data_scanned_tb * 1024 * 15)  # 15 seconds per GB
        estimated_hours = estimated_seconds / 3600

        compute_cost = hourly_rate * estimated_hours

        return CostEstimate(
            warehouse='Redshift',
            compute_cost=compute_cost,
            storage_cost=0,
            data_transfer_cost=0,
            total_cost=compute_cost,
            assumptions=[
                f"Using RA3.xlplus node type",
                f"Estimated runtime: {estimated_seconds:.1f} seconds",
                "Assumes dedicated cluster (not serverless)",
                "Actual cost depends on cluster configuration"
            ]
        )

    def _estimate_databricks(self, query_info: SQLQueryInfo,
                            data_scanned_tb: float, data_stats: Optional[Dict]) -> CostEstimate:
        pricing = self.PRICING['databricks']

        # Estimate DBUs
        estimated_seconds = max(1, data_scanned_tb * 1024 * 12)
        estimated_hours = estimated_seconds / 3600

        dbu_cost = pricing['dbu_per_hour_sql'] * estimated_hours

        return CostEstimate(
            warehouse='Databricks',
            compute_cost=dbu_cost,
            storage_cost=0,
            data_transfer_cost=0,
            total_cost=dbu_cost,
            assumptions=[
                f"Using SQL warehouse",
                f"Estimated runtime: {estimated_seconds:.1f} seconds",
                "DBU rate may vary by workspace tier",
                "Does not include underlying cloud costs"
            ]
        )


# =============================================================================
# Report Generator
# =============================================================================

class ReportGenerator:
    """Generate optimization reports"""

    def generate_text_report(self, query_info: SQLQueryInfo,
                            recommendations: List[OptimizationRecommendation],
                            cost_estimate: Optional[CostEstimate] = None) -> str:
        """Generate a text report"""
        lines = []
        lines.append("=" * 80)
        lines.append("ETL PERFORMANCE OPTIMIZATION REPORT")
        lines.append("=" * 80)
        lines.append(f"\nGenerated: {datetime.now().isoformat()}")

        # Query summary
        lines.append("\n" + "-" * 40)
        lines.append("QUERY ANALYSIS")
        lines.append("-" * 40)
        lines.append(f"Query Type: {query_info.query_type}")
        lines.append(f"Tables: {', '.join(query_info.tables) or 'None'}")
        lines.append(f"Joins: {len(query_info.joins)}")
        lines.append(f"Subqueries: {query_info.subqueries}")
        lines.append(f"Aggregations: {', '.join(query_info.aggregations) or 'None'}")
        lines.append(f"Window Functions: {', '.join(query_info.window_functions) or 'None'}")
        lines.append(f"Complexity: {query_info.estimated_complexity.upper()}")

        # Cost estimate
        if cost_estimate:
            lines.append("\n" + "-" * 40)
            lines.append("COST ESTIMATE")
            lines.append("-" * 40)
            lines.append(f"Warehouse: {cost_estimate.warehouse}")
            lines.append(f"Estimated Cost: ${cost_estimate.total_cost:.4f} {cost_estimate.currency}")
            lines.append("Assumptions:")
            for assumption in cost_estimate.assumptions:
                lines.append(f"  - {assumption}")

        # Recommendations
        if recommendations:
            lines.append("\n" + "-" * 40)
            lines.append(f"OPTIMIZATION RECOMMENDATIONS ({len(recommendations)} found)")
            lines.append("-" * 40)

            for i, rec in enumerate(recommendations, 1):
                severity_icon = {
                    'critical': '🔴',
                    'high': '🟠',
                    'medium': '🟡',
                    'low': '🟢'
                }.get(rec.severity, '⚪')

                lines.append(f"\n{i}. {severity_icon} [{rec.severity.upper()}] {rec.title}")
                lines.append(f"   Category: {rec.category}")
                lines.append(f"   Issue: {rec.current_issue}")
                lines.append(f"   Recommendation: {rec.recommendation}")
                lines.append(f"   Expected Improvement: {rec.expected_improvement}")
                lines.append(f"\n   Implementation:")
                for impl_line in rec.implementation.strip().split('\n'):
                    lines.append(f"   {impl_line}")
        else:
            lines.append("\n✅ No optimization issues detected")

        lines.append("\n" + "=" * 80)

        return "\n".join(lines)

    def generate_json_report(self, query_info: SQLQueryInfo,
                            recommendations: List[OptimizationRecommendation],
                            cost_estimate: Optional[CostEstimate] = None) -> Dict:
        """Generate a JSON report"""
        return {
            "report_type": "etl_performance_optimization",
            "generated_at": datetime.now().isoformat(),
            "query_analysis": {
                "query_type": query_info.query_type,
                "tables": query_info.tables,
                "joins": query_info.joins,
                "subqueries": query_info.subqueries,
                "aggregations": query_info.aggregations,
                "window_functions": query_info.window_functions,
                "complexity": query_info.estimated_complexity
            },
            "cost_estimate": asdict(cost_estimate) if cost_estimate else None,
            "recommendations": [asdict(r) for r in recommendations],
            "summary": {
                "total_recommendations": len(recommendations),
                "critical": sum(1 for r in recommendations if r.severity == "critical"),
                "high": sum(1 for r in recommendations if r.severity == "high"),
                "medium": sum(1 for r in recommendations if r.severity == "medium"),
                "low": sum(1 for r in recommendations if r.severity == "low")
            }
        }


# =============================================================================
# CLI Commands
# =============================================================================

def cmd_analyze_sql(args):
    """Analyze SQL query for optimization opportunities"""
    # Load SQL
    sql_path = Path(args.input)
    if sql_path.exists():
        with open(sql_path, 'r') as f:
            sql = f.read()
    else:
        sql = args.input  # Treat as inline SQL

    # Parse and analyze
    parser = SQLParser()
    query_info = parser.parse(sql)

    optimizer = SQLOptimizer()
    recommendations = optimizer.analyze(query_info, sql)

    # Cost estimate if warehouse specified
    cost_estimate = None
    if args.warehouse:
        estimator = CostEstimator()
        data_stats = None
        if args.stats:
            with open(args.stats, 'r') as f:
                data_stats = json.load(f)
        cost_estimate = estimator.estimate(query_info, args.warehouse, data_stats)

    # Generate report
    reporter = ReportGenerator()

    if args.json:
        report = reporter.generate_json_report(query_info, recommendations, cost_estimate)
        output = json.dumps(report, indent=2)
    else:
        output = reporter.generate_text_report(query_info, recommendations, cost_estimate)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        logger.info(f"Report saved to {args.output}")
    else:
        print(output)


def cmd_analyze_spark(args):
    """Analyze Spark job metrics"""
    with open(args.input, 'r') as f:
        metrics_data = json.load(f)

    # Handle both single job and array of jobs
    if isinstance(metrics_data, list):
        jobs = metrics_data
    else:
        jobs = [metrics_data]

    all_recommendations = []
    analyzer = SparkJobAnalyzer()

    for job_data in jobs:
        metrics = SparkJobMetrics(
            job_id=job_data.get('jobId', 'unknown'),
            duration_ms=job_data.get('duration', 0),
            stages=job_data.get('numStages', 0),
            tasks=job_data.get('numTasks', 0),
            shuffle_read_bytes=job_data.get('shuffleReadBytes', 0),
            shuffle_write_bytes=job_data.get('shuffleWriteBytes', 0),
            input_bytes=job_data.get('inputBytes', 0),
            output_bytes=job_data.get('outputBytes', 0),
            peak_memory_bytes=job_data.get('peakMemoryBytes', 0),
            gc_time_ms=job_data.get('gcTime', 0),
            failed_tasks=job_data.get('failedTasks', 0),
            speculative_tasks=job_data.get('speculativeTasks', 0),
            skew_ratio=job_data.get('skewRatio', 1.0)
        )

        recommendations = analyzer.analyze(metrics)
        all_recommendations.extend(recommendations)

    # Deduplicate similar recommendations
    unique_recs = []
    seen_titles = set()
    for rec in all_recommendations:
        if rec.title not in seen_titles:
            unique_recs.append(rec)
            seen_titles.add(rec.title)

    # Output
    if args.json:
        output = json.dumps([asdict(r) for r in unique_recs], indent=2)
    else:
        lines = []
        lines.append("=" * 60)
        lines.append("SPARK JOB OPTIMIZATION REPORT")
        lines.append("=" * 60)
        lines.append(f"\nJobs Analyzed: {len(jobs)}")
        lines.append(f"Recommendations: {len(unique_recs)}")

        for i, rec in enumerate(unique_recs, 1):
            lines.append(f"\n{i}. [{rec.severity.upper()}] {rec.title}")
            lines.append(f"   {rec.description}")
            lines.append(f"   Implementation: {rec.implementation[:200]}...")

        output = "\n".join(lines)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
    else:
        print(output)


def cmd_optimize_partition(args):
    """Recommend partition strategies"""
    with open(args.input, 'r') as f:
        data_stats = json.load(f)

    advisor = PartitionAdvisor()
    strategies = advisor.recommend(data_stats)

    if args.json:
        output = json.dumps([asdict(s) for s in strategies], indent=2)
    else:
        lines = []
        lines.append("=" * 60)
        lines.append("PARTITION STRATEGY RECOMMENDATIONS")
        lines.append("=" * 60)

        if not strategies:
            lines.append("\nNo partition recommendations based on provided data statistics.")
        else:
            for i, strategy in enumerate(strategies, 1):
                lines.append(f"\n{i}. Partition by: {strategy.column}")
                lines.append(f"   Type: {strategy.partition_type}")
                if strategy.num_partitions:
                    lines.append(f"   Partitions: {strategy.num_partitions}")
                lines.append(f"   Estimated size: {strategy.partition_size_mb:.1f} MB per partition")
                lines.append(f"   Reasoning: {strategy.reasoning}")
                lines.append(f"\n   Implementation:")
                for impl_line in strategy.implementation.strip().split('\n'):
                    lines.append(f"   {impl_line}")

        output = "\n".join(lines)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
    else:
        print(output)


def cmd_estimate_cost(args):
    """Estimate query cost"""
    # Load SQL
    sql_path = Path(args.input)
    if sql_path.exists():
        with open(sql_path, 'r') as f:
            sql = f.read()
    else:
        sql = args.input

    # Parse
    parser = SQLParser()
    query_info = parser.parse(sql)

    # Load data stats if provided
    data_stats = None
    if args.stats:
        with open(args.stats, 'r') as f:
            data_stats = json.load(f)

    # Estimate cost
    estimator = CostEstimator()
    cost = estimator.estimate(query_info, args.warehouse, data_stats)

    if args.json:
        output = json.dumps(asdict(cost), indent=2)
    else:
        lines = []
        lines.append(f"Cost Estimate for {cost.warehouse}")
        lines.append("=" * 40)
        lines.append(f"Compute Cost:      ${cost.compute_cost:.4f}")
        lines.append(f"Storage Cost:      ${cost.storage_cost:.4f}")
        lines.append(f"Data Transfer:     ${cost.data_transfer_cost:.4f}")
        lines.append("-" * 40)
        lines.append(f"Total:             ${cost.total_cost:.4f} {cost.currency}")
        lines.append("\nAssumptions:")
        for assumption in cost.assumptions:
            lines.append(f"  - {assumption}")

        output = "\n".join(lines)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
    else:
        print(output)


def cmd_generate_template(args):
    """Generate template files"""
    templates = {
        'data_stats': {
            "total_size_bytes": 10737418240,
            "row_count": 10000000,
            "columns": {
                "id": {
                    "data_type": "integer",
                    "cardinality": 10000000,
                    "null_percentage": 0
                },
                "created_at": {
                    "data_type": "timestamp",
                    "cardinality": 1000000,
                    "null_percentage": 0
                },
                "category": {
                    "data_type": "string",
                    "cardinality": 50,
                    "null_percentage": 2
                },
                "amount": {
                    "data_type": "float",
                    "cardinality": 100000,
                    "null_percentage": 5
                }
            }
        },
        'spark_metrics': {
            "jobId": "job_12345",
            "duration": 300000,
            "numStages": 5,
            "numTasks": 200,
            "shuffleReadBytes": 5368709120,
            "shuffleWriteBytes": 2147483648,
            "inputBytes": 10737418240,
            "outputBytes": 1073741824,
            "peakMemoryBytes": 4294967296,
            "gcTime": 15000,
            "failedTasks": 2,
            "speculativeTasks": 5,
            "skewRatio": 3.5
        }
    }

    if args.template not in templates:
        logger.error(f"Unknown template: {args.template}. Available: {list(templates.keys())}")
        sys.exit(1)

    output = json.dumps(templates[args.template], indent=2)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
        logger.info(f"Template saved to {args.output}")
    else:
        print(output)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="ETL Performance Optimizer - Analyze and optimize data pipelines",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Analyze SQL query
  python etl_performance_optimizer.py analyze-sql query.sql

  # Analyze with cost estimate
  python etl_performance_optimizer.py analyze-sql query.sql --warehouse bigquery

  # Analyze Spark job metrics
  python etl_performance_optimizer.py analyze-spark spark-history.json

  # Get partition recommendations
  python etl_performance_optimizer.py optimize-partition data_stats.json

  # Estimate query cost
  python etl_performance_optimizer.py estimate-cost query.sql --warehouse snowflake

  # Generate template files
  python etl_performance_optimizer.py template data_stats --output stats.json
        """
    )

    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')

    subparsers = parser.add_subparsers(dest='command', help='Command to run')

    # Analyze SQL command
    sql_parser = subparsers.add_parser('analyze-sql', help='Analyze SQL query')
    sql_parser.add_argument('input', help='SQL file or inline query')
    sql_parser.add_argument('--warehouse', '-w', choices=['bigquery', 'snowflake', 'redshift', 'databricks'],
                          help='Warehouse for cost estimation')
    sql_parser.add_argument('--stats', '-s', help='Data statistics JSON file')
    sql_parser.add_argument('--output', '-o', help='Output file')
    sql_parser.add_argument('--json', action='store_true', help='Output as JSON')
    sql_parser.set_defaults(func=cmd_analyze_sql)

    # Analyze Spark command
    spark_parser = subparsers.add_parser('analyze-spark', help='Analyze Spark job metrics')
    spark_parser.add_argument('input', help='Spark metrics JSON file')
    spark_parser.add_argument('--output', '-o', help='Output file')
    spark_parser.add_argument('--json', action='store_true', help='Output as JSON')
    spark_parser.set_defaults(func=cmd_analyze_spark)

    # Optimize partition command
    partition_parser = subparsers.add_parser('optimize-partition', help='Recommend partition strategies')
    partition_parser.add_argument('input', help='Data statistics JSON file')
    partition_parser.add_argument('--output', '-o', help='Output file')
    partition_parser.add_argument('--json', action='store_true', help='Output as JSON')
    partition_parser.set_defaults(func=cmd_optimize_partition)

    # Estimate cost command
    cost_parser = subparsers.add_parser('estimate-cost', help='Estimate query cost')
    cost_parser.add_argument('input', help='SQL file or inline query')
    cost_parser.add_argument('--warehouse', '-w', required=True,
                           choices=['bigquery', 'snowflake', 'redshift', 'databricks'],
                           help='Target warehouse')
    cost_parser.add_argument('--stats', '-s', help='Data statistics JSON file')
    cost_parser.add_argument('--output', '-o', help='Output file')
    cost_parser.add_argument('--json', action='store_true', help='Output as JSON')
    cost_parser.set_defaults(func=cmd_estimate_cost)

    # Template command
    template_parser = subparsers.add_parser('template', help='Generate template files')
    template_parser.add_argument('template', choices=['data_stats', 'spark_metrics'],
                                help='Template type')
    template_parser.add_argument('--output', '-o', help='Output file')
    template_parser.set_defaults(func=cmd_generate_template)

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
