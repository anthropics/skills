#!/usr/bin/env python3
"""
SQL Query Optimizer — Static Analysis

Analyzes SQL queries for common performance issues:
- SELECT * usage
- Missing WHERE clauses on UPDATE/DELETE
- Cartesian joins (missing JOIN conditions)
- Subqueries in SELECT list
- Missing LIMIT on unbounded SELECTs
- Function calls on indexed columns (non-sargable)
- LIKE with leading wildcard
- ORDER BY RAND()
- UNION instead of UNION ALL
- NOT IN with subquery (NULL-unsafe)

Usage:
    python query_optimizer.py --query "SELECT * FROM users"
    python query_optimizer.py --query queries.sql --dialect postgres
    python query_optimizer.py --query "SELECT * FROM orders" --json
"""

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, asdict
from typing import List, Optional


@dataclass
class Issue:
    """A single optimization issue found in a query."""
    severity: str  # critical, warning, info
    rule: str
    message: str
    suggestion: str
    line: Optional[int] = None


@dataclass
class QueryAnalysis:
    """Analysis result for one SQL query."""
    query: str
    issues: List[Issue]
    score: int  # 0-100, higher is better

    def to_dict(self):
        return {
            "query": self.query[:200] + ("..." if len(self.query) > 200 else ""),
            "issues": [asdict(i) for i in self.issues],
            "issue_count": len(self.issues),
            "score": self.score,
        }


# ---------------------------------------------------------------------------
# Rule checkers
# ---------------------------------------------------------------------------

def check_select_star(sql: str) -> Optional[Issue]:
    """Detect SELECT * usage."""
    if re.search(r'\bSELECT\s+\*\s', sql, re.IGNORECASE):
        return Issue(
            severity="warning",
            rule="select-star",
            message="SELECT * transfers unnecessary data and breaks on schema changes.",
            suggestion="List only the columns you need: SELECT col1, col2, ...",
        )
    return None


def check_missing_where(sql: str) -> Optional[Issue]:
    """Detect UPDATE/DELETE without WHERE."""
    upper = sql.upper().strip()
    for keyword in ("UPDATE", "DELETE"):
        if upper.startswith(keyword) and "WHERE" not in upper:
            return Issue(
                severity="critical",
                rule="missing-where",
                message=f"{keyword} without WHERE affects every row in the table.",
                suggestion=f"Add a WHERE clause to restrict the {keyword} scope.",
            )
    return None


def check_cartesian_join(sql: str) -> Optional[Issue]:
    """Detect comma-separated tables without explicit JOIN or WHERE join condition."""
    upper = sql.upper()
    if "SELECT" not in upper:
        return None
    from_match = re.search(r'\bFROM\s+(.+?)(?:\bWHERE\b|\bGROUP\b|\bORDER\b|\bLIMIT\b|\bHAVING\b|;|$)',
                           sql, re.IGNORECASE | re.DOTALL)
    if not from_match:
        return None
    from_clause = from_match.group(1)
    # Skip if explicit JOINs are used
    if re.search(r'\bJOIN\b', from_clause, re.IGNORECASE):
        return None
    # Count comma-separated tables
    tables = [t.strip() for t in from_clause.split(",") if t.strip()]
    if len(tables) > 1 and "WHERE" not in upper:
        return Issue(
            severity="critical",
            rule="cartesian-join",
            message="Multiple tables in FROM without JOIN or WHERE creates a cartesian product.",
            suggestion="Use explicit JOIN syntax with ON conditions.",
        )
    return None


def check_subquery_in_select(sql: str) -> Optional[Issue]:
    """Detect correlated subqueries in SELECT list."""
    select_match = re.search(r'\bSELECT\b(.+?)\bFROM\b', sql, re.IGNORECASE | re.DOTALL)
    if select_match:
        select_clause = select_match.group(1)
        if re.search(r'\(\s*SELECT\b', select_clause, re.IGNORECASE):
            return Issue(
                severity="warning",
                rule="subquery-in-select",
                message="Subquery in SELECT list executes once per row (correlated subquery).",
                suggestion="Rewrite as a LEFT JOIN with aggregation.",
            )
    return None


def check_missing_limit(sql: str) -> Optional[Issue]:
    """Detect unbounded SELECT without LIMIT."""
    upper = sql.upper().strip()
    if not upper.startswith("SELECT"):
        return None
    # Skip if it's a subquery or aggregate-only
    if re.search(r'\bCOUNT\s*\(', upper) and "GROUP BY" not in upper:
        return None
    if "LIMIT" not in upper and "FETCH" not in upper and "TOP " not in upper:
        return Issue(
            severity="info",
            rule="missing-limit",
            message="SELECT without LIMIT may return unbounded rows.",
            suggestion="Add LIMIT to prevent returning excessive data.",
        )
    return None


def check_function_on_column(sql: str) -> Optional[Issue]:
    """Detect function calls on columns in WHERE (non-sargable)."""
    where_match = re.search(r'\bWHERE\b(.+?)(?:\bGROUP\b|\bORDER\b|\bLIMIT\b|\bHAVING\b|;|$)',
                            sql, re.IGNORECASE | re.DOTALL)
    if not where_match:
        return None
    where_clause = where_match.group(1)
    non_sargable = re.search(
        r'\b(YEAR|MONTH|DAY|DATE|UPPER|LOWER|TRIM|CAST|COALESCE|IFNULL|NVL)\s*\(',
        where_clause, re.IGNORECASE
    )
    if non_sargable:
        func = non_sargable.group(1).upper()
        return Issue(
            severity="warning",
            rule="non-sargable",
            message=f"Function {func}() on column in WHERE prevents index usage.",
            suggestion="Rewrite to compare the raw column against transformed constants.",
        )
    return None


def check_leading_wildcard(sql: str) -> Optional[Issue]:
    """Detect LIKE '%...' patterns."""
    if re.search(r"LIKE\s+'%", sql, re.IGNORECASE):
        return Issue(
            severity="warning",
            rule="leading-wildcard",
            message="LIKE with leading wildcard prevents index usage.",
            suggestion="Use full-text search (GIN index, FULLTEXT, FTS5) for substring matching.",
        )
    return None


def check_order_by_rand(sql: str) -> Optional[Issue]:
    """Detect ORDER BY RAND() / RANDOM()."""
    if re.search(r'ORDER\s+BY\s+(RAND|RANDOM)\s*\(\)', sql, re.IGNORECASE):
        return Issue(
            severity="warning",
            rule="order-by-rand",
            message="ORDER BY RAND() scans and sorts the entire table.",
            suggestion="Use application-side random sampling or TABLESAMPLE.",
        )
    return None


def check_union_vs_union_all(sql: str) -> Optional[Issue]:
    """Detect UNION without ALL (unnecessary dedup)."""
    if re.search(r'\bUNION\b(?!\s+ALL\b)', sql, re.IGNORECASE):
        return Issue(
            severity="info",
            rule="union-without-all",
            message="UNION performs deduplication sort; use UNION ALL if duplicates are acceptable.",
            suggestion="Replace UNION with UNION ALL unless you specifically need deduplication.",
        )
    return None


def check_not_in_subquery(sql: str) -> Optional[Issue]:
    """Detect NOT IN (SELECT ...) which is NULL-unsafe."""
    if re.search(r'\bNOT\s+IN\s*\(\s*SELECT\b', sql, re.IGNORECASE):
        return Issue(
            severity="warning",
            rule="not-in-subquery",
            message="NOT IN with subquery returns no rows if any subquery result is NULL.",
            suggestion="Use NOT EXISTS (SELECT 1 ...) instead.",
        )
    return None


ALL_CHECKS = [
    check_select_star,
    check_missing_where,
    check_cartesian_join,
    check_subquery_in_select,
    check_missing_limit,
    check_function_on_column,
    check_leading_wildcard,
    check_order_by_rand,
    check_union_vs_union_all,
    check_not_in_subquery,
]


# ---------------------------------------------------------------------------
# Analysis engine
# ---------------------------------------------------------------------------

def analyze_query(sql: str, dialect: str = "postgres") -> QueryAnalysis:
    """Run all checks against a single SQL query."""
    issues: List[Issue] = []
    for check_fn in ALL_CHECKS:
        issue = check_fn(sql)
        if issue:
            issues.append(issue)

    # Score: start at 100, deduct per severity
    score = 100
    for issue in issues:
        if issue.severity == "critical":
            score -= 25
        elif issue.severity == "warning":
            score -= 10
        else:
            score -= 5
    score = max(0, score)

    return QueryAnalysis(query=sql.strip(), issues=issues, score=score)


def split_queries(text: str) -> List[str]:
    """Split SQL text into individual statements."""
    queries = []
    for stmt in text.split(";"):
        stmt = stmt.strip()
        if stmt and len(stmt) > 5:
            queries.append(stmt + ";")
    return queries


# ---------------------------------------------------------------------------
# Output formatting
# ---------------------------------------------------------------------------

SEVERITY_ICONS = {"critical": "[CRITICAL]", "warning": "[WARNING]", "info": "[INFO]"}


def format_text(analyses: List[QueryAnalysis]) -> str:
    """Format analysis results as human-readable text."""
    lines = []
    for i, analysis in enumerate(analyses, 1):
        lines.append(f"{'='*60}")
        lines.append(f"Query {i} (Score: {analysis.score}/100)")
        lines.append(f"  {analysis.query[:120]}{'...' if len(analysis.query) > 120 else ''}")
        lines.append("")
        if not analysis.issues:
            lines.append("  No issues detected.")
        for issue in analysis.issues:
            icon = SEVERITY_ICONS.get(issue.severity, "")
            lines.append(f"  {icon} {issue.rule}: {issue.message}")
            lines.append(f"    -> {issue.suggestion}")
        lines.append("")
    return "\n".join(lines)


def format_json(analyses: List[QueryAnalysis]) -> str:
    """Format analysis results as JSON."""
    return json.dumps(
        {"analyses": [a.to_dict() for a in analyses], "total_queries": len(analyses)},
        indent=2,
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Analyze SQL queries for common performance issues.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --query "SELECT * FROM users"
  %(prog)s --query queries.sql --dialect mysql
  %(prog)s --query "DELETE FROM orders" --json
        """,
    )
    parser.add_argument(
        "--query", required=True,
        help="SQL query string or path to a .sql file",
    )
    parser.add_argument(
        "--dialect", choices=["postgres", "mysql", "sqlite", "sqlserver"],
        default="postgres", help="SQL dialect (default: postgres)",
    )
    parser.add_argument(
        "--json", action="store_true", dest="json_output",
        help="Output results as JSON",
    )
    args = parser.parse_args()

    # Determine if query is a file path or inline SQL
    sql_text = args.query
    if os.path.isfile(args.query):
        with open(args.query, "r") as f:
            sql_text = f.read()

    queries = split_queries(sql_text)
    if not queries:
        # Treat the whole input as a single query
        queries = [sql_text.strip()]

    analyses = [analyze_query(q, args.dialect) for q in queries]

    if args.json_output:
        print(format_json(analyses))
    else:
        print(format_text(analyses))


if __name__ == "__main__":
    main()
