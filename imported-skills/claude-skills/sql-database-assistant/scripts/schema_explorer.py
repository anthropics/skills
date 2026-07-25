#!/usr/bin/env python3
"""
Schema Explorer

Generates schema documentation from database introspection queries.
Outputs the introspection SQL and sample documentation templates
for PostgreSQL, MySQL, SQLite, and SQL Server.

Since this tool runs without a live database connection, it generates:
1. The introspection queries you need to run
2. Documentation templates from the results
3. Sample schema docs for common table patterns

Usage:
    python schema_explorer.py --dialect postgres --tables all --format md
    python schema_explorer.py --dialect mysql --tables users,orders --format json
    python schema_explorer.py --dialect sqlite --tables all --json
"""

import argparse
import json
import sys
import textwrap
from dataclasses import dataclass, asdict
from typing import List, Optional, Dict


# ---------------------------------------------------------------------------
# Introspection query templates per dialect
# ---------------------------------------------------------------------------

INTROSPECTION_QUERIES: Dict[str, Dict[str, str]] = {
    "postgres": {
        "tables": textwrap.dedent("""\
            SELECT table_name
            FROM information_schema.tables
            WHERE table_schema = 'public' AND table_type = 'BASE TABLE'
            ORDER BY table_name;"""),
        "columns": textwrap.dedent("""\
            SELECT table_name, column_name, data_type, character_maximum_length,
                   is_nullable, column_default
            FROM information_schema.columns
            WHERE table_schema = 'public' {table_filter}
            ORDER BY table_name, ordinal_position;"""),
        "primary_keys": textwrap.dedent("""\
            SELECT tc.table_name, kcu.column_name
            FROM information_schema.table_constraints tc
            JOIN information_schema.key_column_usage kcu
              ON tc.constraint_name = kcu.constraint_name
            WHERE tc.constraint_type = 'PRIMARY KEY' AND tc.table_schema = 'public'
            ORDER BY tc.table_name;"""),
        "foreign_keys": textwrap.dedent("""\
            SELECT tc.table_name, kcu.column_name,
                   ccu.table_name AS foreign_table, ccu.column_name AS foreign_column
            FROM information_schema.table_constraints tc
            JOIN information_schema.key_column_usage kcu
              ON tc.constraint_name = kcu.constraint_name
            JOIN information_schema.constraint_column_usage ccu
              ON tc.constraint_name = ccu.constraint_name
            WHERE tc.constraint_type = 'FOREIGN KEY'
            ORDER BY tc.table_name;"""),
        "indexes": textwrap.dedent("""\
            SELECT schemaname, tablename, indexname, indexdef
            FROM pg_indexes
            WHERE schemaname = 'public'
            ORDER BY tablename, indexname;"""),
        "table_sizes": textwrap.dedent("""\
            SELECT relname AS table_name,
                   pg_size_pretty(pg_total_relation_size(relid)) AS total_size,
                   pg_size_pretty(pg_relation_size(relid)) AS data_size,
                   pg_size_pretty(pg_total_relation_size(relid) - pg_relation_size(relid)) AS index_size
            FROM pg_catalog.pg_statio_user_tables
            ORDER BY pg_total_relation_size(relid) DESC;"""),
    },
    "mysql": {
        "tables": textwrap.dedent("""\
            SELECT table_name
            FROM information_schema.tables
            WHERE table_schema = DATABASE() AND table_type = 'BASE TABLE'
            ORDER BY table_name;"""),
        "columns": textwrap.dedent("""\
            SELECT table_name, column_name, column_type, is_nullable,
                   column_default, column_key, extra
            FROM information_schema.columns
            WHERE table_schema = DATABASE() {table_filter}
            ORDER BY table_name, ordinal_position;"""),
        "foreign_keys": textwrap.dedent("""\
            SELECT table_name, column_name, referenced_table_name, referenced_column_name
            FROM information_schema.key_column_usage
            WHERE table_schema = DATABASE() AND referenced_table_name IS NOT NULL
            ORDER BY table_name;"""),
        "indexes": textwrap.dedent("""\
            SELECT table_name, index_name, non_unique, column_name, seq_in_index
            FROM information_schema.statistics
            WHERE table_schema = DATABASE()
            ORDER BY table_name, index_name, seq_in_index;"""),
        "table_sizes": textwrap.dedent("""\
            SELECT table_name, table_rows,
                   ROUND(data_length / 1024 / 1024, 2) AS data_mb,
                   ROUND(index_length / 1024 / 1024, 2) AS index_mb
            FROM information_schema.tables
            WHERE table_schema = DATABASE()
            ORDER BY data_length DESC;"""),
    },
    "sqlite": {
        "tables": textwrap.dedent("""\
            SELECT name FROM sqlite_master
            WHERE type = 'table' AND name NOT LIKE 'sqlite_%'
            ORDER BY name;"""),
        "columns": textwrap.dedent("""\
            -- Run for each table:
            PRAGMA table_info({table_name});"""),
        "foreign_keys": textwrap.dedent("""\
            -- Run for each table:
            PRAGMA foreign_key_list({table_name});"""),
        "indexes": textwrap.dedent("""\
            SELECT name, tbl_name, sql FROM sqlite_master
            WHERE type = 'index'
            ORDER BY tbl_name, name;"""),
        "schema_dump": textwrap.dedent("""\
            SELECT name, sql FROM sqlite_master
            WHERE type = 'table'
            ORDER BY name;"""),
    },
    "sqlserver": {
        "tables": textwrap.dedent("""\
            SELECT TABLE_NAME
            FROM INFORMATION_SCHEMA.TABLES
            WHERE TABLE_TYPE = 'BASE TABLE'
            ORDER BY TABLE_NAME;"""),
        "columns": textwrap.dedent("""\
            SELECT t.name AS table_name, c.name AS column_name,
                   ty.name AS data_type, c.max_length, c.precision, c.scale,
                   c.is_nullable, dc.definition AS default_value
            FROM sys.columns c
            JOIN sys.tables t ON c.object_id = t.object_id
            JOIN sys.types ty ON c.user_type_id = ty.user_type_id
            LEFT JOIN sys.default_constraints dc ON c.default_object_id = dc.object_id
            {table_filter}
            ORDER BY t.name, c.column_id;"""),
        "foreign_keys": textwrap.dedent("""\
            SELECT fk.name AS fk_name,
                   tp.name AS parent_table, cp.name AS parent_column,
                   tr.name AS referenced_table, cr.name AS referenced_column
            FROM sys.foreign_keys fk
            JOIN sys.foreign_key_columns fkc ON fk.object_id = fkc.constraint_object_id
            JOIN sys.tables tp ON fkc.parent_object_id = tp.object_id
            JOIN sys.columns cp ON fkc.parent_object_id = cp.object_id AND fkc.parent_column_id = cp.column_id
            JOIN sys.tables tr ON fkc.referenced_object_id = tr.object_id
            JOIN sys.columns cr ON fkc.referenced_object_id = cr.object_id AND fkc.referenced_column_id = cr.column_id
            ORDER BY tp.name;"""),
        "indexes": textwrap.dedent("""\
            SELECT t.name AS table_name, i.name AS index_name,
                   i.type_desc, i.is_unique, c.name AS column_name,
                   ic.key_ordinal
            FROM sys.indexes i
            JOIN sys.index_columns ic ON i.object_id = ic.object_id AND i.index_id = ic.index_id
            JOIN sys.columns c ON ic.object_id = c.object_id AND ic.column_id = c.column_id
            JOIN sys.tables t ON i.object_id = t.object_id
            WHERE i.name IS NOT NULL
            ORDER BY t.name, i.name, ic.key_ordinal;"""),
    },
}


# ---------------------------------------------------------------------------
# Documentation generators
# ---------------------------------------------------------------------------

SAMPLE_TABLES = {
    "users": {
        "columns": [
            {"name": "id", "type": "SERIAL / INT", "nullable": "NO", "default": "auto", "notes": "Primary key"},
            {"name": "email", "type": "VARCHAR(255)", "nullable": "NO", "default": "-", "notes": "Unique, indexed"},
            {"name": "name", "type": "VARCHAR(255)", "nullable": "YES", "default": "NULL", "notes": "Display name"},
            {"name": "password_hash", "type": "VARCHAR(255)", "nullable": "NO", "default": "-", "notes": "bcrypt hash"},
            {"name": "created_at", "type": "TIMESTAMP", "nullable": "NO", "default": "NOW()", "notes": ""},
            {"name": "updated_at", "type": "TIMESTAMP", "nullable": "NO", "default": "NOW()", "notes": ""},
        ],
        "indexes": ["PRIMARY KEY (id)", "UNIQUE INDEX (email)"],
        "foreign_keys": [],
    },
    "orders": {
        "columns": [
            {"name": "id", "type": "SERIAL / INT", "nullable": "NO", "default": "auto", "notes": "Primary key"},
            {"name": "user_id", "type": "INTEGER", "nullable": "NO", "default": "-", "notes": "FK -> users.id"},
            {"name": "status", "type": "VARCHAR(50)", "nullable": "NO", "default": "'pending'", "notes": "pending/paid/shipped/cancelled"},
            {"name": "total", "type": "DECIMAL(19,4)", "nullable": "NO", "default": "0", "notes": "Order total in cents"},
            {"name": "created_at", "type": "TIMESTAMP", "nullable": "NO", "default": "NOW()", "notes": ""},
        ],
        "indexes": ["PRIMARY KEY (id)", "INDEX (user_id)", "INDEX (status, created_at)"],
        "foreign_keys": ["user_id -> users.id ON DELETE CASCADE"],
    },
}


def generate_md(dialect: str, tables: List[str]) -> str:
    """Generate markdown schema documentation."""
    lines = [f"# Database Schema Documentation ({dialect.upper()})\n"]
    lines.append(f"Generated by sql-database-assistant schema_explorer.\n")

    # Introspection queries section
    lines.append("## Introspection Queries\n")
    lines.append("Run these queries against your database to extract schema information:\n")
    queries = INTROSPECTION_QUERIES.get(dialect, {})
    for qname, qsql in queries.items():
        table_filter = ""
        if "all" not in tables:
            tlist = ", ".join(f"'{t}'" for t in tables)
            table_filter = f"AND table_name IN ({tlist})"
        qsql = qsql.replace("{table_filter}", table_filter)
        qsql = qsql.replace("{table_name}", tables[0] if tables and tables[0] != "all" else "TABLE_NAME")
        lines.append(f"### {qname.replace('_', ' ').title()}\n")
        lines.append(f"```sql\n{qsql}\n```\n")

    # Sample documentation
    lines.append("## Sample Table Documentation\n")
    lines.append("Below is an example of the documentation format produced from query results:\n")

    show_tables = tables if "all" not in tables else list(SAMPLE_TABLES.keys())
    for tname in show_tables:
        sample = SAMPLE_TABLES.get(tname)
        if not sample:
            lines.append(f"### {tname}\n")
            lines.append("_No sample data available. Run introspection queries above._\n")
            continue

        lines.append(f"### {tname}\n")
        lines.append("| Column | Type | Nullable | Default | Notes |")
        lines.append("|--------|------|----------|---------|-------|")
        for col in sample["columns"]:
            lines.append(f"| {col['name']} | {col['type']} | {col['nullable']} | {col['default']} | {col['notes']} |")
        lines.append("")
        if sample["indexes"]:
            lines.append("**Indexes:** " + ", ".join(sample["indexes"]))
        if sample["foreign_keys"]:
            lines.append("**Foreign Keys:** " + ", ".join(sample["foreign_keys"]))
        lines.append("")

    return "\n".join(lines)


def generate_json_output(dialect: str, tables: List[str]) -> dict:
    """Generate JSON schema documentation."""
    queries = INTROSPECTION_QUERIES.get(dialect, {})
    processed = {}
    for qname, qsql in queries.items():
        table_filter = ""
        if "all" not in tables:
            tlist = ", ".join(f"'{t}'" for t in tables)
            table_filter = f"AND table_name IN ({tlist})"
        processed[qname] = qsql.replace("{table_filter}", table_filter).replace(
            "{table_name}", tables[0] if tables and tables[0] != "all" else "TABLE_NAME"
        )

    show_tables = tables if "all" not in tables else list(SAMPLE_TABLES.keys())
    sample_docs = {}
    for tname in show_tables:
        sample = SAMPLE_TABLES.get(tname)
        if sample:
            sample_docs[tname] = sample

    return {
        "dialect": dialect,
        "requested_tables": tables,
        "introspection_queries": processed,
        "sample_documentation": sample_docs,
        "instructions": "Run the introspection queries against your database, then use the results to populate documentation in the sample format shown.",
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Generate schema documentation from database introspection.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --dialect postgres --tables all --format md
  %(prog)s --dialect mysql --tables users,orders --format json
  %(prog)s --dialect sqlite --tables all --json
        """,
    )
    parser.add_argument(
        "--dialect", required=True, choices=["postgres", "mysql", "sqlite", "sqlserver"],
        help="Target database dialect",
    )
    parser.add_argument(
        "--tables", default="all",
        help="Comma-separated table names or 'all' (default: all)",
    )
    parser.add_argument(
        "--format", choices=["md", "json"], default="md", dest="fmt",
        help="Output format (default: md)",
    )
    parser.add_argument(
        "--json", action="store_true", dest="json_output",
        help="Output as JSON (overrides --format)",
    )
    args = parser.parse_args()

    tables = [t.strip() for t in args.tables.split(",")]

    if args.json_output or args.fmt == "json":
        result = generate_json_output(args.dialect, tables)
        print(json.dumps(result, indent=2))
    else:
        print(generate_md(args.dialect, tables))


if __name__ == "__main__":
    main()
