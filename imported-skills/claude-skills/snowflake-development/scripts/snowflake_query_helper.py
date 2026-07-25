#!/usr/bin/env python3
"""
Snowflake Query Helper

Generate common Snowflake SQL patterns: MERGE upserts, Dynamic Table DDL,
and RBAC grant statements. Outputs ready-to-use SQL that follows Snowflake
best practices.

Usage:
    python snowflake_query_helper.py merge --target customers --source stg_customers --key id --columns name,email
    python snowflake_query_helper.py dynamic-table --name cleaned_events --warehouse transform_wh --lag "5 minutes"
    python snowflake_query_helper.py grant --role analyst --database analytics --schemas public --privileges SELECT,USAGE
    python snowflake_query_helper.py merge --target t --source s --key id --columns a,b --json
"""

import argparse
import json
import sys
import textwrap
from typing import List, Optional


def generate_merge(
    target: str,
    source: str,
    key: str,
    columns: List[str],
    schema: Optional[str] = None,
) -> str:
    """Generate a MERGE (upsert) statement following Snowflake best practices."""
    prefix = f"{schema}." if schema else ""
    t = f"{prefix}{target}"
    s = f"{prefix}{source}"

    # Filter out updated_at from user columns to avoid duplicates
    merge_cols = [col for col in columns if col != "updated_at"]

    update_sets = ",\n        ".join(
        f"t.{col} = s.{col}" for col in merge_cols
    )
    update_sets += ",\n        t.updated_at = CURRENT_TIMESTAMP()"

    insert_cols = ", ".join([key] + merge_cols + ["updated_at"])
    insert_vals = ", ".join(
        [f"s.{key}"] + [f"s.{col}" for col in merge_cols] + ["CURRENT_TIMESTAMP()"]
    )

    return textwrap.dedent(f"""\
        MERGE INTO {t} t
        USING {s} s
            ON t.{key} = s.{key}
        WHEN MATCHED THEN
            UPDATE SET
                {update_sets}
        WHEN NOT MATCHED THEN
            INSERT ({insert_cols})
            VALUES ({insert_vals});""")


def generate_dynamic_table(
    name: str,
    warehouse: str,
    lag: str,
    source: Optional[str] = None,
    columns: Optional[List[str]] = None,
    schema: Optional[str] = None,
) -> str:
    """Generate a Dynamic Table DDL with best-practice defaults."""
    prefix = f"{schema}." if schema else ""
    full_name = f"{prefix}{name}"
    src = source or "<source_table>"
    col_list = ", ".join(columns) if columns else "<col1>, <col2>, <col3>"

    return textwrap.dedent(f"""\
        CREATE OR REPLACE DYNAMIC TABLE {full_name}
            TARGET_LAG = '{lag}'
            WAREHOUSE = {warehouse}
            AS
            SELECT {col_list}
            FROM {src}
            WHERE 1=1;  -- Add your filter conditions

        -- Verify refresh mode (incremental is preferred):
        -- SELECT name, refresh_mode, refresh_mode_reason
        -- FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLES())
        -- WHERE name = '{name.upper()}';""")


def generate_grants(
    role: str,
    database: str,
    schemas: List[str],
    privileges: List[str],
) -> str:
    """Generate RBAC grant statements following least-privilege principles."""
    lines = [f"-- RBAC grants for role: {role}"]
    lines.append(f"-- Generated following least-privilege principles")
    lines.append("")

    # Database-level
    lines.append(f"GRANT USAGE ON DATABASE {database} TO ROLE {role};")
    lines.append("")

    for schema in schemas:
        fq_schema = f"{database}.{schema}"
        lines.append(f"-- Schema: {fq_schema}")
        lines.append(f"GRANT USAGE ON SCHEMA {fq_schema} TO ROLE {role};")

        for priv in privileges:
            p = priv.strip().upper()
            if p == "USAGE":
                continue  # Already granted above
            elif p == "SELECT":
                lines.append(
                    f"GRANT SELECT ON ALL TABLES IN SCHEMA {fq_schema} TO ROLE {role};"
                )
                lines.append(
                    f"GRANT SELECT ON FUTURE TABLES IN SCHEMA {fq_schema} TO ROLE {role};"
                )
                lines.append(
                    f"GRANT SELECT ON ALL VIEWS IN SCHEMA {fq_schema} TO ROLE {role};"
                )
                lines.append(
                    f"GRANT SELECT ON FUTURE VIEWS IN SCHEMA {fq_schema} TO ROLE {role};"
                )
            elif p in ("INSERT", "UPDATE", "DELETE", "TRUNCATE"):
                lines.append(
                    f"GRANT {p} ON ALL TABLES IN SCHEMA {fq_schema} TO ROLE {role};"
                )
                lines.append(
                    f"GRANT {p} ON FUTURE TABLES IN SCHEMA {fq_schema} TO ROLE {role};"
                )
            elif p == "CREATE TABLE":
                lines.append(
                    f"GRANT CREATE TABLE ON SCHEMA {fq_schema} TO ROLE {role};"
                )
            elif p == "CREATE VIEW":
                lines.append(
                    f"GRANT CREATE VIEW ON SCHEMA {fq_schema} TO ROLE {role};"
                )
            else:
                lines.append(
                    f"GRANT {p} ON SCHEMA {fq_schema} TO ROLE {role};"
                )
        lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate common Snowflake SQL patterns",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
              %(prog)s merge --target customers --source stg --key id --columns name,email
              %(prog)s dynamic-table --name clean_events --warehouse wh --lag "5 min"
              %(prog)s grant --role analyst --database db --schemas public --privileges SELECT
        """),
    )
    parser.add_argument(
        "--json", action="store_true", help="Output as JSON instead of raw SQL"
    )

    subparsers = parser.add_subparsers(dest="command", help="SQL pattern to generate")

    # MERGE subcommand
    merge_p = subparsers.add_parser("merge", help="Generate MERGE (upsert) statement")
    merge_p.add_argument("--target", required=True, help="Target table name")
    merge_p.add_argument("--source", required=True, help="Source table name")
    merge_p.add_argument("--key", required=True, help="Join key column")
    merge_p.add_argument(
        "--columns", required=True, help="Comma-separated columns to merge"
    )
    merge_p.add_argument("--schema", help="Schema prefix (e.g., my_db.my_schema)")

    # Dynamic Table subcommand
    dt_p = subparsers.add_parser(
        "dynamic-table", help="Generate Dynamic Table DDL"
    )
    dt_p.add_argument("--name", required=True, help="Dynamic Table name")
    dt_p.add_argument("--warehouse", required=True, help="Warehouse for refresh")
    dt_p.add_argument(
        "--lag", required=True, help="Target lag (e.g., '5 minutes', '1 hour')"
    )
    dt_p.add_argument("--source", help="Source table name")
    dt_p.add_argument("--columns", help="Comma-separated column list")
    dt_p.add_argument("--schema", help="Schema prefix")

    # Grant subcommand
    grant_p = subparsers.add_parser("grant", help="Generate RBAC grant statements")
    grant_p.add_argument("--role", required=True, help="Role to grant to")
    grant_p.add_argument("--database", required=True, help="Database name")
    grant_p.add_argument(
        "--schemas", required=True, help="Comma-separated schema names"
    )
    grant_p.add_argument(
        "--privileges",
        required=True,
        help="Comma-separated privileges (SELECT, INSERT, UPDATE, DELETE, CREATE TABLE, etc.)",
    )

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        sys.exit(1)

    if args.command == "merge":
        cols = [c.strip() for c in args.columns.split(",")]
        sql = generate_merge(args.target, args.source, args.key, cols, args.schema)
    elif args.command == "dynamic-table":
        cols = [c.strip() for c in args.columns.split(",")] if args.columns else None
        sql = generate_dynamic_table(
            args.name, args.warehouse, args.lag, args.source, cols, args.schema
        )
    elif args.command == "grant":
        schemas = [s.strip() for s in args.schemas.split(",")]
        privs = [p.strip() for p in args.privileges.split(",")]
        sql = generate_grants(args.role, args.database, schemas, privs)
    else:
        parser.print_help()
        sys.exit(1)

    if args.json:
        output = {"command": args.command, "sql": sql}
        print(json.dumps(output, indent=2))
    else:
        print(sql)


if __name__ == "__main__":
    main()
