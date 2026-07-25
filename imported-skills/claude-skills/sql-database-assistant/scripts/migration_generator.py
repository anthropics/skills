#!/usr/bin/env python3
"""
Migration Generator

Generates database migration file templates (up/down) from natural-language
schema change descriptions.

Supported operations:
- Add column, drop column, rename column
- Add table, drop table, rename table
- Add index, drop index
- Add constraint, drop constraint
- Change column type

Usage:
    python migration_generator.py --change "add email_verified boolean to users" --dialect postgres
    python migration_generator.py --change "rename column name to full_name in customers" --format alembic
    python migration_generator.py --change "add index on orders(status, created_at)" --output 001_add_index.sql
    python migration_generator.py --change "create table reviews with id, user_id, rating, body" --json
"""

import argparse
import json
import os
import re
import sys
import textwrap
from dataclasses import dataclass, asdict
from datetime import datetime
from typing import List, Optional, Tuple


@dataclass
class Migration:
    """A generated migration with up and down scripts."""
    description: str
    dialect: str
    format: str
    up: str
    down: str
    warnings: List[str]

    def to_dict(self):
        return asdict(self)


# ---------------------------------------------------------------------------
# Change parsers — extract structured intent from natural language
# ---------------------------------------------------------------------------

def parse_add_column(desc: str) -> Optional[dict]:
    """Parse: add <column> <type> to <table>"""
    m = re.match(
        r'add\s+(?:column\s+)?(\w+)\s+(\w[\w(),.]*)\s+(?:to|on)\s+(\w+)',
        desc, re.IGNORECASE,
    )
    if m:
        return {"op": "add_column", "column": m.group(1), "type": m.group(2), "table": m.group(3)}
    return None


def parse_drop_column(desc: str) -> Optional[dict]:
    """Parse: drop/remove <column> from <table>"""
    m = re.match(
        r'(?:drop|remove)\s+(?:column\s+)?(\w+)\s+from\s+(\w+)',
        desc, re.IGNORECASE,
    )
    if m:
        return {"op": "drop_column", "column": m.group(1), "table": m.group(2)}
    return None


def parse_rename_column(desc: str) -> Optional[dict]:
    """Parse: rename column <old> to <new> in <table>"""
    m = re.match(
        r'rename\s+column\s+(\w+)\s+to\s+(\w+)\s+in\s+(\w+)',
        desc, re.IGNORECASE,
    )
    if m:
        return {"op": "rename_column", "old": m.group(1), "new": m.group(2), "table": m.group(3)}
    return None


def parse_add_table(desc: str) -> Optional[dict]:
    """Parse: create table <name> with <col1>, <col2>, ..."""
    m = re.match(
        r'create\s+table\s+(\w+)\s+with\s+(.+)',
        desc, re.IGNORECASE,
    )
    if m:
        cols = [c.strip() for c in m.group(2).split(",")]
        return {"op": "add_table", "table": m.group(1), "columns": cols}
    return None


def parse_drop_table(desc: str) -> Optional[dict]:
    """Parse: drop table <name>"""
    m = re.match(r'drop\s+table\s+(\w+)', desc, re.IGNORECASE)
    if m:
        return {"op": "drop_table", "table": m.group(1)}
    return None


def parse_add_index(desc: str) -> Optional[dict]:
    """Parse: add index on <table>(<col1>, <col2>)"""
    m = re.match(
        r'add\s+(?:unique\s+)?index\s+(?:on\s+)?(\w+)\s*\(([^)]+)\)',
        desc, re.IGNORECASE,
    )
    if m:
        unique = "unique" in desc.lower()
        cols = [c.strip() for c in m.group(2).split(",")]
        return {"op": "add_index", "table": m.group(1), "columns": cols, "unique": unique}
    return None


def parse_change_type(desc: str) -> Optional[dict]:
    """Parse: change <column> type to <type> in <table>"""
    m = re.match(
        r'change\s+(?:column\s+)?(\w+)\s+type\s+to\s+(\w[\w(),.]*)\s+in\s+(\w+)',
        desc, re.IGNORECASE,
    )
    if m:
        return {"op": "change_type", "column": m.group(1), "new_type": m.group(2), "table": m.group(3)}
    return None


PARSERS = [
    parse_add_column,
    parse_drop_column,
    parse_rename_column,
    parse_add_table,
    parse_drop_table,
    parse_add_index,
    parse_change_type,
]


def parse_change(desc: str) -> Optional[dict]:
    for parser in PARSERS:
        result = parser(desc)
        if result:
            return result
    return None


# ---------------------------------------------------------------------------
# SQL generators per dialect
# ---------------------------------------------------------------------------

TYPE_MAP = {
    "boolean": {"postgres": "BOOLEAN", "mysql": "TINYINT(1)", "sqlite": "INTEGER", "sqlserver": "BIT"},
    "text": {"postgres": "TEXT", "mysql": "TEXT", "sqlite": "TEXT", "sqlserver": "NVARCHAR(MAX)"},
    "integer": {"postgres": "INTEGER", "mysql": "INT", "sqlite": "INTEGER", "sqlserver": "INT"},
    "int": {"postgres": "INTEGER", "mysql": "INT", "sqlite": "INTEGER", "sqlserver": "INT"},
    "serial": {"postgres": "SERIAL", "mysql": "INT AUTO_INCREMENT", "sqlite": "INTEGER", "sqlserver": "INT IDENTITY(1,1)"},
    "varchar": {"postgres": "VARCHAR(255)", "mysql": "VARCHAR(255)", "sqlite": "TEXT", "sqlserver": "NVARCHAR(255)"},
    "timestamp": {"postgres": "TIMESTAMP", "mysql": "DATETIME", "sqlite": "TEXT", "sqlserver": "DATETIME2"},
    "uuid": {"postgres": "UUID", "mysql": "CHAR(36)", "sqlite": "TEXT", "sqlserver": "UNIQUEIDENTIFIER"},
    "json": {"postgres": "JSONB", "mysql": "JSON", "sqlite": "TEXT", "sqlserver": "NVARCHAR(MAX)"},
    "decimal": {"postgres": "DECIMAL(19,4)", "mysql": "DECIMAL(19,4)", "sqlite": "REAL", "sqlserver": "DECIMAL(19,4)"},
    "float": {"postgres": "DOUBLE PRECISION", "mysql": "DOUBLE", "sqlite": "REAL", "sqlserver": "FLOAT"},
}


def map_type(type_name: str, dialect: str) -> str:
    """Map a generic type name to a dialect-specific type."""
    key = type_name.lower().rstrip("()")
    if key in TYPE_MAP and dialect in TYPE_MAP[key]:
        return TYPE_MAP[key][dialect]
    return type_name.upper()


def gen_add_column(change: dict, dialect: str) -> Tuple[str, str, List[str]]:
    col_type = map_type(change["type"], dialect)
    table = change["table"]
    col = change["column"]
    up = f"ALTER TABLE {table} ADD COLUMN {col} {col_type};"
    down = f"ALTER TABLE {table} DROP COLUMN {col};"
    return up, down, []


def gen_drop_column(change: dict, dialect: str) -> Tuple[str, str, List[str]]:
    table = change["table"]
    col = change["column"]
    up = f"ALTER TABLE {table} DROP COLUMN {col};"
    down = f"-- WARNING: Cannot fully reverse DROP COLUMN. Provide the original type.\nALTER TABLE {table} ADD COLUMN {col} TEXT;"
    return up, down, ["Down migration uses TEXT as placeholder. Replace with the original column type."]


def gen_rename_column(change: dict, dialect: str) -> Tuple[str, str, List[str]]:
    table = change["table"]
    old, new = change["old"], change["new"]
    warnings = []
    if dialect == "postgres":
        up = f"ALTER TABLE {table} RENAME COLUMN {old} TO {new};"
        down = f"ALTER TABLE {table} RENAME COLUMN {new} TO {old};"
    elif dialect == "mysql":
        up = f"ALTER TABLE {table} RENAME COLUMN {old} TO {new};"
        down = f"ALTER TABLE {table} RENAME COLUMN {new} TO {old};"
    elif dialect == "sqlite":
        up = f"ALTER TABLE {table} RENAME COLUMN {old} TO {new};"
        down = f"ALTER TABLE {table} RENAME COLUMN {new} TO {old};"
        warnings.append("SQLite RENAME COLUMN requires version 3.25.0+.")
    elif dialect == "sqlserver":
        up = f"EXEC sp_rename '{table}.{old}', '{new}', 'COLUMN';"
        down = f"EXEC sp_rename '{table}.{new}', '{old}', 'COLUMN';"
    else:
        up = f"ALTER TABLE {table} RENAME COLUMN {old} TO {new};"
        down = f"ALTER TABLE {table} RENAME COLUMN {new} TO {old};"
    return up, down, warnings


def gen_add_table(change: dict, dialect: str) -> Tuple[str, str, List[str]]:
    table = change["table"]
    cols = change["columns"]
    col_defs = []
    has_id = False
    for col in cols:
        col = col.strip()
        if col.lower() == "id":
            has_id = True
            if dialect == "postgres":
                col_defs.append("    id SERIAL PRIMARY KEY")
            elif dialect == "mysql":
                col_defs.append("    id INT AUTO_INCREMENT PRIMARY KEY")
            elif dialect == "sqlite":
                col_defs.append("    id INTEGER PRIMARY KEY AUTOINCREMENT")
            elif dialect == "sqlserver":
                col_defs.append("    id INT IDENTITY(1,1) PRIMARY KEY")
        else:
            # Check if type is specified (e.g., "rating int")
            parts = col.split()
            if len(parts) >= 2:
                col_defs.append(f"    {parts[0]} {map_type(parts[1], dialect)}")
            else:
                col_defs.append(f"    {col} TEXT")

    cols_sql = ",\n".join(col_defs)
    up = f"CREATE TABLE {table} (\n{cols_sql}\n);"
    down = f"DROP TABLE {table};"
    warnings = []
    if not has_id:
        warnings.append("Table has no explicit primary key. Consider adding an 'id' column.")
    return up, down, warnings


def gen_drop_table(change: dict, dialect: str) -> Tuple[str, str, List[str]]:
    table = change["table"]
    up = f"DROP TABLE {table};"
    down = f"-- WARNING: Cannot reverse DROP TABLE without original DDL.\nCREATE TABLE {table} (id INTEGER PRIMARY KEY);"
    return up, down, ["Down migration is a placeholder. Replace with the original CREATE TABLE statement."]


def gen_add_index(change: dict, dialect: str) -> Tuple[str, str, List[str]]:
    table = change["table"]
    cols = change["columns"]
    unique = "UNIQUE " if change.get("unique") else ""
    idx_name = f"idx_{table}_{'_'.join(cols)}"
    if dialect == "postgres":
        up = f"CREATE {unique}INDEX CONCURRENTLY {idx_name} ON {table} ({', '.join(cols)});"
    else:
        up = f"CREATE {unique}INDEX {idx_name} ON {table} ({', '.join(cols)});"
    down = f"DROP INDEX {idx_name};" if dialect != "mysql" else f"DROP INDEX {idx_name} ON {table};"
    warnings = []
    if dialect == "postgres":
        warnings.append("CONCURRENTLY cannot run inside a transaction. Run outside migration transaction.")
    return up, down, warnings


def gen_change_type(change: dict, dialect: str) -> Tuple[str, str, List[str]]:
    table = change["table"]
    col = change["column"]
    new_type = map_type(change["new_type"], dialect)
    warnings = ["Down migration uses TEXT as placeholder. Replace with the original column type."]
    if dialect == "postgres":
        up = f"ALTER TABLE {table} ALTER COLUMN {col} TYPE {new_type};"
        down = f"ALTER TABLE {table} ALTER COLUMN {col} TYPE TEXT;"
    elif dialect == "mysql":
        up = f"ALTER TABLE {table} MODIFY COLUMN {col} {new_type};"
        down = f"ALTER TABLE {table} MODIFY COLUMN {col} TEXT;"
    elif dialect == "sqlserver":
        up = f"ALTER TABLE {table} ALTER COLUMN {col} {new_type};"
        down = f"ALTER TABLE {table} ALTER COLUMN {col} NVARCHAR(MAX);"
    else:
        up = f"-- SQLite does not support ALTER COLUMN. Recreate the table."
        down = f"-- SQLite does not support ALTER COLUMN. Recreate the table."
        warnings.append("SQLite requires table recreation for type changes.")
    return up, down, warnings


GENERATORS = {
    "add_column": gen_add_column,
    "drop_column": gen_drop_column,
    "rename_column": gen_rename_column,
    "add_table": gen_add_table,
    "drop_table": gen_drop_table,
    "add_index": gen_add_index,
    "change_type": gen_change_type,
}


# ---------------------------------------------------------------------------
# Format wrappers
# ---------------------------------------------------------------------------

def wrap_sql(up: str, down: str, description: str) -> Tuple[str, str]:
    """Wrap as plain SQL migration files."""
    timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
    header = f"-- Migration: {description}\n-- Generated: {datetime.now().isoformat()}\n\n"
    return header + "-- Up\n" + up, header + "-- Down\n" + down


def wrap_prisma(up: str, down: str, description: str) -> Tuple[str, str]:
    """Format as Prisma migration SQL (Prisma uses raw SQL in migration.sql)."""
    header = f"-- Migration: {description}\n-- Format: Prisma (migration.sql)\n\n"
    return header + up, header + "-- Rollback\n" + down


def wrap_alembic(up: str, down: str, description: str) -> Tuple[str, str]:
    """Format as Alembic Python migration."""
    slug = re.sub(r'\W+', '_', description.lower())[:40]
    revision = datetime.now().strftime("%Y%m%d%H%M")
    template = textwrap.dedent(f'''\
        """
        {description}

        Revision ID: {revision}
        """
        from alembic import op
        import sqlalchemy as sa

        revision = '{revision}'
        down_revision = None  # Set to previous revision


        def upgrade():
            op.execute("""
        {textwrap.indent(up, "        ")}
            """)


        def downgrade():
            op.execute("""
        {textwrap.indent(down, "        ")}
            """)
    ''')
    return template, ""


FORMATTERS = {
    "sql": wrap_sql,
    "prisma": wrap_prisma,
    "alembic": wrap_alembic,
}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Generate database migration templates from change descriptions.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Supported change descriptions:
  "add email_verified boolean to users"
  "drop column legacy_flag from accounts"
  "rename column name to full_name in customers"
  "create table reviews with id, user_id, rating int, body text"
  "drop table temp_imports"
  "add index on orders(status, created_at)"
  "add unique index on users(email)"
  "change email type to varchar in users"

Examples:
  %(prog)s --change "add phone varchar to users" --dialect postgres
  %(prog)s --change "create table reviews with id, user_id, rating int, body" --format prisma
  %(prog)s --change "add index on orders(status)" --output migrations/001.sql --json
        """,
    )
    parser.add_argument("--change", required=True, help="Natural-language description of the schema change")
    parser.add_argument("--dialect", choices=["postgres", "mysql", "sqlite", "sqlserver"],
                        default="postgres", help="Target database dialect (default: postgres)")
    parser.add_argument("--format", choices=["sql", "prisma", "alembic"], default="sql",
                        dest="fmt", help="Output format (default: sql)")
    parser.add_argument("--output", help="Write migration to file instead of stdout")
    parser.add_argument("--json", action="store_true", dest="json_output", help="Output as JSON")
    args = parser.parse_args()

    change = parse_change(args.change)
    if not change:
        print(f"Error: Could not parse change description: '{args.change}'", file=sys.stderr)
        print("Run with --help to see supported patterns.", file=sys.stderr)
        sys.exit(1)

    gen_fn = GENERATORS.get(change["op"])
    if not gen_fn:
        print(f"Error: No generator for operation '{change['op']}'", file=sys.stderr)
        sys.exit(1)

    up, down, warnings = gen_fn(change, args.dialect)

    fmt_fn = FORMATTERS[args.fmt]
    up_formatted, down_formatted = fmt_fn(up, down, args.change)

    migration = Migration(
        description=args.change,
        dialect=args.dialect,
        format=args.fmt,
        up=up_formatted,
        down=down_formatted,
        warnings=warnings,
    )

    if args.json_output:
        print(json.dumps(migration.to_dict(), indent=2))
    else:
        if args.output:
            with open(args.output, "w") as f:
                f.write(migration.up)
            print(f"Migration written to {args.output}")
            if migration.down:
                down_path = args.output.replace(".sql", "_down.sql")
                with open(down_path, "w") as f:
                    f.write(migration.down)
                print(f"Rollback written to {down_path}")
        else:
            print(migration.up)
            if migration.down:
                print("\n" + "=" * 40 + " ROLLBACK " + "=" * 40 + "\n")
                print(migration.down)

        if warnings:
            print("\nWarnings:")
            for w in warnings:
                print(f"  - {w}")


if __name__ == "__main__":
    main()
