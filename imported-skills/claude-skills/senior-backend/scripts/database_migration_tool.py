#!/usr/bin/env python3
"""
Database Migration Tool

Analyzes SQL schema files, detects potential issues, suggests indexes,
and generates migration scripts with rollback support.

Usage:
    python database_migration_tool.py schema.sql --analyze
    python database_migration_tool.py old.sql --compare new.sql --output migrations/
    python database_migration_tool.py schema.sql --suggest-indexes
"""

import os
import sys
import json
import argparse
import re
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from datetime import datetime
from dataclasses import dataclass, field, asdict


@dataclass
class Column:
    """Database column definition."""
    name: str
    data_type: str
    nullable: bool = True
    default: Optional[str] = None
    primary_key: bool = False
    unique: bool = False
    references: Optional[str] = None


@dataclass
class Index:
    """Database index definition."""
    name: str
    table: str
    columns: List[str]
    unique: bool = False
    partial: Optional[str] = None


@dataclass
class Table:
    """Database table definition."""
    name: str
    columns: Dict[str, Column] = field(default_factory=dict)
    indexes: List[Index] = field(default_factory=list)
    primary_key: List[str] = field(default_factory=list)
    foreign_keys: List[Dict] = field(default_factory=list)


@dataclass
class Issue:
    """Schema issue or recommendation."""
    severity: str  # 'error', 'warning', 'info'
    category: str  # 'index', 'naming', 'type', 'constraint'
    table: str
    message: str
    suggestion: Optional[str] = None


class SQLParser:
    """Parse SQL DDL statements."""

    # Common patterns
    CREATE_TABLE_PATTERN = re.compile(
        r'CREATE\s+TABLE\s+(?:IF\s+NOT\s+EXISTS\s+)?["`]?(\w+)["`]?\s*\((.*?)\)\s*;',
        re.IGNORECASE | re.DOTALL
    )

    CREATE_INDEX_PATTERN = re.compile(
        r'CREATE\s+(UNIQUE\s+)?INDEX\s+(?:IF\s+NOT\s+EXISTS\s+)?["`]?(\w+)["`]?\s+'
        r'ON\s+["`]?(\w+)["`]?\s*\(([^)]+)\)(?:\s+WHERE\s+(.+?))?;',
        re.IGNORECASE | re.DOTALL
    )

    COLUMN_PATTERN = re.compile(
        r'["`]?(\w+)["`]?\s+'  # Column name
        r'(\w+(?:\s*\([^)]+\))?)'  # Data type
        r'([^,]*)',  # Constraints
        re.IGNORECASE
    )

    FK_PATTERN = re.compile(
        r'FOREIGN\s+KEY\s*\(["`]?(\w+)["`]?\)\s+'
        r'REFERENCES\s+["`]?(\w+)["`]?\s*\(["`]?(\w+)["`]?\)',
        re.IGNORECASE
    )

    def parse(self, sql: str) -> Dict[str, Table]:
        """Parse SQL and return table definitions."""
        tables = {}

        # Parse CREATE TABLE statements
        for match in self.CREATE_TABLE_PATTERN.finditer(sql):
            table_name = match.group(1)
            body = match.group(2)
            table = self._parse_table_body(table_name, body)
            tables[table_name] = table

        # Parse CREATE INDEX statements
        for match in self.CREATE_INDEX_PATTERN.finditer(sql):
            unique = bool(match.group(1))
            index_name = match.group(2)
            table_name = match.group(3)
            columns = [c.strip().strip('"`') for c in match.group(4).split(',')]
            where_clause = match.group(5)

            index = Index(
                name=index_name,
                table=table_name,
                columns=columns,
                unique=unique,
                partial=where_clause.strip() if where_clause else None
            )

            if table_name in tables:
                tables[table_name].indexes.append(index)

        return tables

    def _parse_table_body(self, table_name: str, body: str) -> Table:
        """Parse table body (columns, constraints)."""
        table = Table(name=table_name)

        # Split by comma, but respect parentheses
        parts = self._split_by_comma(body)

        for part in parts:
            part = part.strip()

            # Skip empty parts
            if not part:
                continue

            # Check for PRIMARY KEY constraint
            if part.upper().startswith('PRIMARY KEY'):
                pk_match = re.search(r'PRIMARY\s+KEY\s*\(([^)]+)\)', part, re.IGNORECASE)
                if pk_match:
                    cols = [c.strip().strip('"`') for c in pk_match.group(1).split(',')]
                    table.primary_key = cols

            # Check for FOREIGN KEY constraint
            elif part.upper().startswith('FOREIGN KEY'):
                fk_match = self.FK_PATTERN.search(part)
                if fk_match:
                    table.foreign_keys.append({
                        'column': fk_match.group(1),
                        'ref_table': fk_match.group(2),
                        'ref_column': fk_match.group(3),
                    })

            # Check for CONSTRAINT
            elif part.upper().startswith('CONSTRAINT'):
                # Handle named constraints
                if 'PRIMARY KEY' in part.upper():
                    pk_match = re.search(r'PRIMARY\s+KEY\s*\(([^)]+)\)', part, re.IGNORECASE)
                    if pk_match:
                        cols = [c.strip().strip('"`') for c in pk_match.group(1).split(',')]
                        table.primary_key = cols
                elif 'FOREIGN KEY' in part.upper():
                    fk_match = self.FK_PATTERN.search(part)
                    if fk_match:
                        table.foreign_keys.append({
                            'column': fk_match.group(1),
                            'ref_table': fk_match.group(2),
                            'ref_column': fk_match.group(3),
                        })

            # Regular column definition
            else:
                col_match = self.COLUMN_PATTERN.match(part)
                if col_match:
                    col_name = col_match.group(1)
                    col_type = col_match.group(2)
                    constraints = col_match.group(3).upper() if col_match.group(3) else ''

                    column = Column(
                        name=col_name,
                        data_type=col_type.upper(),
                        nullable='NOT NULL' not in constraints,
                        primary_key='PRIMARY KEY' in constraints,
                        unique='UNIQUE' in constraints,
                    )

                    # Extract default value
                    default_match = re.search(r'DEFAULT\s+(\S+)', constraints, re.IGNORECASE)
                    if default_match:
                        column.default = default_match.group(1)

                    # Extract references
                    ref_match = re.search(
                        r'REFERENCES\s+["`]?(\w+)["`]?\s*\(["`]?(\w+)["`]?\)',
                        constraints,
                        re.IGNORECASE
                    )
                    if ref_match:
                        column.references = f"{ref_match.group(1)}({ref_match.group(2)})"
                        table.foreign_keys.append({
                            'column': col_name,
                            'ref_table': ref_match.group(1),
                            'ref_column': ref_match.group(2),
                        })

                    if column.primary_key and col_name not in table.primary_key:
                        table.primary_key.append(col_name)

                    table.columns[col_name] = column

        return table

    def _split_by_comma(self, s: str) -> List[str]:
        """Split string by comma, respecting parentheses."""
        parts = []
        current = []
        depth = 0

        for char in s:
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            elif char == ',' and depth == 0:
                parts.append(''.join(current))
                current = []
                continue
            current.append(char)

        if current:
            parts.append(''.join(current))

        return parts


class SchemaAnalyzer:
    """Analyze database schema for issues and optimizations."""

    # Columns that typically need indexes (foreign keys)
    FK_COLUMN_PATTERNS = ['_id', 'Id', '_ID']

    # Columns that typically need indexes for filtering
    FILTER_COLUMN_PATTERNS = ['status', 'state', 'type', 'category', 'active', 'enabled', 'deleted']

    # Columns that typically need indexes for sorting/ordering
    SORT_COLUMN_PATTERNS = ['created_at', 'updated_at', 'date', 'timestamp', 'order', 'position']

    def __init__(self, tables: Dict[str, Table]):
        self.tables = tables
        self.issues: List[Issue] = []

    def analyze(self) -> List[Issue]:
        """Run all analysis checks."""
        self.issues = []

        for table_name, table in self.tables.items():
            self._check_naming_conventions(table)
            self._check_primary_key(table)
            self._check_foreign_key_indexes(table)
            self._check_common_filter_columns(table)
            self._check_timestamp_columns(table)
            self._check_data_types(table)

        return self.issues

    def _check_naming_conventions(self, table: Table):
        """Check table and column naming conventions."""
        # Table name should be lowercase
        if table.name != table.name.lower():
            self.issues.append(Issue(
                severity='warning',
                category='naming',
                table=table.name,
                message=f"Table name '{table.name}' should be lowercase",
                suggestion=f"Rename to '{table.name.lower()}'"
            ))

        # Table name should be plural (basic check)
        if not table.name.endswith('s') and not table.name.endswith('es'):
            self.issues.append(Issue(
                severity='info',
                category='naming',
                table=table.name,
                message=f"Table name '{table.name}' should typically be plural",
            ))

        for col_name, col in table.columns.items():
            # Column names should be lowercase with underscores
            if col_name != col_name.lower():
                self.issues.append(Issue(
                    severity='warning',
                    category='naming',
                    table=table.name,
                    message=f"Column '{col_name}' should use snake_case",
                    suggestion=f"Rename to '{self._to_snake_case(col_name)}'"
                ))

    def _check_primary_key(self, table: Table):
        """Check for missing primary key."""
        if not table.primary_key:
            self.issues.append(Issue(
                severity='error',
                category='constraint',
                table=table.name,
                message=f"Table '{table.name}' has no primary key",
                suggestion="Add a primary key column (e.g., 'id SERIAL PRIMARY KEY')"
            ))

    def _check_foreign_key_indexes(self, table: Table):
        """Check that foreign key columns have indexes."""
        indexed_columns = set()
        for index in table.indexes:
            indexed_columns.update(index.columns)

        # Primary key columns are implicitly indexed
        indexed_columns.update(table.primary_key)

        for fk in table.foreign_keys:
            fk_col = fk['column']
            if fk_col not in indexed_columns:
                self.issues.append(Issue(
                    severity='warning',
                    category='index',
                    table=table.name,
                    message=f"Foreign key column '{fk_col}' is not indexed",
                    suggestion=f"CREATE INDEX idx_{table.name}_{fk_col} ON {table.name}({fk_col});"
                ))

        # Also check columns that look like foreign keys but aren't declared
        for col_name in table.columns:
            if any(col_name.endswith(pattern) for pattern in self.FK_COLUMN_PATTERNS):
                if col_name not in indexed_columns:
                    # Check if it's actually a declared FK
                    is_declared_fk = any(fk['column'] == col_name for fk in table.foreign_keys)
                    if not is_declared_fk:
                        self.issues.append(Issue(
                            severity='info',
                            category='index',
                            table=table.name,
                            message=f"Column '{col_name}' looks like a foreign key but has no index",
                            suggestion=f"CREATE INDEX idx_{table.name}_{col_name} ON {table.name}({col_name});"
                        ))

    def _check_common_filter_columns(self, table: Table):
        """Check for indexes on commonly filtered columns."""
        indexed_columns = set()
        for index in table.indexes:
            indexed_columns.update(index.columns)
        indexed_columns.update(table.primary_key)

        for col_name in table.columns:
            col_lower = col_name.lower()
            if any(pattern in col_lower for pattern in self.FILTER_COLUMN_PATTERNS):
                if col_name not in indexed_columns:
                    self.issues.append(Issue(
                        severity='info',
                        category='index',
                        table=table.name,
                        message=f"Column '{col_name}' is commonly used for filtering but has no index",
                        suggestion=f"CREATE INDEX idx_{table.name}_{col_name} ON {table.name}({col_name});"
                    ))

    def _check_timestamp_columns(self, table: Table):
        """Check for indexes on timestamp columns used for sorting."""
        has_created_at = 'created_at' in table.columns
        has_updated_at = 'updated_at' in table.columns

        if not has_created_at:
            self.issues.append(Issue(
                severity='info',
                category='convention',
                table=table.name,
                message=f"Table '{table.name}' has no 'created_at' column",
                suggestion="Consider adding: created_at TIMESTAMP DEFAULT NOW()"
            ))

        if not has_updated_at:
            self.issues.append(Issue(
                severity='info',
                category='convention',
                table=table.name,
                message=f"Table '{table.name}' has no 'updated_at' column",
                suggestion="Consider adding: updated_at TIMESTAMP DEFAULT NOW()"
            ))

    def _check_data_types(self, table: Table):
        """Check for potential data type issues."""
        for col_name, col in table.columns.items():
            dtype = col.data_type.upper()

            # Check for VARCHAR without length
            if 'VARCHAR' in dtype and '(' not in dtype:
                self.issues.append(Issue(
                    severity='warning',
                    category='type',
                    table=table.name,
                    message=f"Column '{col_name}' uses VARCHAR without length",
                    suggestion="Specify a maximum length, e.g., VARCHAR(255)"
                ))

            # Check for FLOAT/DOUBLE for monetary values
            if 'FLOAT' in dtype or 'DOUBLE' in dtype:
                if 'price' in col_name.lower() or 'amount' in col_name.lower() or 'total' in col_name.lower():
                    self.issues.append(Issue(
                        severity='warning',
                        category='type',
                        table=table.name,
                        message=f"Column '{col_name}' uses floating point for monetary value",
                        suggestion="Use DECIMAL or NUMERIC for monetary values"
                    ))

            # Check for TEXT columns that might benefit from length limits
            if dtype == 'TEXT':
                if 'email' in col_name.lower() or 'url' in col_name.lower():
                    self.issues.append(Issue(
                        severity='info',
                        category='type',
                        table=table.name,
                        message=f"Column '{col_name}' uses TEXT but might benefit from VARCHAR",
                        suggestion=f"Consider VARCHAR(255) for {col_name}"
                    ))

    def _to_snake_case(self, name: str) -> str:
        """Convert name to snake_case."""
        s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
        return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()


class MigrationGenerator:
    """Generate migration scripts from schema differences."""

    def __init__(self, old_tables: Dict[str, Table], new_tables: Dict[str, Table]):
        self.old_tables = old_tables
        self.new_tables = new_tables

    def generate(self) -> Tuple[str, str]:
        """Generate UP and DOWN migration scripts."""
        up_statements = []
        down_statements = []

        # Find new tables
        for table_name, table in self.new_tables.items():
            if table_name not in self.old_tables:
                up_statements.append(self._generate_create_table(table))
                down_statements.append(f"DROP TABLE IF EXISTS {table_name};")

        # Find removed tables
        for table_name, table in self.old_tables.items():
            if table_name not in self.new_tables:
                up_statements.append(f"DROP TABLE IF EXISTS {table_name};")
                down_statements.append(self._generate_create_table(table))

        # Find modified tables
        for table_name in set(self.old_tables.keys()) & set(self.new_tables.keys()):
            old_table = self.old_tables[table_name]
            new_table = self.new_tables[table_name]
            up, down = self._compare_tables(old_table, new_table)
            up_statements.extend(up)
            down_statements.extend(down)

        up_sql = '\n\n'.join(up_statements) if up_statements else '-- No changes'
        down_sql = '\n\n'.join(down_statements) if down_statements else '-- No changes'

        return up_sql, down_sql

    def _generate_create_table(self, table: Table) -> str:
        """Generate CREATE TABLE statement."""
        lines = [f"CREATE TABLE {table.name} ("]

        col_defs = []
        for col_name, col in table.columns.items():
            col_def = f"  {col_name} {col.data_type}"
            if not col.nullable:
                col_def += " NOT NULL"
            if col.default:
                col_def += f" DEFAULT {col.default}"
            if col.primary_key and len(table.primary_key) == 1:
                col_def += " PRIMARY KEY"
            if col.unique:
                col_def += " UNIQUE"
            col_defs.append(col_def)

        # Add composite primary key
        if len(table.primary_key) > 1:
            pk_cols = ', '.join(table.primary_key)
            col_defs.append(f"  PRIMARY KEY ({pk_cols})")

        # Add foreign keys
        for fk in table.foreign_keys:
            col_defs.append(
                f"  FOREIGN KEY ({fk['column']}) REFERENCES {fk['ref_table']}({fk['ref_column']})"
            )

        lines.append(',\n'.join(col_defs))
        lines.append(");")

        return '\n'.join(lines)

    def _compare_tables(self, old: Table, new: Table) -> Tuple[List[str], List[str]]:
        """Compare two tables and generate ALTER statements."""
        up = []
        down = []

        # New columns
        for col_name, col in new.columns.items():
            if col_name not in old.columns:
                up.append(f"ALTER TABLE {new.name} ADD COLUMN {col_name} {col.data_type}"
                         + (" NOT NULL" if not col.nullable else "")
                         + (f" DEFAULT {col.default}" if col.default else "") + ";")
                down.append(f"ALTER TABLE {new.name} DROP COLUMN IF EXISTS {col_name};")

        # Removed columns
        for col_name, col in old.columns.items():
            if col_name not in new.columns:
                up.append(f"ALTER TABLE {old.name} DROP COLUMN IF EXISTS {col_name};")
                down.append(f"ALTER TABLE {old.name} ADD COLUMN {col_name} {col.data_type}"
                           + (" NOT NULL" if not col.nullable else "")
                           + (f" DEFAULT {col.default}" if col.default else "") + ";")

        # Modified columns (type changes)
        for col_name in set(old.columns.keys()) & set(new.columns.keys()):
            old_col = old.columns[col_name]
            new_col = new.columns[col_name]

            if old_col.data_type != new_col.data_type:
                up.append(f"ALTER TABLE {new.name} ALTER COLUMN {col_name} TYPE {new_col.data_type};")
                down.append(f"ALTER TABLE {old.name} ALTER COLUMN {col_name} TYPE {old_col.data_type};")

        # New indexes
        old_index_names = {idx.name for idx in old.indexes}
        for idx in new.indexes:
            if idx.name not in old_index_names:
                unique = "UNIQUE " if idx.unique else ""
                cols = ', '.join(idx.columns)
                where = f" WHERE {idx.partial}" if idx.partial else ""
                up.append(f"CREATE {unique}INDEX CONCURRENTLY {idx.name} ON {idx.table}({cols}){where};")
                down.append(f"DROP INDEX IF EXISTS {idx.name};")

        # Removed indexes
        new_index_names = {idx.name for idx in new.indexes}
        for idx in old.indexes:
            if idx.name not in new_index_names:
                unique = "UNIQUE " if idx.unique else ""
                cols = ', '.join(idx.columns)
                where = f" WHERE {idx.partial}" if idx.partial else ""
                up.append(f"DROP INDEX IF EXISTS {idx.name};")
                down.append(f"CREATE {unique}INDEX {idx.name} ON {idx.table}({cols}){where};")

        return up, down


class DatabaseMigrationTool:
    """Main tool for database migration analysis."""

    def __init__(self, schema_path: str, compare_path: Optional[str] = None,
                 output_dir: Optional[str] = None, verbose: bool = False):
        self.schema_path = Path(schema_path)
        self.compare_path = Path(compare_path) if compare_path else None
        self.output_dir = Path(output_dir) if output_dir else None
        self.verbose = verbose
        self.parser = SQLParser()

    def run(self, mode: str = 'analyze') -> Dict:
        """Execute the tool in specified mode."""
        print(f"Database Migration Tool")
        print(f"Schema: {self.schema_path}")
        print("-" * 50)

        if not self.schema_path.exists():
            raise FileNotFoundError(f"Schema file not found: {self.schema_path}")

        schema_sql = self.schema_path.read_text()
        tables = self.parser.parse(schema_sql)

        if self.verbose:
            print(f"Parsed {len(tables)} tables")

        if mode == 'analyze':
            return self._analyze(tables)
        elif mode == 'compare':
            return self._compare(tables)
        elif mode == 'suggest-indexes':
            return self._suggest_indexes(tables)
        else:
            raise ValueError(f"Unknown mode: {mode}")

    def _analyze(self, tables: Dict[str, Table]) -> Dict:
        """Analyze schema for issues."""
        analyzer = SchemaAnalyzer(tables)
        issues = analyzer.analyze()

        # Group by severity
        errors = [i for i in issues if i.severity == 'error']
        warnings = [i for i in issues if i.severity == 'warning']
        infos = [i for i in issues if i.severity == 'info']

        print(f"\nAnalysis Results:")
        print(f"  Tables: {len(tables)}")
        print(f"  Errors: {len(errors)}")
        print(f"  Warnings: {len(warnings)}")
        print(f"  Suggestions: {len(infos)}")

        if errors:
            print(f"\nERRORS:")
            for issue in errors:
                print(f"  [{issue.table}] {issue.message}")
                if issue.suggestion:
                    print(f"    Suggestion: {issue.suggestion}")

        if warnings:
            print(f"\nWARNINGS:")
            for issue in warnings:
                print(f"  [{issue.table}] {issue.message}")
                if issue.suggestion:
                    print(f"    Suggestion: {issue.suggestion}")

        if self.verbose and infos:
            print(f"\nSUGGESTIONS:")
            for issue in infos:
                print(f"  [{issue.table}] {issue.message}")
                if issue.suggestion:
                    print(f"    {issue.suggestion}")

        return {
            'status': 'success',
            'tables_count': len(tables),
            'issues': {
                'errors': len(errors),
                'warnings': len(warnings),
                'suggestions': len(infos),
            },
            'issues_detail': [asdict(i) for i in issues],
        }

    def _compare(self, old_tables: Dict[str, Table]) -> Dict:
        """Compare two schemas and generate migration."""
        if not self.compare_path:
            raise ValueError("Compare path required for compare mode")

        if not self.compare_path.exists():
            raise FileNotFoundError(f"Compare file not found: {self.compare_path}")

        new_sql = self.compare_path.read_text()
        new_tables = self.parser.parse(new_sql)

        generator = MigrationGenerator(old_tables, new_tables)
        up_sql, down_sql = generator.generate()

        print(f"\nComparing schemas:")
        print(f"  Old: {self.schema_path}")
        print(f"  New: {self.compare_path}")

        # Calculate changes
        added_tables = set(new_tables.keys()) - set(old_tables.keys())
        removed_tables = set(old_tables.keys()) - set(new_tables.keys())

        print(f"\nChanges detected:")
        print(f"  Added tables: {len(added_tables)}")
        print(f"  Removed tables: {len(removed_tables)}")

        if self.output_dir:
            self.output_dir.mkdir(parents=True, exist_ok=True)
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')

            up_file = self.output_dir / f"{timestamp}_migration.sql"
            down_file = self.output_dir / f"{timestamp}_migration_rollback.sql"

            up_file.write_text(f"-- Migration: {self.schema_path} -> {self.compare_path}\n"
                              f"-- Generated: {datetime.now().isoformat()}\n\n"
                              f"BEGIN;\n\n{up_sql}\n\nCOMMIT;\n")

            down_file.write_text(f"-- Rollback for migration {timestamp}\n"
                                f"-- Generated: {datetime.now().isoformat()}\n\n"
                                f"BEGIN;\n\n{down_sql}\n\nCOMMIT;\n")

            print(f"\nGenerated files:")
            print(f"  Migration: {up_file}")
            print(f"  Rollback: {down_file}")
        else:
            print(f"\n--- UP MIGRATION ---")
            print(up_sql)
            print(f"\n--- DOWN MIGRATION ---")
            print(down_sql)

        return {
            'status': 'success',
            'added_tables': list(added_tables),
            'removed_tables': list(removed_tables),
            'up_sql': up_sql,
            'down_sql': down_sql,
        }

    def _suggest_indexes(self, tables: Dict[str, Table]) -> Dict:
        """Generate index suggestions."""
        suggestions = []

        for table_name, table in tables.items():
            # Get existing indexed columns
            indexed = set()
            for idx in table.indexes:
                indexed.update(idx.columns)
            indexed.update(table.primary_key)

            # Suggest indexes for foreign keys
            for fk in table.foreign_keys:
                if fk['column'] not in indexed:
                    suggestions.append({
                        'table': table_name,
                        'column': fk['column'],
                        'reason': 'Foreign key',
                        'sql': f"CREATE INDEX idx_{table_name}_{fk['column']} ON {table_name}({fk['column']});"
                    })

            # Suggest indexes for common patterns
            for col_name in table.columns:
                if col_name in indexed:
                    continue

                col_lower = col_name.lower()

                # Foreign key pattern
                if col_name.endswith('_id') and col_name not in indexed:
                    suggestions.append({
                        'table': table_name,
                        'column': col_name,
                        'reason': 'Likely foreign key',
                        'sql': f"CREATE INDEX idx_{table_name}_{col_name} ON {table_name}({col_name});"
                    })

                # Status/type columns
                elif col_lower in ['status', 'state', 'type', 'category']:
                    suggestions.append({
                        'table': table_name,
                        'column': col_name,
                        'reason': 'Common filter column',
                        'sql': f"CREATE INDEX idx_{table_name}_{col_name} ON {table_name}({col_name});"
                    })

                # Timestamp columns
                elif col_lower in ['created_at', 'updated_at']:
                    suggestions.append({
                        'table': table_name,
                        'column': col_name,
                        'reason': 'Common sort column',
                        'sql': f"CREATE INDEX idx_{table_name}_{col_name} ON {table_name}({col_name} DESC);"
                    })

        print(f"\nIndex Suggestions ({len(suggestions)} found):")
        for s in suggestions:
            print(f"\n  [{s['table']}.{s['column']}] {s['reason']}")
            print(f"    {s['sql']}")

        if self.output_dir:
            self.output_dir.mkdir(parents=True, exist_ok=True)
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            output_file = self.output_dir / f"{timestamp}_add_indexes.sql"

            lines = [
                f"-- Suggested indexes",
                f"-- Generated: {datetime.now().isoformat()}",
                "",
            ]
            for s in suggestions:
                lines.append(f"-- {s['table']}.{s['column']}: {s['reason']}")
                lines.append(s['sql'])
                lines.append("")

            output_file.write_text('\n'.join(lines))
            print(f"\nWritten to: {output_file}")

        return {
            'status': 'success',
            'suggestions_count': len(suggestions),
            'suggestions': suggestions,
        }


def main():
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description='Analyze SQL schemas and generate migrations',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  %(prog)s schema.sql --analyze
  %(prog)s old.sql --compare new.sql --output migrations/
  %(prog)s schema.sql --suggest-indexes --output migrations/
        '''
    )

    parser.add_argument(
        'schema',
        help='Path to SQL schema file'
    )
    parser.add_argument(
        '--analyze',
        action='store_true',
        help='Analyze schema for issues and optimizations'
    )
    parser.add_argument(
        '--compare',
        metavar='FILE',
        help='Compare with another schema file and generate migration'
    )
    parser.add_argument(
        '--suggest-indexes',
        action='store_true',
        help='Generate index suggestions'
    )
    parser.add_argument(
        '--output', '-o',
        help='Output directory for generated files'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output results as JSON'
    )

    args = parser.parse_args()

    # Determine mode
    if args.compare:
        mode = 'compare'
    elif args.suggest_indexes:
        mode = 'suggest-indexes'
    else:
        mode = 'analyze'

    try:
        tool = DatabaseMigrationTool(
            schema_path=args.schema,
            compare_path=args.compare,
            output_dir=args.output,
            verbose=args.verbose,
        )

        results = tool.run(mode=mode)

        if args.json:
            print(json.dumps(results, indent=2))

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
