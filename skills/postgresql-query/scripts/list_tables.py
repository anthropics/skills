#!/usr/bin/env python3
"""
List all tables in a PostgreSQL database.

Usage:
    python list_tables.py --help
    python list_tables.py --database mydb --user myuser
    python list_tables.py --schema public --database mydb --user myuser
"""

import argparse
import os
import sys


def get_connection_params(args):
    """Get connection parameters from args or environment variables."""
    return {
        'host': args.host or os.environ.get('PGHOST', 'localhost'),
        'port': int(args.port or os.environ.get('PGPORT', '5432')),
        'database': args.database or os.environ.get('PGDATABASE'),
        'user': args.user or os.environ.get('PGUSER'),
        'password': args.password or os.environ.get('PGPASSWORD'),
    }


def list_tables(conn_params, schema=None, include_columns=False):
    """List tables in the database."""
    try:
        import psycopg2
    except ImportError:
        return {
            'error': 'psycopg2 not installed. Run: pip install psycopg2-binary',
            'status': 'error'
        }

    if not conn_params.get('database'):
        return {'error': 'Database name is required', 'status': 'error'}
    if not conn_params.get('user'):
        return {'error': 'Username is required', 'status': 'error'}

    conn = None
    try:
        conn = psycopg2.connect(
            host=conn_params['host'],
            port=conn_params['port'],
            database=conn_params['database'],
            user=conn_params['user'],
            password=conn_params['password'],
            connect_timeout=10
        )
        
        tables = []
        with conn.cursor() as cur:
            if schema:
                cur.execute("""
                    SELECT table_schema, table_name, table_type
                    FROM information_schema.tables
                    WHERE table_schema = %s
                    ORDER BY table_schema, table_name
                """, (schema,))
            else:
                cur.execute("""
                    SELECT table_schema, table_name, table_type
                    FROM information_schema.tables
                    WHERE table_schema NOT IN ('pg_catalog', 'information_schema')
                    ORDER BY table_schema, table_name
                """)
            
            for row in cur.fetchall():
                table_info = {
                    'schema': row[0],
                    'name': row[1],
                    'type': row[2]
                }
                
                if include_columns:
                    cur.execute("""
                        SELECT column_name, data_type, is_nullable, column_default
                        FROM information_schema.columns
                        WHERE table_schema = %s AND table_name = %s
                        ORDER BY ordinal_position
                    """, (row[0], row[1]))
                    
                    table_info['columns'] = [
                        {
                            'name': col[0],
                            'type': col[1],
                            'nullable': col[2] == 'YES',
                            'default': col[3]
                        }
                        for col in cur.fetchall()
                    ]
                
                tables.append(table_info)
        
        return {
            'status': 'success',
            'database': conn_params['database'],
            'table_count': len(tables),
            'tables': tables
        }
                
    except psycopg2.OperationalError as e:
        return {'error': f'Connection failed: {e}', 'status': 'error'}
    except psycopg2.Error as e:
        return {'error': f'Database error: {e}', 'status': 'error'}
    finally:
        if conn:
            conn.close()


def format_output(result, verbose=False):
    """Format the result for display."""
    if result.get('status') == 'error':
        return f"Error: {result.get('error')}"
    
    database = result.get('database', 'unknown')
    table_count = result.get('table_count', 0)
    tables = result.get('tables', [])
    
    lines = [
        f"Database: {database}",
        f"Tables found: {table_count}",
        ""
    ]
    
    current_schema = None
    for table in tables:
        if table['schema'] != current_schema:
            current_schema = table['schema']
            lines.append(f"Schema: {current_schema}")
            lines.append("-" * 40)
        
        table_type = "VIEW" if table['type'] == 'VIEW' else "TABLE"
        lines.append(f"  {table['name']} ({table_type})")
        
        if verbose and 'columns' in table:
            for col in table['columns']:
                nullable = "NULL" if col['nullable'] else "NOT NULL"
                default = f" DEFAULT {col['default']}" if col['default'] else ""
                lines.append(f"    - {col['name']}: {col['type']} {nullable}{default}")
            lines.append("")
    
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(
        description='List tables in a PostgreSQL database.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Environment variables:
  PGHOST      Database host (default: localhost)
  PGPORT      Database port (default: 5432)
  PGDATABASE  Database name
  PGUSER      Username
  PGPASSWORD  Password

Examples:
  %(prog)s --database mydb --user admin
  %(prog)s --schema public --verbose
  %(prog)s --host db.example.com --database mydb --user admin
"""
    )
    parser.add_argument('--host', '-H', help='Database host (or PGHOST env var)')
    parser.add_argument('--port', '-p', help='Database port (or PGPORT env var)')
    parser.add_argument('--database', '-d', help='Database name (or PGDATABASE env var)')
    parser.add_argument('--user', '-U', help='Username (or PGUSER env var)')
    parser.add_argument('--password', '-W', help='Password (or PGPASSWORD env var)')
    parser.add_argument('--schema', '-s', help='Filter by schema name')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Include column details for each table')
    
    args = parser.parse_args()
    
    conn_params = get_connection_params(args)
    result = list_tables(conn_params, args.schema, args.verbose)
    
    if result.get('status') == 'error':
        print(f"Error: {result.get('error')}", file=sys.stderr)
        sys.exit(1)
    
    print(format_output(result, args.verbose))


if __name__ == '__main__':
    main()
