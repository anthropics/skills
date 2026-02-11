#!/usr/bin/env python3
"""
Execute SQL queries against a PostgreSQL database.

Usage:
    python query_postgres.py --help
    python query_postgres.py --query "SELECT * FROM users LIMIT 10"
    python query_postgres.py --host localhost --port 5432 --database mydb --user myuser --query "SELECT 1"
"""

import argparse
import json
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


def execute_query(conn_params, query, output_format='table', limit=None, read_only=True):
    """Execute a SQL query and return results."""
    try:
        import psycopg2
        from psycopg2 import sql
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
        
        with conn.cursor() as cur:
            if read_only:
                cur.execute("SET TRANSACTION READ ONLY")
            cur.execute(query)
            
            if cur.description is None:
                conn.commit()
                return {
                    'status': 'success',
                    'message': f'Query executed successfully. Rows affected: {cur.rowcount}'
                }
            
            columns = [desc[0] for desc in cur.description]
            
            if limit:
                rows = cur.fetchmany(limit)
            else:
                rows = cur.fetchall()
            
            rows = [list(row) for row in rows]
            
            if output_format == 'json':
                result_data = [dict(zip(columns, row)) for row in rows]
                return {
                    'status': 'success',
                    'columns': columns,
                    'row_count': len(rows),
                    'data': result_data
                }
            else:
                return {
                    'status': 'success',
                    'columns': columns,
                    'row_count': len(rows),
                    'rows': rows
                }
                
    except psycopg2.OperationalError as e:
        return {'error': f'Connection failed: {e}', 'status': 'error'}
    except psycopg2.ProgrammingError as e:
        return {'error': f'Query error: {e}', 'status': 'error'}
    except psycopg2.Error as e:
        return {'error': f'Database error: {e}', 'status': 'error'}
    finally:
        if conn:
            conn.close()


def format_table(columns, rows, max_width=50):
    """Format results as a text table."""
    if not rows:
        return "No rows returned."
    
    def truncate(val, width):
        s = str(val) if val is not None else 'NULL'
        return s[:width-3] + '...' if len(s) > width else s
    
    col_widths = []
    for i, col in enumerate(columns):
        max_val_width = max((len(truncate(row[i], max_width)) for row in rows), default=0)
        col_widths.append(max(len(col), max_val_width))
    
    header = ' | '.join(col.ljust(col_widths[i]) for i, col in enumerate(columns))
    separator = '-+-'.join('-' * w for w in col_widths)
    
    lines = [header, separator]
    for row in rows:
        line = ' | '.join(truncate(row[i], max_width).ljust(col_widths[i]) for i in range(len(columns)))
        lines.append(line)
    
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(
        description='Execute SQL queries against a PostgreSQL database.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Environment variables:
  PGHOST      Database host (default: localhost)
  PGPORT      Database port (default: 5432)
  PGDATABASE  Database name
  PGUSER      Username
  PGPASSWORD  Password

Examples:
  %(prog)s --query "SELECT * FROM users LIMIT 10"
  %(prog)s --host db.example.com --database mydb --user admin --query "SELECT 1"
  %(prog)s --query "SELECT * FROM orders" --format json --limit 100
"""
    )
    parser.add_argument('--host', '-H', help='Database host (or PGHOST env var)')
    parser.add_argument('--port', '-p', help='Database port (or PGPORT env var)')
    parser.add_argument('--database', '-d', help='Database name (or PGDATABASE env var)')
    parser.add_argument('--user', '-U', help='Username (or PGUSER env var)')
    parser.add_argument('--password', '-W', help='Password (or PGPASSWORD env var)')
    parser.add_argument('--query', '-q', required=True, help='SQL query to execute')
    parser.add_argument('--format', '-f', choices=['table', 'json'], default='table',
                        help='Output format (default: table)')
    parser.add_argument('--limit', '-l', type=int, help='Limit number of rows returned')
    parser.add_argument('--allow-write', action='store_true',
                        help='Allow write operations (INSERT, UPDATE, DELETE). Default is read-only.')
    
    args = parser.parse_args()
    
    conn_params = get_connection_params(args)
    result = execute_query(conn_params, args.query, args.format, args.limit, read_only=not args.allow_write)
    
    if result.get('status') == 'error':
        print(f"Error: {result.get('error')}", file=sys.stderr)
        sys.exit(1)
    
    if args.format == 'json':
        print(json.dumps(result, indent=2, default=str))
    else:
        if 'message' in result:
            print(result['message'])
        elif 'rows' in result:
            print(f"Columns: {', '.join(result['columns'])}")
            print(f"Rows: {result['row_count']}")
            print()
            print(format_table(result['columns'], result['rows']))


if __name__ == '__main__':
    main()
