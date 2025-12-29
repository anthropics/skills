---
name: postgresql-query
description: "Connect to PostgreSQL databases and execute SQL queries. Use when Claude needs to: (1) Connect to a PostgreSQL database, (2) Execute SELECT queries to retrieve data, (3) List database tables and schemas, (4) Explore database structure, or (5) Run data analysis queries on PostgreSQL"
license: Complete terms in LICENSE.txt
---

# PostgreSQL Database Query Skill

Execute SQL queries against PostgreSQL databases using Python and psycopg2.

## Prerequisites

- PostgreSQL database accessible from the environment
- Database credentials (host, port, database name, username, password)
- Python psycopg2 library (install with `pip install psycopg2-binary`)

## Connection Configuration

Database connections require these parameters:
- `host`: Database server hostname or IP address
- `port`: Database port (default: 5432)
- `database`: Database name
- `user`: Username for authentication
- `password`: Password for authentication

**Security Note**: Never hardcode credentials in scripts. Use environment variables or prompt the user for credentials.

## Helper Scripts

- `scripts/query_postgres.py` - Execute SQL queries and return results
- `scripts/list_tables.py` - List all tables in the database

Always run scripts with `--help` first to see usage options.

## Quick Start

### Execute a Query

```bash
python scripts/query_postgres.py --host localhost --port 5432 --database mydb --user myuser --query "SELECT * FROM users LIMIT 10"
```

Or use environment variables:
```bash
export PGHOST=localhost
export PGPORT=5432
export PGDATABASE=mydb
export PGUSER=myuser
export PGPASSWORD=mypassword
python scripts/query_postgres.py --query "SELECT * FROM users LIMIT 10"
```

### List Tables

```bash
python scripts/list_tables.py --host localhost --port 5432 --database mydb --user myuser
```

## Writing Queries Directly in Python

For complex workflows, write Python scripts using psycopg2:

```python
import psycopg2
import os

# Connection using environment variables
conn = psycopg2.connect(
    host=os.environ.get('PGHOST', 'localhost'),
    port=os.environ.get('PGPORT', '5432'),
    database=os.environ['PGDATABASE'],
    user=os.environ['PGUSER'],
    password=os.environ['PGPASSWORD']
)

try:
    with conn.cursor() as cur:
        cur.execute("SELECT * FROM users WHERE active = %s", (True,))
        rows = cur.fetchall()
        for row in rows:
            print(row)
finally:
    conn.close()
```

## Best Practices

### Query Safety
- Always use parameterized queries to prevent SQL injection
- Use `LIMIT` clauses to avoid returning excessive data
- For read-only operations, use `SET TRANSACTION READ ONLY`

### Connection Management
- Always close connections after use
- Use context managers (`with` statements) when possible
- Set appropriate timeouts for long-running queries

### Data Handling
- Handle NULL values appropriately
- Be aware of data types when processing results
- Use `fetchmany()` for large result sets to manage memory

## Common Tasks

### Explore Database Structure

```sql
-- List all schemas
SELECT schema_name FROM information_schema.schemata;

-- List tables in a schema
SELECT table_name FROM information_schema.tables 
WHERE table_schema = 'public';

-- Describe a table's columns
SELECT column_name, data_type, is_nullable 
FROM information_schema.columns 
WHERE table_name = 'your_table';
```

### Data Analysis Examples

```sql
-- Count rows
SELECT COUNT(*) FROM your_table;

-- Group by with aggregation
SELECT category, COUNT(*), AVG(value) 
FROM your_table 
GROUP BY category;

-- Find duplicates
SELECT column, COUNT(*) 
FROM your_table 
GROUP BY column 
HAVING COUNT(*) > 1;
```

## Troubleshooting

- **Connection refused**: Check host, port, and firewall settings
- **Authentication failed**: Verify username and password
- **Database does not exist**: Confirm database name is correct
- **Permission denied**: User may lack required privileges

## Reference Files

- [Connection Guide](references/connection_guide.md) - Detailed connection configuration options
