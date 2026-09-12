# PostgreSQL Connection Guide

This guide covers detailed connection configuration options for PostgreSQL.

## Connection Methods

### 1. Environment Variables

The most secure method for storing credentials:

```bash
export PGHOST=localhost
export PGPORT=5432
export PGDATABASE=mydb
export PGUSER=myuser
export PGPASSWORD=mypassword
```

### 2. Connection String (DSN)

```python
import psycopg2

# Standard format
conn = psycopg2.connect("host=localhost port=5432 dbname=mydb user=myuser password=mypassword")

# URI format
conn = psycopg2.connect("postgresql://myuser:mypassword@localhost:5432/mydb")
```

### 3. Connection Dictionary

```python
import psycopg2

conn = psycopg2.connect(
    host="localhost",
    port=5432,
    database="mydb",
    user="myuser",
    password="mypassword"
)
```

## SSL/TLS Configuration

For secure connections, configure SSL:

```python
import psycopg2

conn = psycopg2.connect(
    host="db.example.com",
    port=5432,
    database="mydb",
    user="myuser",
    password="mypassword",
    sslmode="require",  # Options: disable, allow, prefer, require, verify-ca, verify-full
    sslrootcert="/path/to/ca.crt",
    sslcert="/path/to/client.crt",
    sslkey="/path/to/client.key"
)
```

### SSL Mode Options

| Mode | Description |
|------|-------------|
| `disable` | No SSL |
| `allow` | Try non-SSL first, then SSL |
| `prefer` | Try SSL first, then non-SSL (default) |
| `require` | Require SSL, skip server certificate verification |
| `verify-ca` | Require SSL and verify server certificate authority |
| `verify-full` | Require SSL, verify CA and hostname |

## Connection Pooling

For applications with multiple queries, use connection pooling:

```python
from psycopg2 import pool

# Create a connection pool
connection_pool = pool.ThreadedConnectionPool(
    minconn=1,
    maxconn=10,
    host="localhost",
    port=5432,
    database="mydb",
    user="myuser",
    password="mypassword"
)

# Get a connection from the pool
conn = connection_pool.getconn()

try:
    with conn.cursor() as cur:
        cur.execute("SELECT * FROM users")
        results = cur.fetchall()
finally:
    # Return connection to pool
    connection_pool.putconn(conn)

# Close all connections when done
connection_pool.closeall()
```

## Timeout Configuration

```python
import psycopg2

conn = psycopg2.connect(
    host="localhost",
    database="mydb",
    user="myuser",
    password="mypassword",
    connect_timeout=10,  # Connection timeout in seconds
    options="-c statement_timeout=30000"  # Query timeout in milliseconds
)
```

## Read Replica Configuration

For read-heavy workloads with replicas:

```python
import psycopg2

# Primary for writes
primary_conn = psycopg2.connect(
    host="primary.db.example.com",
    database="mydb",
    user="myuser",
    password="mypassword"
)

# Replica for reads
replica_conn = psycopg2.connect(
    host="replica.db.example.com",
    database="mydb",
    user="myuser",
    password="mypassword",
    options="-c default_transaction_read_only=on"
)
```

## Common Connection Issues

### Issue: Connection Refused

**Causes:**
- PostgreSQL not running
- Wrong host or port
- Firewall blocking connection

**Solutions:**
```bash
# Check if PostgreSQL is running
pg_isready -h localhost -p 5432

# Check firewall rules
sudo ufw status
```

### Issue: Authentication Failed

**Causes:**
- Wrong username or password
- User doesn't exist
- pg_hba.conf restrictions

**Solutions:**
```sql
-- Check if user exists
SELECT * FROM pg_roles WHERE rolname = 'myuser';

-- Check authentication method in pg_hba.conf
```

### Issue: SSL Required

**Cause:** Server requires SSL but client didn't provide it

**Solution:**
```python
conn = psycopg2.connect(
    ...,
    sslmode="require"
)
```

### Issue: Too Many Connections

**Cause:** Connection limit exceeded

**Solutions:**
```sql
-- Check current connections
SELECT count(*) FROM pg_stat_activity;

-- Check max connections
SHOW max_connections;
```

Use connection pooling to manage connections efficiently.

## Security Best Practices

1. **Never hardcode credentials** - Use environment variables or secret managers
2. **Use SSL** - Always use `sslmode=require` or higher in production
3. **Limit privileges** - Create users with minimal required permissions
4. **Use connection pooling** - Reduces connection overhead and limits exposure
5. **Set timeouts** - Prevent hanging connections

```python
import os

# Secure connection example
conn = psycopg2.connect(
    host=os.environ['PGHOST'],
    port=os.environ.get('PGPORT', 5432),
    database=os.environ['PGDATABASE'],
    user=os.environ['PGUSER'],
    password=os.environ['PGPASSWORD'],
    sslmode='require',
    connect_timeout=10
)
```
