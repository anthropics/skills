---
name: sql
description: Use this skill whenever the user wants to write SQL queries, work with databases, perform data analysis with SQL, optimize queries, design schemas, or interact with SQLite, PostgreSQL, MySQL, or other SQL databases. If the user mentions SELECT, INSERT, JOIN, database tables, SQL queries, or wants to query data from a .db or .sqlite file, use this skill.
license: Proprietary. LICENSE.txt has complete terms
---

# SQL Guide

## Overview

This guide covers SQL queries, database operations, and using Python to interact with SQL databases (SQLite, PostgreSQL, MySQL).

## SQLite with Python (built-in)

### Connect and Create Tables
```python
import sqlite3

conn = sqlite3.connect('database.db')  # creates file if not exists
cursor = conn.cursor()

cursor.execute('''
    CREATE TABLE IF NOT EXISTS users (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        email TEXT UNIQUE NOT NULL,
        age INTEGER,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
''')
conn.commit()
```

### Insert Data
```python
# Insert single row
cursor.execute(
    "INSERT INTO users (name, email, age) VALUES (?, ?, ?)",
    ('Alice', 'alice@example.com', 30)
)

# Insert multiple rows
users = [
    ('Bob', 'bob@example.com', 25),
    ('Carol', 'carol@example.com', 35),
]
cursor.executemany(
    "INSERT INTO users (name, email, age) VALUES (?, ?, ?)",
    users
)
conn.commit()
```

### Query Data
```python
# Fetch all rows
cursor.execute("SELECT * FROM users")
rows = cursor.fetchall()
for row in rows:
    print(row)

# Fetch one row
cursor.execute("SELECT * FROM users WHERE id = ?", (1,))
user = cursor.fetchone()

# Use column names (row factory)
conn.row_factory = sqlite3.Row
cursor = conn.cursor()
cursor.execute("SELECT * FROM users")
for row in cursor.fetchall():
    print(dict(row))  # {'id': 1, 'name': 'Alice', ...}
```

### Close Connection
```python
conn.close()

# Better: use context manager
with sqlite3.connect('database.db') as conn:
    cursor = conn.cursor()
    cursor.execute("SELECT * FROM users")
    print(cursor.fetchall())
```

## Core SQL Queries

### SELECT Fundamentals
```sql
-- Select all columns
SELECT * FROM users;

-- Select specific columns
SELECT name, email FROM users;

-- Filter rows
SELECT * FROM users WHERE age > 25;

-- Multiple conditions
SELECT * FROM users WHERE age > 25 AND name LIKE 'A%';

-- Order results
SELECT * FROM users ORDER BY age DESC;

-- Limit results
SELECT * FROM users ORDER BY created_at DESC LIMIT 10;

-- Distinct values
SELECT DISTINCT age FROM users;
```

### Aggregations
```sql
-- Count rows
SELECT COUNT(*) FROM users;
SELECT COUNT(*) FROM users WHERE age > 25;

-- Sum, avg, min, max
SELECT
    SUM(age) AS total_age,
    AVG(age) AS avg_age,
    MIN(age) AS min_age,
    MAX(age) AS max_age
FROM users;

-- Group by
SELECT age, COUNT(*) AS count
FROM users
GROUP BY age
ORDER BY count DESC;

-- Having (filter on aggregated values)
SELECT age, COUNT(*) AS count
FROM users
GROUP BY age
HAVING count > 2;
```

### JOINs
```sql
-- INNER JOIN (only matching rows)
SELECT u.name, o.product, o.amount
FROM users u
INNER JOIN orders o ON u.id = o.user_id;

-- LEFT JOIN (all users, even without orders)
SELECT u.name, o.product
FROM users u
LEFT JOIN orders o ON u.id = o.user_id;

-- Multiple JOINs
SELECT u.name, o.product, p.category
FROM users u
JOIN orders o ON u.id = o.user_id
JOIN products p ON o.product_id = p.id;
```

### Subqueries
```sql
-- Users who have placed orders
SELECT name FROM users
WHERE id IN (SELECT DISTINCT user_id FROM orders);

-- Users with above-average age
SELECT * FROM users
WHERE age > (SELECT AVG(age) FROM users);
```

### Common Table Expressions (CTEs)
```sql
WITH monthly_sales AS (
    SELECT
        strftime('%Y-%m', order_date) AS month,
        SUM(amount) AS total
    FROM orders
    GROUP BY month
),
ranked AS (
    SELECT *, RANK() OVER (ORDER BY total DESC) AS rank
    FROM monthly_sales
)
SELECT * FROM ranked WHERE rank <= 3;
```

### Window Functions
```sql
-- Running total
SELECT
    name,
    amount,
    SUM(amount) OVER (ORDER BY order_date) AS running_total
FROM orders;

-- Rank within group
SELECT
    name,
    department,
    salary,
    RANK() OVER (PARTITION BY department ORDER BY salary DESC) AS dept_rank
FROM employees;

-- Row number
SELECT
    ROW_NUMBER() OVER (ORDER BY created_at) AS row_num,
    *
FROM users;
```

### INSERT, UPDATE, DELETE
```sql
-- Insert
INSERT INTO users (name, email, age) VALUES ('Dave', 'dave@example.com', 28);

-- Update
UPDATE users SET age = 31 WHERE name = 'Alice';

-- Delete
DELETE FROM users WHERE id = 5;

-- Upsert (SQLite)
INSERT INTO users (email, name, age)
VALUES ('alice@example.com', 'Alice Updated', 31)
ON CONFLICT(email) DO UPDATE SET
    name = excluded.name,
    age = excluded.age;
```

## Using with Pandas

```python
import pandas as pd
import sqlite3

conn = sqlite3.connect('database.db')

# Read SQL query into DataFrame
df = pd.read_sql_query("SELECT * FROM users WHERE age > 25", conn)
print(df)

# Write DataFrame to SQL table
df.to_sql('users_backup', conn, if_exists='replace', index=False)

conn.close()
```

## PostgreSQL with psycopg2

```python
import psycopg2

conn = psycopg2.connect(
    host='localhost',
    database='mydb',
    user='postgres',
    password='password'
)
cursor = conn.cursor()

# Use %s placeholders (not ?)
cursor.execute("SELECT * FROM users WHERE age > %s", (25,))
rows = cursor.fetchall()

conn.commit()
cursor.close()
conn.close()
```

## Schema Design Tips

```sql
-- Use appropriate types
CREATE TABLE products (
    id SERIAL PRIMARY KEY,           -- auto-increment in PostgreSQL
    name VARCHAR(255) NOT NULL,
    price DECIMAL(10, 2) NOT NULL,
    stock INTEGER DEFAULT 0,
    is_active BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP DEFAULT NOW()
);

-- Foreign keys with cascade
CREATE TABLE orders (
    id SERIAL PRIMARY KEY,
    user_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
    product_id INTEGER REFERENCES products(id) ON DELETE RESTRICT,
    quantity INTEGER NOT NULL,
    ordered_at TIMESTAMP DEFAULT NOW()
);

-- Indexes for performance
CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_orders_user_id ON orders(user_id);
```

## Query Optimization

```sql
-- Use EXPLAIN to analyze query plan
EXPLAIN SELECT * FROM users WHERE email = 'alice@example.com';

-- Avoid SELECT * in production; name columns explicitly
SELECT id, name, email FROM users;  -- faster than SELECT *

-- Use LIMIT when you only need some rows
SELECT * FROM large_table LIMIT 100;

-- Filter early with WHERE before GROUP BY
SELECT department, AVG(salary)
FROM employees
WHERE is_active = TRUE          -- filter first
GROUP BY department;
```

## Quick Reference

| Operation | SQL |
|-----------|-----|
| Select all | `SELECT * FROM table` |
| Filter | `WHERE condition` |
| Sort | `ORDER BY col DESC` |
| Limit | `LIMIT n` |
| Count | `SELECT COUNT(*) FROM table` |
| Group | `GROUP BY col HAVING count > n` |
| Inner join | `JOIN t2 ON t1.id = t2.fk` |
| Left join | `LEFT JOIN t2 ON t1.id = t2.fk` |
| Insert | `INSERT INTO t (col) VALUES (val)` |
| Update | `UPDATE t SET col=val WHERE id=n` |
| Delete | `DELETE FROM t WHERE id=n` |
