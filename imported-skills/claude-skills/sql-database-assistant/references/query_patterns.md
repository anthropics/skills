# SQL Query Patterns Reference

Common query patterns for everyday database operations. All examples use PostgreSQL syntax with dialect notes where they differ.

---

## JOIN Patterns

### INNER JOIN — matching rows in both tables
```sql
SELECT u.name, o.id AS order_id, o.total
FROM users u
INNER JOIN orders o ON o.user_id = u.id
WHERE o.status = 'paid';
```

### LEFT JOIN — all rows from left, matching from right
```sql
SELECT u.name, COUNT(o.id) AS order_count
FROM users u
LEFT JOIN orders o ON o.user_id = u.id
GROUP BY u.id, u.name;
```
Returns users even if they have zero orders.

### Self JOIN — comparing rows within the same table
```sql
-- Find employees who earn more than their manager
SELECT e.name AS employee, m.name AS manager, e.salary, m.salary AS manager_salary
FROM employees e
JOIN employees m ON e.manager_id = m.id
WHERE e.salary > m.salary;
```

### CROSS JOIN — every combination (cartesian product)
```sql
-- Generate a calendar grid
SELECT d.date, s.shift_name
FROM dates d
CROSS JOIN shifts s;
```
Use intentionally. Accidental cartesian joins are a performance killer.

### LATERAL JOIN (PostgreSQL) — correlated subquery as a table
```sql
-- Top 3 orders per user
SELECT u.name, top_orders.*
FROM users u
CROSS JOIN LATERAL (
  SELECT id, total FROM orders
  WHERE user_id = u.id
  ORDER BY total DESC LIMIT 3
) top_orders;
```
MySQL equivalent: use a subquery with `ROW_NUMBER()`.

---

## Common Table Expressions (CTEs)

### Basic CTE — readable subquery
```sql
WITH active_users AS (
  SELECT id, name, email
  FROM users
  WHERE last_login > CURRENT_DATE - INTERVAL '30 days'
)
SELECT au.name, COUNT(o.id) AS recent_orders
FROM active_users au
JOIN orders o ON o.user_id = au.id
GROUP BY au.name;
```

### Multiple CTEs — chaining transformations
```sql
WITH monthly_revenue AS (
  SELECT DATE_TRUNC('month', created_at) AS month, SUM(total) AS revenue
  FROM orders WHERE status = 'paid'
  GROUP BY 1
),
growth AS (
  SELECT month, revenue,
    LAG(revenue) OVER (ORDER BY month) AS prev_revenue,
    ROUND((revenue - LAG(revenue) OVER (ORDER BY month)) / LAG(revenue) OVER (ORDER BY month) * 100, 1) AS growth_pct
  FROM monthly_revenue
)
SELECT * FROM growth ORDER BY month;
```

### Recursive CTE — hierarchical data
```sql
-- Organization tree
WITH RECURSIVE org_tree AS (
  -- Base case: top-level managers
  SELECT id, name, manager_id, 0 AS depth
  FROM employees WHERE manager_id IS NULL

  UNION ALL

  -- Recursive case: subordinates
  SELECT e.id, e.name, e.manager_id, ot.depth + 1
  FROM employees e
  JOIN org_tree ot ON e.manager_id = ot.id
)
SELECT * FROM org_tree ORDER BY depth, name;
```

### Recursive CTE — path traversal
```sql
-- Category breadcrumb
WITH RECURSIVE breadcrumb AS (
  SELECT id, name, parent_id, name::TEXT AS path
  FROM categories WHERE id = 42

  UNION ALL

  SELECT c.id, c.name, c.parent_id, c.name || ' > ' || b.path
  FROM categories c
  JOIN breadcrumb b ON c.id = b.parent_id
)
SELECT path FROM breadcrumb WHERE parent_id IS NULL;
```

---

## Window Functions

### ROW_NUMBER — assign unique rank per partition
```sql
SELECT *, ROW_NUMBER() OVER (PARTITION BY department_id ORDER BY salary DESC) AS rank
FROM employees;
```

### RANK and DENSE_RANK — handle ties
```sql
-- RANK: 1, 2, 2, 4 (skips after tie)
-- DENSE_RANK: 1, 2, 2, 3 (no skip)
SELECT name, salary,
  RANK() OVER (ORDER BY salary DESC) AS rank,
  DENSE_RANK() OVER (ORDER BY salary DESC) AS dense_rank
FROM employees;
```

### Running total and moving average
```sql
SELECT date, amount,
  SUM(amount) OVER (ORDER BY date) AS running_total,
  AVG(amount) OVER (ORDER BY date ROWS BETWEEN 6 PRECEDING AND CURRENT ROW) AS moving_avg_7d
FROM daily_revenue;
```

### LAG / LEAD — access adjacent rows
```sql
SELECT date, revenue,
  LAG(revenue, 1) OVER (ORDER BY date) AS prev_day,
  revenue - LAG(revenue, 1) OVER (ORDER BY date) AS day_over_day_change
FROM daily_revenue;
```

### NTILE — divide into buckets
```sql
-- Split customers into quartiles by total spend
SELECT customer_id, total_spend,
  NTILE(4) OVER (ORDER BY total_spend DESC) AS spend_quartile
FROM customer_summary;
```

### FIRST_VALUE / LAST_VALUE
```sql
SELECT department_id, name, salary,
  FIRST_VALUE(name) OVER (PARTITION BY department_id ORDER BY salary DESC) AS highest_paid
FROM employees;
```

---

## Subquery Patterns

### EXISTS — correlated existence check
```sql
-- Users who have placed at least one order
SELECT u.* FROM users u
WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id);
```

### NOT EXISTS — safer than NOT IN for NULLs
```sql
-- Users who have never ordered
SELECT u.* FROM users u
WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id);
```

### Scalar subquery — single value
```sql
SELECT name, salary,
  salary - (SELECT AVG(salary) FROM employees) AS diff_from_avg
FROM employees;
```

### Derived table — subquery in FROM
```sql
SELECT dept, avg_salary
FROM (
  SELECT department_id AS dept, AVG(salary) AS avg_salary
  FROM employees GROUP BY department_id
) dept_avg
WHERE avg_salary > 100000;
```

---

## Aggregation Patterns

### GROUP BY with HAVING
```sql
-- Departments with more than 10 employees
SELECT department_id, COUNT(*) AS headcount, AVG(salary) AS avg_salary
FROM employees
GROUP BY department_id
HAVING COUNT(*) > 10;
```

### GROUPING SETS — multiple grouping levels
```sql
SELECT region, product_category, SUM(revenue)
FROM sales
GROUP BY GROUPING SETS (
  (region, product_category),
  (region),
  (product_category),
  ()
);
```

### ROLLUP — hierarchical subtotals
```sql
SELECT region, city, SUM(revenue)
FROM sales
GROUP BY ROLLUP (region, city);
-- Produces: (region, city), (region), ()
```

### CUBE — all combinations
```sql
SELECT region, product, SUM(revenue)
FROM sales
GROUP BY CUBE (region, product);
```

### FILTER clause (PostgreSQL) — conditional aggregation
```sql
SELECT
  COUNT(*) AS total,
  COUNT(*) FILTER (WHERE status = 'paid') AS paid,
  COUNT(*) FILTER (WHERE status = 'cancelled') AS cancelled,
  SUM(total) FILTER (WHERE status = 'paid') AS paid_revenue
FROM orders;
```
MySQL/SQL Server equivalent: `SUM(CASE WHEN status = 'paid' THEN 1 ELSE 0 END)`.

---

## UPSERT Patterns

### PostgreSQL — ON CONFLICT
```sql
INSERT INTO user_settings (user_id, key, value, updated_at)
VALUES (1, 'theme', 'dark', NOW())
ON CONFLICT (user_id, key)
DO UPDATE SET value = EXCLUDED.value, updated_at = EXCLUDED.updated_at;
```

### MySQL — ON DUPLICATE KEY
```sql
INSERT INTO user_settings (user_id, key_name, value, updated_at)
VALUES (1, 'theme', 'dark', NOW())
ON DUPLICATE KEY UPDATE value = VALUES(value), updated_at = VALUES(updated_at);
```

### SQL Server — MERGE
```sql
MERGE INTO user_settings AS target
USING (VALUES (1, 'theme', 'dark')) AS source (user_id, key_name, value)
ON target.user_id = source.user_id AND target.key_name = source.key_name
WHEN MATCHED THEN UPDATE SET value = source.value, updated_at = GETDATE()
WHEN NOT MATCHED THEN INSERT (user_id, key_name, value, updated_at)
  VALUES (source.user_id, source.key_name, source.value, GETDATE());
```

---

## JSON Operations

### PostgreSQL JSONB
```sql
-- Extract field
SELECT data->>'name' AS name FROM products WHERE data->>'category' = 'electronics';

-- Array contains
SELECT * FROM products WHERE data->'tags' ? 'sale';

-- Update nested field
UPDATE products SET data = jsonb_set(data, '{price}', '29.99') WHERE id = 1;

-- Aggregate into JSON array
SELECT jsonb_agg(jsonb_build_object('id', id, 'name', name)) FROM users;
```

### MySQL JSON
```sql
-- Extract field
SELECT JSON_EXTRACT(data, '$.name') AS name FROM products;
-- Shorthand: SELECT data->>"$.name"

-- Search in array
SELECT * FROM products WHERE JSON_CONTAINS(data->"$.tags", '"sale"');

-- Update
UPDATE products SET data = JSON_SET(data, '$.price', 29.99) WHERE id = 1;
```

---

## Pagination Patterns

### Offset pagination (simple but slow for deep pages)
```sql
SELECT * FROM products ORDER BY id LIMIT 20 OFFSET 40;
```

### Keyset pagination (fast, requires ordered unique column)
```sql
-- Page after the last seen id
SELECT * FROM products WHERE id > :last_seen_id ORDER BY id LIMIT 20;
```

### Keyset with composite sort
```sql
SELECT * FROM products
WHERE (created_at, id) < (:last_created_at, :last_id)
ORDER BY created_at DESC, id DESC
LIMIT 20;
```

---

## Bulk Operations

### Batch INSERT
```sql
INSERT INTO events (type, payload, created_at) VALUES
  ('click', '{"page": "/home"}', NOW()),
  ('view', '{"page": "/pricing"}', NOW()),
  ('click', '{"page": "/signup"}', NOW());
```

### Batch UPDATE with VALUES
```sql
UPDATE products AS p SET price = v.price
FROM (VALUES (1, 29.99), (2, 49.99), (3, 9.99)) AS v(id, price)
WHERE p.id = v.id;
```

### DELETE with subquery
```sql
DELETE FROM sessions
WHERE user_id IN (SELECT id FROM users WHERE deleted_at IS NOT NULL);
```

### COPY (PostgreSQL bulk load)
```sql
COPY products (name, price, category) FROM '/path/to/data.csv' WITH (FORMAT csv, HEADER true);
```

---

## Utility Patterns

### Generate series (PostgreSQL)
```sql
-- Fill date gaps
SELECT d::date FROM generate_series('2025-01-01'::date, '2025-12-31', '1 day') d;
```

### Deduplicate rows
```sql
DELETE FROM events a USING events b
WHERE a.id > b.id AND a.user_id = b.user_id AND a.event_type = b.event_type
  AND a.created_at = b.created_at;
```

### Pivot (manual)
```sql
SELECT user_id,
  SUM(CASE WHEN month = 1 THEN revenue END) AS jan,
  SUM(CASE WHEN month = 2 THEN revenue END) AS feb,
  SUM(CASE WHEN month = 3 THEN revenue END) AS mar
FROM monthly_revenue
GROUP BY user_id;
```

### Conditional INSERT (skip if exists)
```sql
INSERT INTO tags (name) SELECT 'new-tag'
WHERE NOT EXISTS (SELECT 1 FROM tags WHERE name = 'new-tag');
```
