package examples_test

import (
	"context"
	"database/sql"
	"testing"

	_ "github.com/lib/pq"
	"github.com/stretchr/testify/require"
	"github.com/testcontainers/testcontainers-go"
	"github.com/testcontainers/testcontainers-go/modules/postgres"
)

// TestPostgresSnapshot demonstrates using snapshots for test isolation
// This is useful when you want to run multiple tests against the same initial state
func TestPostgresSnapshot(t *testing.T) {
	ctx := context.Background()

	// Start PostgreSQL container with a custom database (required for snapshots)
	// Note: Cannot snapshot the default 'postgres' system database
	pgContainer, err := postgres.Run(
		ctx,
		"postgres:16-alpine",
		postgres.WithDatabase("snapshotdb"),
		postgres.BasicWaitStrategies(),
	)
	testcontainers.CleanupContainer(t, pgContainer)
	require.NoError(t, err)

	connStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
	require.NoError(t, err)

	db, err := sql.Open("postgres", connStr)
	require.NoError(t, err)
	defer db.Close()

	// Create initial schema and data
	_, err = db.Exec(`
		CREATE TABLE products (
			id SERIAL PRIMARY KEY,
			name TEXT NOT NULL,
			price DECIMAL(10, 2) NOT NULL
		)
	`)
	require.NoError(t, err)

	_, err = db.Exec(`INSERT INTO products (name, price) VALUES ($1, $2)`, "Widget", 9.99)
	require.NoError(t, err)

	// Close connection before snapshot (PostgreSQL can't snapshot a database with active connections)
	db.Close()

	// Take a snapshot of the initial state
	err = pgContainer.Snapshot(ctx, postgres.WithSnapshotName("initial_state"))
	require.NoError(t, err)

	t.Log("Snapshot created with initial state")

	// Reconnect to modify the database
	db, err = sql.Open("postgres", connStr)
	require.NoError(t, err)

	// Modify the database
	_, err = db.Exec(`INSERT INTO products (name, price) VALUES ($1, $2)`, "Gadget", 19.99)
	require.NoError(t, err)

	// Verify we have 2 products
	var count int
	err = db.QueryRow(`SELECT COUNT(*) FROM products`).Scan(&count)
	require.NoError(t, err)
	require.Equal(t, 2, count)

	t.Log("Added second product, count is now 2")

	// Close connection before restore
	db.Close()

	// Restore to the snapshot
	err = pgContainer.Restore(ctx, postgres.WithSnapshotName("initial_state"))
	require.NoError(t, err)

	t.Log("Restored to initial snapshot")

	// Reconnect after restore
	db, err = sql.Open("postgres", connStr)
	require.NoError(t, err)
	defer db.Close()

	// Verify we're back to 1 product
	err = db.QueryRow(`SELECT COUNT(*) FROM products`).Scan(&count)
	require.NoError(t, err)
	require.Equal(t, 1, count, "After restore, should have only 1 product")

	// Verify it's the original product
	var name string
	var price float64
	err = db.QueryRow(`SELECT name, price FROM products WHERE id = 1`).Scan(&name, &price)
	require.NoError(t, err)
	require.Equal(t, "Widget", name)
	require.Equal(t, 9.99, price)

	t.Log("Successfully restored to initial state")
}

// TestPostgresMultipleSnapshots demonstrates using multiple named snapshots
func TestPostgresMultipleSnapshots(t *testing.T) {
	ctx := context.Background()

	// Use a custom database name (not 'postgres') for snapshots to work properly
	pgContainer, err := postgres.Run(
		ctx,
		"postgres:16-alpine",
		postgres.WithDatabase("testdb"),
		postgres.BasicWaitStrategies(),
	)
	testcontainers.CleanupContainer(t, pgContainer)
	require.NoError(t, err)

	connStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
	require.NoError(t, err)

	db, err := sql.Open("postgres", connStr)
	require.NoError(t, err)
	defer db.Close()

	// Create table
	_, err = db.Exec(`CREATE TABLE counters (id INT PRIMARY KEY, value INT)`)
	require.NoError(t, err)

	// State 1: Empty table
	// Close connection before snapshot (PostgreSQL can't snapshot a database with active connections)
	db.Close()
	err = pgContainer.Snapshot(ctx, postgres.WithSnapshotName("empty"))
	require.NoError(t, err)
	t.Log("Snapshot 'empty' created")

	// Reconnect to make changes
	db, err = sql.Open("postgres", connStr)
	require.NoError(t, err)

	// State 2: One record
	_, err = db.Exec(`INSERT INTO counters (id, value) VALUES (1, 10)`)
	require.NoError(t, err)

	// Close and snapshot
	db.Close()
	err = pgContainer.Snapshot(ctx, postgres.WithSnapshotName("one_record"))
	require.NoError(t, err)
	t.Log("Snapshot 'one_record' created")

	// Reconnect to make changes
	db, err = sql.Open("postgres", connStr)
	require.NoError(t, err)

	// State 3: Two records
	_, err = db.Exec(`INSERT INTO counters (id, value) VALUES (2, 20)`)
	require.NoError(t, err)

	// Close and snapshot
	db.Close()
	err = pgContainer.Snapshot(ctx, postgres.WithSnapshotName("two_records"))
	require.NoError(t, err)
	t.Log("Snapshot 'two_records' created")

	// Now restore to "one_record" state
	err = pgContainer.Restore(ctx, postgres.WithSnapshotName("one_record"))
	require.NoError(t, err)

	// Reconnect after restore
	db, err = sql.Open("postgres", connStr)
	require.NoError(t, err)
	defer db.Close()

	// Verify we have exactly 1 record
	var count int
	err = db.QueryRow(`SELECT COUNT(*) FROM counters`).Scan(&count)
	require.NoError(t, err)
	require.Equal(t, 1, count, "After restoring to 'one_record', should have 1 record")

	t.Log("Successfully restored to 'one_record' snapshot")
}
