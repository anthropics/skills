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

// TestBasicPostgres demonstrates the most basic usage of the PostgreSQL module
func TestBasicPostgres(t *testing.T) {
	ctx := context.Background()

	// Start PostgreSQL container with default settings
	pgContainer, err := postgres.Run(ctx, "postgres:16-alpine", postgres.BasicWaitStrategies())
	testcontainers.CleanupContainer(t, pgContainer)
	require.NoError(t, err)

	// Get connection string
	connStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
	require.NoError(t, err)

	// Connect to database
	db, err := sql.Open("postgres", connStr)
	require.NoError(t, err)
	defer db.Close()

	// Verify connection
	err = db.Ping()
	require.NoError(t, err)

	// Run a simple query
	var result int
	err = db.QueryRow("SELECT 1 + 1").Scan(&result)
	require.NoError(t, err)
	require.Equal(t, 2, result)

	t.Log("Successfully connected to PostgreSQL and ran a query")
}

// TestPostgresWithCustomConfig demonstrates using custom database, user, and password
func TestPostgresWithCustomConfig(t *testing.T) {
	ctx := context.Background()

	// Start PostgreSQL with custom configuration
	pgContainer, err := postgres.Run(
		ctx,
		"postgres:16-alpine",
		postgres.WithDatabase("testdb"),
		postgres.WithUsername("testuser"),
		postgres.WithPassword("testpass"),
		postgres.BasicWaitStrategies(),
	)
	testcontainers.CleanupContainer(t, pgContainer)
	require.NoError(t, err)

	// Get connection string
	connStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
	require.NoError(t, err)

	// Verify the connection string contains our custom values
	require.Contains(t, connStr, "testuser")
	require.Contains(t, connStr, "testpass")
	require.Contains(t, connStr, "testdb")

	// Connect and verify
	db, err := sql.Open("postgres", connStr)
	require.NoError(t, err)
	defer db.Close()

	err = db.Ping()
	require.NoError(t, err)

	t.Log("Successfully connected to PostgreSQL with custom configuration")
}

// TestPostgresWithSchema demonstrates using init scripts to set up a schema
func TestPostgresWithSchema(t *testing.T) {
	ctx := context.Background()

	// Note: In a real test, you would create a schema.sql file in testdata/
	// For this example, we'll use WithDatabase and create the table manually
	pgContainer, err := postgres.Run(
		ctx,
		"postgres:16-alpine",
		postgres.WithDatabase("appdb"),
		postgres.BasicWaitStrategies(),
	)
	testcontainers.CleanupContainer(t, pgContainer)
	require.NoError(t, err)

	connStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
	require.NoError(t, err)

	db, err := sql.Open("postgres", connStr)
	require.NoError(t, err)
	defer db.Close()

	// Create a simple schema
	_, err = db.Exec(`
		CREATE TABLE users (
			id SERIAL PRIMARY KEY,
			name TEXT NOT NULL,
			email TEXT UNIQUE NOT NULL,
			created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
		)
	`)
	require.NoError(t, err)

	// Insert a test record
	_, err = db.Exec(`INSERT INTO users (name, email) VALUES ($1, $2)`, "Alice", "alice@example.com")
	require.NoError(t, err)

	// Query the record
	var name, email string
	err = db.QueryRow(`SELECT name, email FROM users WHERE email = $1`, "alice@example.com").Scan(&name, &email)
	require.NoError(t, err)
	require.Equal(t, "Alice", name)
	require.Equal(t, "alice@example.com", email)

	t.Log("Successfully created schema and inserted data")
}
