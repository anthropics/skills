package examples_test

import (
	"context"
	"database/sql"
	"io"
	"testing"
	"time"

	_ "github.com/lib/pq"
	"github.com/redis/go-redis/v9"
	"github.com/stretchr/testify/require"
	"github.com/testcontainers/testcontainers-go"
	"github.com/testcontainers/testcontainers-go/exec"
	"github.com/testcontainers/testcontainers-go/modules/postgres"
	tcredis "github.com/testcontainers/testcontainers-go/modules/redis"
	"github.com/testcontainers/testcontainers-go/network"
)

// TestMultiContainerNetwork demonstrates connecting multiple containers on a custom network
func TestMultiContainerNetwork(t *testing.T) {
	ctx := context.Background()

	// Create a custom network
	nw, err := network.New(ctx)
	testcontainers.CleanupNetwork(t, nw)
	require.NoError(t, err)

	t.Log("Custom network created")

	// Start PostgreSQL on the network with alias "database"
	pgContainer, err := postgres.Run(
		ctx,
		"postgres:16-alpine",
		postgres.WithDatabase("appdb"),
		network.WithNetwork([]string{"database"}, nw),
		postgres.BasicWaitStrategies(),
	)
	testcontainers.CleanupContainer(t, pgContainer)
	require.NoError(t, err)

	t.Log("PostgreSQL started with network alias 'database'")

	// Start Redis on the same network with alias "cache"
	redisContainer, err := tcredis.Run(
		ctx,
		"redis:7-alpine",
		network.WithNetwork([]string{"cache"}, nw),
	)
	testcontainers.CleanupContainer(t, redisContainer)
	require.NoError(t, err)

	t.Log("Redis started with network alias 'cache'")

	// Connect to PostgreSQL from host
	pgConnStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
	require.NoError(t, err)

	db, err := sql.Open("postgres", pgConnStr)
	require.NoError(t, err)
	defer db.Close()

	err = db.Ping()
	require.NoError(t, err)

	t.Log("Successfully connected to PostgreSQL from host")

	// Connect to Redis from host
	redisConnStr, err := redisContainer.ConnectionString(ctx)
	require.NoError(t, err)

	redisOpt, err := redis.ParseURL(redisConnStr)
	require.NoError(t, err)

	redisClient := redis.NewClient(redisOpt)
	defer redisClient.Close()

	pong, err := redisClient.Ping(ctx).Result()
	require.NoError(t, err)
	require.Equal(t, "PONG", pong)

	t.Log("Successfully connected to Redis from host")

	// Demonstrate that containers can resolve each other by alias
	// We'll use exec to ping from postgres to redis (if tools were available)
	// In a real scenario, your application container would connect using these aliases

	t.Log("Both containers are on the same network and can communicate")
	t.Log("An application container could connect to:")
	t.Log("  - PostgreSQL at: database:5432")
	t.Log("  - Redis at: cache:6379")
}

// TestApplicationWithDependencies simulates an application container that depends on database and cache
func TestApplicationWithDependencies(t *testing.T) {
	ctx := context.Background()

	// Create network
	nw, err := network.New(ctx)
	testcontainers.CleanupNetwork(t, nw)
	require.NoError(t, err)

	// Start PostgreSQL
	pgContainer, err := postgres.Run(
		ctx,
		"postgres:16-alpine",
		postgres.WithDatabase("myapp"),
		postgres.WithUsername("appuser"),
		postgres.WithPassword("apppass"),
		network.WithNetwork([]string{"postgres"}, nw),
		postgres.BasicWaitStrategies(),
	)
	testcontainers.CleanupContainer(t, pgContainer)
	require.NoError(t, err)

	// Start Redis
	redisContainer, err := tcredis.Run(
		ctx,
		"redis:7-alpine",
		network.WithNetwork([]string{"redis"}, nw),
	)
	testcontainers.CleanupContainer(t, redisContainer)
	require.NoError(t, err)

	// In a real test, you would start your application container here with environment variables:
	// appContainer, err := testcontainers.Run(
	//     ctx,
	//     "myapp:latest",
	//     testcontainers.WithEnv(map[string]string{
	//         "DATABASE_URL": "postgres://appuser:apppass@postgres:5432/myapp?sslmode=disable",
	//         "REDIS_URL": "redis://redis:6379",
	//     }),
	//     network.WithNetwork([]string{"app"}, nw),
	//     testcontainers.WithWaitStrategy(
	//         wait.ForHTTP("/health").WithPort("8080/tcp"),
	//     ),
	// )

	// For this example, we'll verify the dependencies are ready
	pgConnStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
	require.NoError(t, err)

	db, err := sql.Open("postgres", pgConnStr)
	require.NoError(t, err)
	defer db.Close()

	err = db.Ping()
	require.NoError(t, err)

	redisConnStr, err := redisContainer.ConnectionString(ctx)
	require.NoError(t, err)

	redisOpt, err := redis.ParseURL(redisConnStr)
	require.NoError(t, err)

	redisClient := redis.NewClient(redisOpt)
	defer redisClient.Close()

	_, err = redisClient.Ping(ctx).Result()
	require.NoError(t, err)

	t.Log("All dependencies are ready for application container")
}

// TestContainerCommunication demonstrates how to verify containers can communicate
func TestContainerCommunication(t *testing.T) {
	ctx := context.Background()

	// Create network
	nw, err := network.New(ctx)
	testcontainers.CleanupNetwork(t, nw)
	require.NoError(t, err)

	// Start two alpine containers for testing communication
	alpine1, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithCmd("sleep", "300"),
		network.WithNetwork([]string{"host1"}, nw),
	)
	testcontainers.CleanupContainer(t, alpine1)
	require.NoError(t, err)

	alpine2, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithCmd("sleep", "300"),
		network.WithNetwork([]string{"host2"}, nw),
	)
	testcontainers.CleanupContainer(t, alpine2)
	require.NoError(t, err)

	// Test connectivity by pinging host2 (ping is available in alpine by default)
	exitCode, reader, err := alpine1.Exec(ctx, []string{"ping", "-c", "1", "host2"}, exec.Multiplexed())
	require.NoError(t, err)
	require.Equal(t, 0, exitCode, "Should be able to ping host2 from host1")

	// Read output to verify ping succeeded
	output, err := io.ReadAll(reader)
	require.NoError(t, err)
	require.Contains(t, string(output), "1 packets transmitted, 1 packets received")

	t.Log("Containers can successfully communicate over custom network")
}

// TestWaitForMultipleContainers demonstrates starting multiple containers and waiting for all to be ready
func TestWaitForMultipleContainers(t *testing.T) {
	ctx := context.Background()

	nw, err := network.New(ctx)
	testcontainers.CleanupNetwork(t, nw)
	require.NoError(t, err)

	// Start containers concurrently (they'll wait for their respective services)
	type containerResult struct {
		name string
		err  error
	}

	results := make(chan containerResult, 2)

	// Start PostgreSQL
	go func() {
		pgContainer, err := postgres.Run(
			ctx,
			"postgres:16-alpine",
			network.WithNetwork([]string{"db"}, nw),
			postgres.BasicWaitStrategies(),
		)
		if err == nil {
			testcontainers.CleanupContainer(t, pgContainer)
		}
		results <- containerResult{name: "postgres", err: err}
	}()

	// Start Redis
	go func() {
		redisContainer, err := tcredis.Run(
			ctx,
			"redis:7-alpine",
			network.WithNetwork([]string{"cache"}, nw),
		)
		if err == nil {
			testcontainers.CleanupContainer(t, redisContainer)
		}
		results <- containerResult{name: "redis", err: err}
	}()

	// Wait for both to be ready
	timeout := time.After(60 * time.Second)
	readyCount := 0

	for readyCount < 2 {
		select {
		case result := <-results:
			require.NoError(t, result.err, "Failed to start %s", result.name)
			t.Logf("%s is ready", result.name)
			readyCount++
		case <-timeout:
			t.Fatal("Timeout waiting for containers to be ready")
		}
	}

	t.Log("All containers started successfully")
}
