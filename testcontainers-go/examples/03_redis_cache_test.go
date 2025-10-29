package examples_test

import (
	"context"
	"testing"
	"time"

	"github.com/redis/go-redis/v9"
	"github.com/stretchr/testify/require"
	"github.com/testcontainers/testcontainers-go"
	tcredis "github.com/testcontainers/testcontainers-go/modules/redis"
)

// TestBasicRedis demonstrates basic Redis operations
func TestBasicRedis(t *testing.T) {
	ctx := context.Background()

	// Start Redis container
	redisContainer, err := tcredis.Run(ctx, "redis:7-alpine")
	testcontainers.CleanupContainer(t, redisContainer)
	require.NoError(t, err)

	// Get connection string
	connStr, err := redisContainer.ConnectionString(ctx)
	require.NoError(t, err)

	// Connect to Redis
	opt, err := redis.ParseURL(connStr)
	require.NoError(t, err)

	client := redis.NewClient(opt)
	defer client.Close()

	// Test SET and GET
	err = client.Set(ctx, "greeting", "Hello, Testcontainers!", 0).Err()
	require.NoError(t, err)

	val, err := client.Get(ctx, "greeting").Result()
	require.NoError(t, err)
	require.Equal(t, "Hello, Testcontainers!", val)

	t.Log("Successfully performed SET and GET operations")
}

// TestRedisWithExpiration demonstrates key expiration
func TestRedisWithExpiration(t *testing.T) {
	ctx := context.Background()

	redisContainer, err := tcredis.Run(ctx, "redis:7-alpine")
	testcontainers.CleanupContainer(t, redisContainer)
	require.NoError(t, err)

	connStr, err := redisContainer.ConnectionString(ctx)
	require.NoError(t, err)

	opt, err := redis.ParseURL(connStr)
	require.NoError(t, err)

	client := redis.NewClient(opt)
	defer client.Close()

	// Set a key with 2-second expiration
	err = client.Set(ctx, "temporary", "I will expire", 2*time.Second).Err()
	require.NoError(t, err)

	// Verify key exists
	val, err := client.Get(ctx, "temporary").Result()
	require.NoError(t, err)
	require.Equal(t, "I will expire", val)

	t.Log("Key set with 2-second expiration")

	// Wait for expiration
	time.Sleep(3 * time.Second)

	// Verify key is gone
	_, err = client.Get(ctx, "temporary").Result()
	require.Equal(t, redis.Nil, err, "Key should have expired")

	t.Log("Key successfully expired")
}

// TestRedisListOperations demonstrates list operations
func TestRedisListOperations(t *testing.T) {
	ctx := context.Background()

	redisContainer, err := tcredis.Run(ctx, "redis:7-alpine")
	testcontainers.CleanupContainer(t, redisContainer)
	require.NoError(t, err)

	connStr, err := redisContainer.ConnectionString(ctx)
	require.NoError(t, err)

	opt, err := redis.ParseURL(connStr)
	require.NoError(t, err)

	client := redis.NewClient(opt)
	defer client.Close()

	// Push items to list
	err = client.RPush(ctx, "tasks", "task1", "task2", "task3").Err()
	require.NoError(t, err)

	// Get list length
	length, err := client.LLen(ctx, "tasks").Result()
	require.NoError(t, err)
	require.Equal(t, int64(3), length)

	// Pop items from list
	task, err := client.LPop(ctx, "tasks").Result()
	require.NoError(t, err)
	require.Equal(t, "task1", task)

	// Get remaining items
	tasks, err := client.LRange(ctx, "tasks", 0, -1).Result()
	require.NoError(t, err)
	require.Equal(t, []string{"task2", "task3"}, tasks)

	t.Log("Successfully performed list operations")
}

// TestRedisHashOperations demonstrates hash operations
func TestRedisHashOperations(t *testing.T) {
	ctx := context.Background()

	redisContainer, err := tcredis.Run(ctx, "redis:7-alpine")
	testcontainers.CleanupContainer(t, redisContainer)
	require.NoError(t, err)

	connStr, err := redisContainer.ConnectionString(ctx)
	require.NoError(t, err)

	opt, err := redis.ParseURL(connStr)
	require.NoError(t, err)

	client := redis.NewClient(opt)
	defer client.Close()

	// Set hash fields
	err = client.HSet(ctx, "user:1000", map[string]interface{}{
		"name":  "John Doe",
		"email": "john@example.com",
		"age":   "30",
	}).Err()
	require.NoError(t, err)

	// Get single field
	name, err := client.HGet(ctx, "user:1000", "name").Result()
	require.NoError(t, err)
	require.Equal(t, "John Doe", name)

	// Get all fields
	user, err := client.HGetAll(ctx, "user:1000").Result()
	require.NoError(t, err)
	require.Equal(t, "John Doe", user["name"])
	require.Equal(t, "john@example.com", user["email"])
	require.Equal(t, "30", user["age"])

	t.Log("Successfully performed hash operations")
}

// TestRedisWithConfig demonstrates using Redis with custom configuration
func TestRedisWithConfig(t *testing.T) {
	ctx := context.Background()

	// Start Redis with snapshotting and verbose logging
	redisContainer, err := tcredis.Run(
		ctx,
		"redis:7-alpine",
		tcredis.WithSnapshotting(10, 1), // Save after 1 key changes within 10 seconds
		tcredis.WithLogLevel(tcredis.LogLevelVerbose),
	)
	testcontainers.CleanupContainer(t, redisContainer)
	require.NoError(t, err)

	connStr, err := redisContainer.ConnectionString(ctx)
	require.NoError(t, err)

	opt, err := redis.ParseURL(connStr)
	require.NoError(t, err)

	client := redis.NewClient(opt)
	defer client.Close()

	// Verify Redis is running
	pong, err := client.Ping(ctx).Result()
	require.NoError(t, err)
	require.Equal(t, "PONG", pong)

	t.Log("Redis running with custom configuration")
}
