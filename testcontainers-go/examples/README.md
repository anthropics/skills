# Testcontainers for Go Examples

This directory contains practical, runnable examples demonstrating various features and patterns of Testcontainers for Go.

## Prerequisites

Before running these examples, you need:

1. **Go 1.24+** installed
2. **Docker** running locally
3. Required Go packages:

```bash
go get github.com/testcontainers/testcontainers-go
go get github.com/testcontainers/testcontainers-go/modules/postgres
go get github.com/testcontainers/testcontainers-go/modules/redis
go get github.com/stretchr/testify/require
go get github.com/lib/pq
go get github.com/redis/go-redis/v9
```

## Examples Overview

### 01_postgres_basic_test.go
**Basic PostgreSQL Usage**

Demonstrates:
- Starting a PostgreSQL container with default settings
- Connecting to PostgreSQL
- Custom database configuration (database name, username, password)
- Creating schemas and inserting data

Run with:
```bash
go test -v -run TestBasicPostgres
go test -v -run TestPostgresWithCustomConfig
go test -v -run TestPostgresWithSchema
```

### 02_postgres_snapshot_test.go
**PostgreSQL Snapshots for Test Isolation**

Demonstrates:
- Creating database snapshots
- Modifying data and restoring to previous state
- Using multiple named snapshots

This is extremely useful for:
- Running multiple tests against the same initial state
- Test isolation without restarting containers
- Fast test execution

Run with:
```bash
go test -v -run TestPostgresSnapshot
go test -v -run TestPostgresMultipleSnapshots
```

### 03_redis_cache_test.go
**Redis Operations**

Demonstrates:
- Basic Redis key-value operations
- Key expiration
- List operations (RPUSH, LPOP, LRANGE)
- Hash operations (HSET, HGET, HGETALL)
- Custom Redis configuration (snapshotting, log levels)

Run with:
```bash
go test -v -run TestBasicRedis
go test -v -run TestRedisWithExpiration
go test -v -run TestRedisListOperations
go test -v -run TestRedisHashOperations
go test -v -run TestRedisWithConfig
```

### 04_multi_container_network_test.go
**Multi-Container Networking**

Demonstrates:
- Creating custom Docker networks
- Connecting multiple containers on the same network
- Container-to-container communication using network aliases
- Simulating microservices architectures
- Waiting for multiple containers concurrently

This is essential for:
- Integration testing with multiple services
- Testing service dependencies
- Simulating production-like environments

Run with:
```bash
go test -v -run TestMultiContainerNetwork
go test -v -run TestApplicationWithDependencies
go test -v -run TestContainerCommunication
go test -v -run TestWaitForMultipleContainers
```

### 05_generic_container_test.go
**Generic Container Patterns**

Demonstrates:
- Using containers without pre-configured modules
- Custom HTML content with nginx
- Environment variables
- Custom commands
- Container labels
- Temporary filesystems (tmpfs)
- Reading container logs
- Executing commands in running containers
- Different wait strategies (HTTP, log-based)
- Getting port information

Run with:
```bash
go test -v -run TestGenericNginx
go test -v -run TestGenericContainerWithCustomHTML
go test -v -run TestGenericContainerWithEnv
go test -v -run TestGenericContainerExec
# ... and many more
```

## Running All Examples

To run all examples:

```bash
# Run all tests
go test -v ./examples/

# Run all tests with more details
go test -v -count=1 ./examples/

# Run a specific example file
go test -v ./examples/01_postgres_basic_test.go
```

## Common Patterns

### 1. Basic Pattern (with Module)

```go
ctx := context.Background()

// Start container
pgContainer, err := postgres.Run(ctx, "postgres:16-alpine")
testcontainers.CleanupContainer(t, pgContainer)  // BEFORE error check!
require.NoError(t, err)

// Get connection details
connStr, err := pgContainer.ConnectionString(ctx)
require.NoError(t, err)

// Use the container...
```

### 2. Generic Container Pattern

```go
ctx := context.Background()

ctr, err := testcontainers.Run(
    ctx,
    "image:tag",
    testcontainers.WithExposedPorts("8080/tcp"),
    testcontainers.WithEnv(map[string]string{"KEY": "value"}),
    testcontainers.WithWaitStrategy(wait.ForListeningPort("8080/tcp")),
)
testcontainers.CleanupContainer(t, ctr)
require.NoError(t, err)
```

### 3. Multi-Container Pattern

```go
ctx := context.Background()

// Create network
nw, err := network.New(ctx)
testcontainers.CleanupNetwork(t, nw)
require.NoError(t, err)

// Start containers on network
db, err := postgres.Run(ctx, "postgres:16-alpine",
    network.WithNetwork([]string{"database"}, nw))
testcontainers.CleanupContainer(t, db)

app, err := testcontainers.Run(ctx, "myapp:latest",
    network.WithNetwork([]string{"app"}, nw))
testcontainers.CleanupContainer(t, app)
```

## Tips and Best Practices

1. **Always register cleanup before checking errors**
   ```go
   ctr, err := testcontainers.Run(ctx, "image")
   testcontainers.CleanupContainer(t, ctr)  // Call this first!
   require.NoError(t, err)                   // Then check error
   ```

2. **Use pre-configured modules when available**
   - Modules provide sensible defaults
   - Helper methods like `ConnectionString()`
   - Automatic credential management

3. **Use snapshots for test isolation**
   - Much faster than restarting containers
   - Perfect for test suites with shared setup

4. **Use custom networks for multi-container tests**
   - Containers can communicate via aliases
   - More realistic than host networking

5. **Use appropriate wait strategies**
   - `ForListeningPort` - when service listens on a port
   - `ForLog` - when service logs a ready message
   - `ForHTTP` - when service has an HTTP health endpoint

## Troubleshooting

### Container won't start
- Check if Docker is running: `docker ps`
- Check Docker logs: add `testcontainers.WithLogConsumers(&testcontainers.StdoutLogConsumer{})`
- Increase timeout: `wait.ForListeningPort("80/tcp").WithStartupTimeout(60*time.Second)`

### Port conflicts
- Testcontainers auto-assigns random ports
- Don't manually specify host ports

### Image pull failures
- Pull manually first: `docker pull postgres:16-alpine`
- Check network connectivity
- For private registries: `docker login registry.example.com`

### Cleanup issues
- Verify Ryuk is running: `docker ps | grep ryuk`
- Check cleanup order: network cleanup after container cleanup
- Enable Ryuk logging: `export RYUK_VERBOSE=true`

## Additional Resources

- [Testcontainers for Go Documentation](https://golang.testcontainers.org/)
- [Available Modules](https://golang.testcontainers.org/modules/)
- [GitHub Repository](https://github.com/testcontainers/testcontainers-go)

## Module Dependencies

To run specific examples, you may need additional module dependencies:

```bash
# For PostgreSQL examples
go get github.com/lib/pq
go get github.com/testcontainers/testcontainers-go/modules/postgres

# For Redis examples
go get github.com/redis/go-redis/v9
go get github.com/testcontainers/testcontainers-go/modules/redis

# Note: network is part of the main testcontainers-go module, not a separate module
```
