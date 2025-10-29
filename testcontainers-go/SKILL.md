---
name: testcontainers-go
description: A comprehensive guide for using Testcontainers for Go to write reliable integration tests with Docker containers in Go projects. Supports 62+ pre-configured modules for databases, message queues, cloud services, and more.
license: Complete terms in LICENSE.txt
---

# Testcontainers for Go Integration Testing

A comprehensive guide for using Testcontainers for Go to write reliable integration tests with Docker containers in Go projects.

## Description

This skill helps you write integration tests using Testcontainers for Go, a Go library that provides lightweight, throwaway instances of common databases, message queues, web browsers, or anything that can run in a Docker container.

**Key capabilities:**
- Use 62+ pre-configured modules for common services (databases, message queues, cloud services, etc.)
- Set up and manage Docker containers in Go tests
- Configure networking, volumes, and environment variables
- Implement proper cleanup and resource management
- Debug and troubleshoot container issues

## When to Use This Skill

Use this skill when you need to:
- Write integration tests that require real services (databases, message queues, etc.)
- Test against multiple versions or configurations of dependencies
- Create reproducible test environments
- Avoid mocking external dependencies in integration tests
- Set up ephemeral test infrastructure

## Prerequisites

- **Docker or Podman** installed and running
- **Go 1.24+** (check `go.mod` for project-specific requirements)
- **Docker socket** accessible at standard locations (Docker Desktop on macOS/Windows, `/var/run/docker.sock` on Linux)

## Instructions

### 1. Installation & Setup

Add testcontainers-go to your project:

```bash
go get github.com/testcontainers/testcontainers-go
```

For pre-configured modules (recommended):

```bash
# Example: PostgreSQL module
go get github.com/testcontainers/testcontainers-go/modules/postgres

# Example: Kafka module
go get github.com/testcontainers/testcontainers-go/modules/kafka

# Example: Redis module
go get github.com/testcontainers/testcontainers-go/modules/redis
```

**Verify Docker availability:**

```go
func TestDockerAvailable(t *testing.T) {
    testcontainers.SkipIfProviderIsNotHealthy(t)
    // Test will skip if Docker is not running
}
```

---

### 2. Using Pre-Configured Modules (Recommended Approach)

**Testcontainers for Go provides 62+ pre-configured modules** that offer production-ready configurations, sensible defaults, and helper methods. **Always prefer modules over generic containers** when available.

#### Why Use Modules?

- **Sensible defaults**: Pre-configured ports, environment variables, and wait strategies
- **Connection helpers**: Built-in methods like `ConnectionString()`, `Endpoint()`
- **Specialized features**: Module-specific functionality (e.g., Postgres snapshots, Kafka topic management)
- **Automatic credentials**: Secure credential generation and management
- **Battle-tested**: Used in production by thousands of projects

#### Available Module Categories

**Databases (17 modules):**
- `postgres`, `mysql`, `mariadb`, `mongodb`, `redis`, `valkey`
- `cockroachdb`, `clickhouse`, `memcached`, `influxdb`
- `arangodb`, `cassandra`, `scylladb`, `dynamodb`
- `dolt`, `databend`, `surrealdb`

**Message Queues (6 modules):**
- `kafka`, `rabbitmq`, `nats`, `pulsar`, `redpanda`, `solace`

**Search & Vector Databases (9 modules):**
- `elasticsearch`, `opensearch`, `meilisearch`
- `weaviate`, `qdrant`, `chroma`, `milvus`, `vearch`, `pinecone`

**Cloud & Infrastructure (6 modules):**
- `gcloud`, `azure`, `azurite`, `localstack`, `dind`, `k3s`

**Services & Tools (13 modules):**
- `consul`, `etcd`, `neo4j`, `couchbase`, `vault`, `openldap`
- `artemis`, `inbucket`, `mockserver`, `nebulagraph`, `minio`
- `toxiproxy`, `aerospike`

**Development (10 modules):**
- `compose`, `registry`, `k6`, `ollama`, `grafana-lgtm`
- `dockermodelrunner`, `dockermcpgateway`, `socat`, `mssql`

#### Basic Module Usage Pattern

```go
package myapp_test

import (
    "context"
    "testing"

    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/modules/postgres"
)

func TestWithPostgres(t *testing.T) {
    ctx := context.Background()

    // Start PostgreSQL container with sensible defaults
    pgContainer, err := postgres.Run(ctx, "postgres:16-alpine")
    testcontainers.CleanupContainer(t, pgContainer)
    require.NoError(t, err)

    // Get connection string - credentials auto-generated
    connStr, err := pgContainer.ConnectionString(ctx)
    require.NoError(t, err)
    // connStr: "postgres://postgres:password@localhost:49153/postgres?sslmode=disable"

    // Use connection string with your database driver
    db, err := sql.Open("postgres", connStr)
    require.NoError(t, err)
    defer db.Close()

    // Run your tests...
}
```

#### Module Configuration with Options

Modules support three levels of customization:

**Level 1: Simple Options (via testcontainers.CustomizeRequestOption)**

```go
pgContainer, err := postgres.Run(
    ctx,
    "postgres:16-alpine",
    testcontainers.WithEnv(map[string]string{
        "POSTGRES_DB": "myapp_test",
    }),
    testcontainers.WithLabels(map[string]string{
        "env": "test",
    }),
)
```

**Level 2: Module-Specific Options**

```go
// PostgreSQL with init scripts
pgContainer, err := postgres.Run(
    ctx,
    "postgres:16-alpine",
    postgres.WithInitScripts("./testdata/init.sql"),
    postgres.WithDatabase("myapp_test"),
    postgres.WithUsername("custom_user"),
    postgres.WithPassword("custom_pass"),
)

// Redis with configuration
redisContainer, err := redis.Run(
    ctx,
    "redis:7-alpine",
    redis.WithSnapshotting(10, 1),
    redis.WithLogLevel(redis.LogLevelVerbose),
)

// Kafka with custom config
kafkaContainer, err := kafka.Run(
    ctx,
    "confluentinc/confluent-local:7.5.0",
    kafka.WithClusterID("test-cluster"),
)
```

**Level 3: Advanced Configuration with Lifecycle Hooks**

```go
// PostgreSQL with custom initialization
pgContainer, err := postgres.Run(
    ctx,
    "postgres:16-alpine",
    postgres.WithDatabase("myapp"),
    testcontainers.WithLifecycleHooks(
        testcontainers.ContainerLifecycleHooks{
            PostStarts: []testcontainers.ContainerHook{
                func(ctx context.Context, c testcontainers.Container) error {
                    // Custom initialization after container starts
                    return nil
                },
            },
        },
    ),
)
```

#### Module-Specific Helper Methods

Most modules provide convenience methods beyond `ConnectionString()`:

```go
// PostgreSQL: Snapshot & Restore for test isolation
func TestDatabaseIsolation(t *testing.T) {
    ctx := context.Background()

    pgContainer, err := postgres.Run(ctx, "postgres:16-alpine")
    testcontainers.CleanupContainer(t, pgContainer)
    require.NoError(t, err)

    connStr, _ := pgContainer.ConnectionString(ctx)
    db, _ := sql.Open("postgres", connStr)
    defer db.Close()

    // Create initial data
    db.Exec("CREATE TABLE users (id SERIAL PRIMARY KEY, name TEXT)")
    db.Exec("INSERT INTO users (name) VALUES ('Alice')")

    // Take snapshot
    err = pgContainer.Snapshot(ctx, postgres.WithSnapshotName("initial"))
    require.NoError(t, err)

    // Make changes
    db.Exec("INSERT INTO users (name) VALUES ('Bob')")

    // Restore to snapshot
    err = pgContainer.Restore(ctx, postgres.WithSnapshotName("initial"))
    require.NoError(t, err)

    // Bob is gone, only Alice remains
}

// Kafka: Get bootstrap servers
kafkaContainer, _ := kafka.Run(ctx, "confluentinc/confluent-local:7.5.0")
brokers, _ := kafkaContainer.Brokers(ctx)
```

#### Finding the Right Module

1. **Browse available modules**: https://testcontainers.com/modules/?language=go (complete, up-to-date list)
2. **Check the modules directory**: `/modules/` in the [testcontainers-go GitHub repository](https://github.com/testcontainers/testcontainers-go)
3. **Module documentation**: https://golang.testcontainers.org/modules/ (online docs for each module)
4. **Browse by category** (see lists above)
5. **Search for examples**: Each module has `examples_test.go` in its directory

**Module location pattern:**
```
github.com/testcontainers/testcontainers-go/modules/<module-name>
```

---

### 3. Using Generic Containers (Fallback)

When no pre-configured module exists, use generic containers.

**IMPORTANT: Always add a wait strategy when exposing ports** to ensure the container is ready before tests run. This is critical for reliability, especially in CI environments. Never use `time.Sleep` as a substitute - it's an anti-pattern that leads to flaky tests.

```go
func TestCustomContainer(t *testing.T) {
    ctx := context.Background()

    ctr, err := testcontainers.Run(
        ctx,
        "custom-image:latest",
        testcontainers.WithExposedPorts("8080/tcp"),
        testcontainers.WithEnv(map[string]string{
            "APP_ENV": "test",
        }),
        // CRITICAL: Always add wait strategy for exposed ports
        testcontainers.WithWaitStrategy(
            wait.ForListeningPort("8080/tcp").WithStartupTimeout(time.Second*30),
        ),
    )
    testcontainers.CleanupContainer(t, ctr)
    require.NoError(t, err)

    // Get endpoint
    endpoint, err := ctr.Endpoint(ctx, "http")
    require.NoError(t, err)
}
```

**Common generic container options:**

```go
testcontainers.Run(
    ctx,
    "image:tag",

    // Ports
    testcontainers.WithExposedPorts("80/tcp", "443/tcp"),

    // Environment
    testcontainers.WithEnv(map[string]string{
        "KEY": "value",
    }),

    // Files
    testcontainers.WithFiles(testcontainers.ContainerFile{
        Reader:            strings.NewReader("content"),
        ContainerFilePath: "/app/config.yml",
        FileMode:          0o644,
    }),

    // Volumes
    testcontainers.WithHostConfigModifier(func(hc *container.HostConfig) {
        hc.Binds = []string{"/host/path:/container/path"}
    }),

    // Wait strategies (REQUIRED when using WithExposedPorts)
    // Use wait.ForListeningPort for reliability - never use time.Sleep!
    testcontainers.WithWaitStrategy(
        wait.ForListeningPort("80/tcp"),
        // Or use other strategies: wait.ForLog(), wait.ForHTTP(), etc.
    ),

    // Commands
    testcontainers.WithAfterReadyCommand(
        testcontainers.NewRawCommand([]string{"echo", "initialized"}),
    ),

    // Labels
    testcontainers.WithLabels(map[string]string{
        "app": "myapp",
    }),
)
```

---

### 4. Writing Integration Tests

#### Test Structure Best Practices

```go
package myapp_test

import (
    "context"
    "testing"

    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/modules/postgres"
)

func TestDatabaseOperations(t *testing.T) {
    // 1. Setup: Create context
    ctx := context.Background()

    // 2. Start container
    pgContainer, err := postgres.Run(ctx, "postgres:16-alpine")

    // 3. CRITICAL: Register cleanup BEFORE error check
    testcontainers.CleanupContainer(t, pgContainer)

    // 4. Check for errors
    require.NoError(t, err)

    // 5. Get connection details
    connStr, err := pgContainer.ConnectionString(ctx)
    require.NoError(t, err)

    // 6. Connect to service
    db, err := sql.Open("postgres", connStr)
    require.NoError(t, err)
    defer db.Close()

    // 7. Run your tests
    err = db.Ping()
    require.NoError(t, err)

    // Test your application logic here...
}
```

**Critical pattern: Cleanup BEFORE error checking**

```go
// CORRECT:
ctr, err := testcontainers.Run(ctx, "nginx:alpine")
testcontainers.CleanupContainer(t, ctr)  // Register cleanup immediately
require.NoError(t, err)                   // Then check error

// WRONG: Creates resource leaks
ctr, err := testcontainers.Run(ctx, "nginx:alpine")
require.NoError(t, err)                   // If this fails...
testcontainers.CleanupContainer(t, ctr)  // ...cleanup never registers
```

#### Table-Driven Tests with Containers

```go
func TestMultipleVersions(t *testing.T) {
    ctx := context.Background()

    versions := []struct {
        name  string
        image string
    }{
        {"Postgres 14", "postgres:14-alpine"},
        {"Postgres 15", "postgres:15-alpine"},
        {"Postgres 16", "postgres:16-alpine"},
    }

    for _, tc := range versions {
        t.Run(tc.name, func(t *testing.T) {
            pgContainer, err := postgres.Run(ctx, tc.image)
            testcontainers.CleanupContainer(t, pgContainer)
            require.NoError(t, err)

            // Run tests against this version...
        })
    }
}
```

#### Parallel Test Execution

```go
func TestParallelContainers(t *testing.T) {
    t.Parallel()  // Enable parallel execution

    ctx := context.Background()

    pgContainer, err := postgres.Run(ctx, "postgres:16-alpine")
    testcontainers.CleanupContainer(t, pgContainer)
    require.NoError(t, err)

    // Each parallel test gets its own container
}
```

---

### 5. Container Networking

#### Connecting Multiple Containers

```go
import "github.com/testcontainers/testcontainers-go/network"

func TestMultipleServices(t *testing.T) {
    ctx := context.Background()

    // Create custom network
    nw, err := network.New(ctx)
    testcontainers.CleanupNetwork(t, nw)
    require.NoError(t, err)

    // Start database on network
    pgContainer, err := postgres.Run(
        ctx,
        "postgres:16-alpine",
        network.WithNetwork([]string{"database"}, nw),
    )
    testcontainers.CleanupContainer(t, pgContainer)
    require.NoError(t, err)

    // Start application on same network
    appContainer, err := testcontainers.Run(
        ctx,
        "myapp:latest",
        testcontainers.WithEnv(map[string]string{
            "DB_HOST": "database",  // Can reach via network alias
            "DB_PORT": "5432",      // Use internal port, not mapped port
        }),
        network.WithNetwork([]string{"app"}, nw),
    )
    testcontainers.CleanupContainer(t, appContainer)
    require.NoError(t, err)

    // Test application can communicate with database...
}
```

#### Accessing Container Ports

```go
func TestPortAccess(t *testing.T) {
    ctx := context.Background()

    ctr, err := testcontainers.Run(
        ctx,
        "nginx:alpine",
        testcontainers.WithExposedPorts("80/tcp"),
    )
    testcontainers.CleanupContainer(t, ctr)
    require.NoError(t, err)

    // Method 1: Get full endpoint (recommended)
    endpoint, err := ctr.Endpoint(ctx, "http")
    require.NoError(t, err)
    // endpoint = "http://localhost:49153"

    // Method 2: Get mapped port only
    port, err := ctr.MappedPort(ctx, "80/tcp")
    require.NoError(t, err)
    portNum := port.Int()  // e.g., 49153

    // Method 3: Get host and port separately
    host, err := ctr.Host(ctx)
    require.NoError(t, err)
    // host = "localhost" (or docker host IP)
}
```

---

### 6. Resource Management & Cleanup

#### Cleanup Methods

**Method 1: `testcontainers.CleanupContainer()` (Recommended)**

```go
func TestRecommendedCleanup(t *testing.T) {
    ctx := context.Background()

    ctr, err := testcontainers.Run(ctx, "nginx:alpine")
    testcontainers.CleanupContainer(t, ctr)  // Registers with t.Cleanup
    require.NoError(t, err)

    // Container automatically cleaned up when test ends
}
```

**Method 2: `t.Cleanup()` (Manual)**

```go
func TestManualCleanup(t *testing.T) {
    ctx := context.Background()

    ctr, err := testcontainers.Run(ctx, "nginx:alpine")
    require.NoError(t, err)

    t.Cleanup(func() {
        err := testcontainers.TerminateContainer(ctr)
        require.NoError(t, err)
    })
}
```

**Method 3: `defer` (Legacy)**

```go
func TestDeferCleanup(t *testing.T) {
    ctx := context.Background()

    ctr, err := testcontainers.Run(ctx, "nginx:alpine")
    require.NoError(t, err)

    defer func() {
        err := testcontainers.TerminateContainer(ctr)
        require.NoError(t, err)
    }()
}
```

#### Cleanup Options

```go
// Cleanup with custom timeout
testcontainers.CleanupContainer(t, ctr,
    testcontainers.StopTimeout(10*time.Second),
)

// Cleanup and remove volumes
testcontainers.CleanupContainer(t, ctr,
    testcontainers.RemoveVolumes("volume1", "volume2"),
)

// Combine options
testcontainers.CleanupContainer(t, ctr,
    testcontainers.StopTimeout(5*time.Second),
    testcontainers.RemoveVolumes("data"),
)
```

#### Automatic Cleanup with Ryuk

Testcontainers for Go uses **Ryuk**, a garbage collector that automatically cleans up containers even if tests crash or timeout:

- Runs as a sidecar container (`testcontainers/ryuk:0.13.0`)
- Monitors test session lifecycle
- Cleans up containers when session ends
- Handles parallel test execution

**Control Ryuk behavior:**

```go
// Disable Ryuk (not recommended)
os.Setenv("TESTCONTAINERS_RYUK_DISABLED", "true")

// Enable verbose logging
os.Setenv("RYUK_VERBOSE", "true")

// Adjust timeouts
os.Setenv("RYUK_CONNECTION_TIMEOUT", "2m")
os.Setenv("RYUK_RECONNECTION_TIMEOUT", "30s")
```

---

### 7. Configuration Patterns

#### Environment Variables

```go
testcontainers.Run(
    ctx,
    "myapp:latest",
    testcontainers.WithEnv(map[string]string{
        "DATABASE_URL": "postgres://localhost/db",
        "LOG_LEVEL":    "debug",
        "API_KEY":      "test-key",
    }),
)
```

#### Executing Commands in Containers

When executing commands with `Exec()`, it's recommended to use `exec.Multiplexed()` to properly handle Docker's output format:

```go
import "github.com/testcontainers/testcontainers-go/exec"

// Execute command with Multiplexed option
exitCode, reader, err := ctr.Exec(ctx, []string{"sh", "-c", "echo 'hello'"}, exec.Multiplexed())
require.NoError(t, err)
require.Equal(t, 0, exitCode)

// Read the output
output, err := io.ReadAll(reader)
require.NoError(t, err)
fmt.Println(string(output))
```

**Why use `exec.Multiplexed()`?**
- Removes Docker's multiplexing headers from the output
- Combines stdout and stderr into a single clean stream
- Makes the output easier to read and parse

Without `exec.Multiplexed()`, you'll get Docker's raw multiplexed stream which includes header bytes that are difficult to parse.

#### Files and Directories

```go
// Copy single file
testcontainers.Run(
    ctx,
    "nginx:alpine",
    testcontainers.WithFiles(testcontainers.ContainerFile{
        Reader:            strings.NewReader("server { listen 80; }"),
        ContainerFilePath: "/etc/nginx/conf.d/default.conf",
        FileMode:          0o644,
    }),
)

// Copy multiple files
testcontainers.Run(
    ctx,
    "myapp:latest",
    testcontainers.WithFiles(
        testcontainers.ContainerFile{...},  // config.yml
        testcontainers.ContainerFile{...},  // secrets.json
    ),
)

// Copy from container after start
ctr, _ := testcontainers.Run(ctx, "nginx:alpine")
reader, err := ctr.CopyFileFromContainer(ctx, "/etc/nginx/nginx.conf")
content, _ := io.ReadAll(reader)
```

#### Volume Mounts

```go
testcontainers.Run(
    ctx,
    "postgres:16",
    testcontainers.WithHostConfigModifier(func(hc *container.HostConfig) {
        // Bind mount
        hc.Binds = []string{
            "/host/data:/var/lib/postgresql/data",
        }

        // Named volume
        hc.Mounts = []mount.Mount{
            {
                Type:   mount.TypeVolume,
                Source: "pgdata",
                Target: "/var/lib/postgresql/data",
            },
        }
    }),
)
```

#### Temporary Filesystems

```go
testcontainers.Run(
    ctx,
    "myapp:latest",
    testcontainers.WithTmpfs(map[string]string{
        "/tmp":      "rw",
        "/app/temp": "rw,size=100m,mode=1777",
    }),
)
```

---

### 8. Wait Strategies

**Wait strategies are critical for reliable tests.** They ensure containers are fully ready before tests run, which is especially important in CI environments where timing can vary.

**Best Practices:**
- ✅ **Always use `wait.ForListeningPort()` when exposing ports** - This is the most reliable approach
- ✅ **Choose appropriate wait strategies** based on your service (HTTP health checks, log patterns, etc.)
- ❌ **Never use `time.Sleep()`** - This is an anti-pattern that leads to flaky tests
- ✅ **Set reasonable timeouts** to handle slow CI environments

#### Port-Based Waiting (Recommended for Exposed Ports)

```go
import "github.com/testcontainers/testcontainers-go/wait"

testcontainers.Run(
    ctx,
    "postgres:16",
    testcontainers.WithWaitStrategy(
        wait.ForListeningPort("5432/tcp").
            WithStartupTimeout(30*time.Second).
            WithPollInterval(1*time.Second),
    ),
)
```

#### Log-Based Waiting

```go
testcontainers.Run(
    ctx,
    "elasticsearch:8.7.0",
    testcontainers.WithWaitStrategy(
        wait.ForLog("started").
            WithStartupTimeout(60*time.Second).
            WithOccurrence(1),
    ),
)
```

#### HTTP-Based Waiting

```go
testcontainers.Run(
    ctx,
    "myapp:latest",
    testcontainers.WithWaitStrategy(
        wait.ForHTTP("/health").
            WithPort("8080/tcp").
            WithStatusCodeMatcher(func(status int) bool {
                return status == 200
            }).
            WithStartupTimeout(30*time.Second),
    ),
)
```

#### SQL-Based Waiting

```go
testcontainers.Run(
    ctx,
    "postgres:16",
    testcontainers.WithWaitStrategy(
        wait.ForSQL("5432/tcp", "postgres", func(host string, port nat.Port) string {
            return fmt.Sprintf("postgres://user:pass@%s:%s/db?sslmode=disable",
                host, port.Port())
        }).WithStartupTimeout(30*time.Second),
    ),
)
```

#### Multiple Wait Strategies

```go
testcontainers.Run(
    ctx,
    "myapp:latest",
    testcontainers.WithWaitStrategy(
        wait.ForAll(
            wait.ForListeningPort("8080/tcp"),
            wait.ForLog("Application started"),
            wait.ForHTTP("/health"),
        ),
    ),
)
```

---

### 9. Troubleshooting

#### Check Docker Availability

```go
func TestDockerConnection(t *testing.T) {
    testcontainers.SkipIfProviderIsNotHealthy(t)

    ctx := context.Background()
    cli, err := testcontainers.NewDockerClientWithOpts(ctx)
    require.NoError(t, err)

    info, err := cli.Info(ctx)
    require.NoError(t, err)

    t.Logf("Docker version: %s", info.ServerVersion)
    t.Logf("OS: %s", info.OperatingSystem)
}
```

#### Debug Container Logs

```go
func TestWithLogging(t *testing.T) {
    ctx := context.Background()

    // Method 1: Stream to stdout
    ctr, _ := testcontainers.Run(
        ctx,
        "myapp:latest",
        testcontainers.WithLogConsumers(
            &testcontainers.StdoutLogConsumer{},
        ),
    )
    testcontainers.CleanupContainer(t, ctr)

    // Method 2: Read logs manually
    rc, _ := ctr.Logs(ctx)
    defer rc.Close()
    logs, _ := io.ReadAll(rc)
    t.Logf("Container logs:\n%s", string(logs))

    // Method 3: Inspect container
    info, _ := ctr.Inspect(ctx)
    t.Logf("Container state: %+v", info.State)
}
```

#### Common Issues

**Issue: Container startup timeout**
```go
// Increase wait timeout
testcontainers.WithWaitStrategy(
    wait.ForListeningPort("5432/tcp").
        WithStartupTimeout(60*time.Second),  // Increase from default
)

// Check logs to see what's happening
testcontainers.WithLogConsumers(&testcontainers.StdoutLogConsumer{})
```

**Issue: Port already in use**
- Testcontainers auto-assigns random ports
- Don't manually specify host ports unless necessary
- Check for leaked containers: `docker ps -a`

**Issue: Image pull failures**
```bash
# Pull manually first to verify
docker pull postgres:16

# For private registries, login first
docker login registry.example.com
# Testcontainers will use credentials from ~/.docker/config.json
```

**Issue: Container not cleaning up**
```go
// Verify Ryuk is running
docker ps | grep ryuk

// Check cleanup is registered correctly
testcontainers.CleanupContainer(t, ctr)  // Before error check!
```

#### Environment Variables for Debugging

```bash
# Enable Ryuk verbose logging
export RYUK_VERBOSE=true

# Adjust timeouts
export RYUK_CONNECTION_TIMEOUT=2m
export RYUK_RECONNECTION_TIMEOUT=30s

# Custom Docker socket
export DOCKER_HOST=unix:///var/run/docker.sock

# Registry prefix for private registry
export TESTCONTAINERS_HUB_IMAGE_NAME_PREFIX=private.registry.com
```

---

## Examples

### Example 1: PostgreSQL Integration Test

```go
package myapp_test

import (
    "context"
    "database/sql"
    "testing"

    _ "github.com/lib/pq"
    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/modules/postgres"
)

func TestUserRepository(t *testing.T) {
    ctx := context.Background()

    // Start PostgreSQL container
    pgContainer, err := postgres.Run(
        ctx,
        "postgres:16-alpine",
        postgres.WithDatabase("testdb"),
        postgres.WithUsername("testuser"),
        postgres.WithPassword("testpass"),
        postgres.WithInitScripts("./testdata/schema.sql"),
    )
    testcontainers.CleanupContainer(t, pgContainer)
    require.NoError(t, err)

    // Get connection string
    connStr, err := pgContainer.ConnectionString(ctx, "sslmode=disable")
    require.NoError(t, err)

    // Connect to database
    db, err := sql.Open("postgres", connStr)
    require.NoError(t, err)
    defer db.Close()

    // Test your repository
    repo := NewUserRepository(db)

    t.Run("CreateUser", func(t *testing.T) {
        user := &User{Name: "Alice", Email: "alice@example.com"}
        err := repo.Create(user)
        require.NoError(t, err)
        require.NotZero(t, user.ID)
    })

    t.Run("GetUser", func(t *testing.T) {
        user, err := repo.GetByEmail("alice@example.com")
        require.NoError(t, err)
        require.Equal(t, "Alice", user.Name)
    })
}
```

### Example 2: Redis Cache Test

```go
package cache_test

import (
    "context"
    "testing"
    "time"

    "github.com/redis/go-redis/v9"
    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/modules/redis"
)

func TestRedisCache(t *testing.T) {
    ctx := context.Background()

    // Start Redis container
    redisContainer, err := redis.Run(
        ctx,
        "redis:7-alpine",
        redis.WithSnapshotting(10, 1),
        redis.WithLogLevel(redis.LogLevelVerbose),
    )
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

    // Test cache operations
    t.Run("SetAndGet", func(t *testing.T) {
        err := client.Set(ctx, "key1", "value1", time.Minute).Err()
        require.NoError(t, err)

        val, err := client.Get(ctx, "key1").Result()
        require.NoError(t, err)
        require.Equal(t, "value1", val)
    })

    t.Run("Expiration", func(t *testing.T) {
        err := client.Set(ctx, "key2", "value2", time.Second).Err()
        require.NoError(t, err)

        time.Sleep(2 * time.Second)

        _, err = client.Get(ctx, "key2").Result()
        require.Equal(t, redis.Nil, err)
    })
}
```

### Example 3: Kafka Producer/Consumer Test

```go
package messaging_test

import (
    "context"
    "testing"
    "time"

    "github.com/segmentio/kafka-go"
    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/modules/kafka"
)

func TestKafkaMessaging(t *testing.T) {
    ctx := context.Background()

    // Start Kafka container
    kafkaContainer, err := kafka.Run(
        ctx,
        "confluentinc/confluent-local:7.5.0",
        kafka.WithClusterID("test-cluster"),
    )
    testcontainers.CleanupContainer(t, kafkaContainer)
    require.NoError(t, err)

    // Get bootstrap servers
    brokers, err := kafkaContainer.Brokers(ctx)
    require.NoError(t, err)

    topic := "test-topic"

    // Create producer
    writer := kafka.NewWriter(kafka.WriterConfig{
        Brokers: brokers,
        Topic:   topic,
    })
    defer writer.Close()

    // Create consumer
    reader := kafka.NewReader(kafka.ReaderConfig{
        Brokers: brokers,
        Topic:   topic,
        GroupID: "test-group",
    })
    defer reader.Close()

    // Test message flow
    t.Run("ProduceAndConsume", func(t *testing.T) {
        // Produce message
        err := writer.WriteMessages(ctx, kafka.Message{
            Key:   []byte("key1"),
            Value: []byte("Hello, Kafka!"),
        })
        require.NoError(t, err)

        // Consume message
        msg, err := reader.ReadMessage(ctx)
        require.NoError(t, err)
        require.Equal(t, "Hello, Kafka!", string(msg.Value))
    })
}
```

### Example 4: Multi-Container Application Stack

```go
package integration_test

import (
    "context"
    "net/http"
    "testing"

    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/modules/postgres"
    "github.com/testcontainers/testcontainers-go/modules/redis"
    "github.com/testcontainers/testcontainers-go/network"
)

func TestFullStack(t *testing.T) {
    ctx := context.Background()

    // Create custom network
    nw, err := network.New(ctx)
    testcontainers.CleanupNetwork(t, nw)
    require.NoError(t, err)

    // Start PostgreSQL
    pgContainer, err := postgres.Run(
        ctx,
        "postgres:16-alpine",
        network.WithNetwork([]string{"database"}, nw),
    )
    testcontainers.CleanupContainer(t, pgContainer)
    require.NoError(t, err)

    // Start Redis
    redisContainer, err := redis.Run(
        ctx,
        "redis:7-alpine",
        network.WithNetwork([]string{"cache"}, nw),
    )
    testcontainers.CleanupContainer(t, redisContainer)
    require.NoError(t, err)

    // Start application
    appContainer, err := testcontainers.Run(
        ctx,
        "myapp:latest",
        testcontainers.WithEnv(map[string]string{
            "DB_HOST":    "database",
            "DB_PORT":    "5432",
            "REDIS_HOST": "cache",
            "REDIS_PORT": "6379",
        }),
        testcontainers.WithExposedPorts("8080/tcp"),
        network.WithNetwork([]string{"app"}, nw),
    )
    testcontainers.CleanupContainer(t, appContainer)
    require.NoError(t, err)

    // Get application endpoint
    endpoint, err := appContainer.Endpoint(ctx, "http")
    require.NoError(t, err)

    // Test application
    resp, err := http.Get(endpoint + "/health")
    require.NoError(t, err)
    require.Equal(t, 200, resp.StatusCode)
}
```

### Example 5: Docker Compose Stack

```go
package compose_test

import (
    "context"
    "testing"

    "github.com/stretchr/testify/require"
    "github.com/testcontainers/testcontainers-go"
    "github.com/testcontainers/testcontainers-go/modules/compose"
)

func TestComposeStack(t *testing.T) {
    ctx := context.Background()

    // Start services from docker-compose.yml
    composeStack, err := compose.NewDockerCompose("./docker-compose.yml")
    require.NoError(t, err)

    t.Cleanup(func() {
        if err := composeStack.Down(ctx); err != nil {
            t.Fatalf("failed to down compose stack: %v", err)
        }
    })

    err = composeStack.Up(ctx, compose.Wait(true))
    require.NoError(t, err)

    // Get service container
    webContainer, err := composeStack.ServiceContainer(ctx, "web")
    require.NoError(t, err)

    // Test service
    endpoint, err := webContainer.Endpoint(ctx, "http")
    require.NoError(t, err)

    // Run tests against the stack...
}
```

---

## Best Practices

1. **Always use pre-configured modules when available** - They provide sensible defaults and helper methods
2. **Register cleanup immediately** - Call `testcontainers.CleanupContainer(t, ctr)` before checking errors
3. **Always add wait strategies when exposing ports** - Use `wait.ForListeningPort()` to ensure reliability, especially in CI. Never use `time.Sleep()` - it's an anti-pattern that causes flaky tests
4. **Choose appropriate wait strategies** - Use `wait.ForHTTP()` for health endpoints, `wait.ForLog()` for log patterns, or `wait.ForListeningPort()` for port availability
5. **Leverage table-driven tests** - Test against multiple versions or configurations
6. **Use custom networks** - For multi-container communication
7. **Keep containers ephemeral** - Don't rely on state between tests
8. **Check Docker availability** - Use `testcontainers.SkipIfProviderIsNotHealthy(t)`
9. **Enable parallel execution** - Use `t.Parallel()` for faster test suites
10. **Use module helper methods** - E.g., `ConnectionString()`, `Snapshot()`, `Restore()`
11. **Debug with logs** - Use `WithLogConsumers()` when troubleshooting

---

## Additional Resources

- **Official Documentation**: https://golang.testcontainers.org/
- **Available Modules**: https://testcontainers.com/modules/?language=go (complete, up-to-date list)
- **Module Documentation**: https://golang.testcontainers.org/modules/ (online docs for each module)
- **GitHub Repository**: https://github.com/testcontainers/testcontainers-go
- **Module Examples**: Check `modules/*/examples_test.go` files in the GitHub repository
- **Community Slack**: [testcontainers.slack.com](https://testcontainers.slack.com)
