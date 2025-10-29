package examples_test

import (
	"context"
	"fmt"
	"io"
	"net/http"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"github.com/testcontainers/testcontainers-go"
	"github.com/testcontainers/testcontainers-go/exec"
	"github.com/testcontainers/testcontainers-go/wait"
)

// TestGenericNginx demonstrates using a generic container with nginx
func TestGenericNginx(t *testing.T) {
	ctx := context.Background()

	// Start nginx container
	nginxContainer, err := testcontainers.Run(
		ctx,
		"nginx:alpine",
		testcontainers.WithExposedPorts("80/tcp"),
		testcontainers.WithWaitStrategy(
			wait.ForListeningPort("80/tcp").WithStartupTimeout(30*time.Second),
		),
	)
	testcontainers.CleanupContainer(t, nginxContainer)
	require.NoError(t, err)

	// Get endpoint
	endpoint, err := nginxContainer.Endpoint(ctx, "http")
	require.NoError(t, err)

	// Test the nginx default page
	resp, err := http.Get(endpoint)
	require.NoError(t, err)
	defer resp.Body.Close()

	require.Equal(t, http.StatusOK, resp.StatusCode)

	body, err := io.ReadAll(resp.Body)
	require.NoError(t, err)
	require.Contains(t, string(body), "Welcome to nginx")

	t.Log("Successfully accessed nginx container")
}

// TestGenericContainerWithCustomHTML demonstrates serving custom content with nginx
func TestGenericContainerWithCustomHTML(t *testing.T) {
	ctx := context.Background()

	customHTML := `<!DOCTYPE html>
<html>
<head><title>Test Page</title></head>
<body><h1>Hello from Testcontainers!</h1></body>
</html>`

	// Start nginx with custom HTML
	nginxContainer, err := testcontainers.Run(
		ctx,
		"nginx:alpine",
		testcontainers.WithExposedPorts("80/tcp"),
		testcontainers.WithFiles(testcontainers.ContainerFile{
			Reader:            strings.NewReader(customHTML),
			ContainerFilePath: "/usr/share/nginx/html/index.html",
			FileMode:          0o644,
		}),
		testcontainers.WithWaitStrategy(
			wait.ForListeningPort("80/tcp"),
		),
	)
	testcontainers.CleanupContainer(t, nginxContainer)
	require.NoError(t, err)

	endpoint, err := nginxContainer.Endpoint(ctx, "http")
	require.NoError(t, err)

	resp, err := http.Get(endpoint)
	require.NoError(t, err)
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	require.NoError(t, err)
	require.Contains(t, string(body), "Hello from Testcontainers!")

	t.Log("Successfully served custom HTML from nginx")
}

// TestGenericContainerWithEnv demonstrates using environment variables
func TestGenericContainerWithEnv(t *testing.T) {
	ctx := context.Background()

	// Start alpine container that echoes an environment variable
	alpineContainer, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithEnv(map[string]string{
			"MY_VAR":      "test_value",
			"ANOTHER_VAR": "another_value",
		}),
		testcontainers.WithCmd("sleep", "300"),
	)
	testcontainers.CleanupContainer(t, alpineContainer)
	require.NoError(t, err)

	// Execute command to read environment variable
	exitCode, reader, err := alpineContainer.Exec(ctx, []string{"sh", "-c", "echo $MY_VAR"}, exec.Multiplexed())
	require.NoError(t, err)
	require.Equal(t, 0, exitCode)

	output, err := io.ReadAll(reader)
	require.NoError(t, err)
	require.Contains(t, string(output), "test_value")

	t.Log("Successfully used environment variables in container")
}

// TestGenericContainerWithCommand demonstrates running a custom command
func TestGenericContainerWithCommand(t *testing.T) {
	ctx := context.Background()

	// Start alpine with a custom command that creates a file
	alpineContainer, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithCmd("sh", "-c", "echo 'Hello' > /tmp/hello.txt && sleep 300"),
	)
	testcontainers.CleanupContainer(t, alpineContainer)
	require.NoError(t, err)

	// Give it a moment to create the file
	time.Sleep(1 * time.Second)

	// Read the file we created
	exitCode, reader, err := alpineContainer.Exec(ctx, []string{"cat", "/tmp/hello.txt"}, exec.Multiplexed())
	require.NoError(t, err)
	require.Equal(t, 0, exitCode)

	output, err := io.ReadAll(reader)
	require.NoError(t, err)
	require.Contains(t, string(output), "Hello")

	t.Log("Successfully ran custom command in container")
}

// TestGenericContainerWithLabels demonstrates using labels
func TestGenericContainerWithLabels(t *testing.T) {
	ctx := context.Background()

	alpineContainer, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithLabels(map[string]string{
			"app":         "testapp",
			"environment": "test",
			"version":     "1.0",
		}),
		testcontainers.WithCmd("sleep", "300"),
	)
	testcontainers.CleanupContainer(t, alpineContainer)
	require.NoError(t, err)

	// Inspect container to verify labels
	inspect, err := alpineContainer.Inspect(ctx)
	require.NoError(t, err)

	require.Equal(t, "testapp", inspect.Config.Labels["app"])
	require.Equal(t, "test", inspect.Config.Labels["environment"])
	require.Equal(t, "1.0", inspect.Config.Labels["version"])

	t.Log("Successfully set and verified container labels")
}

// TestGenericContainerWithTmpfs demonstrates using temporary filesystems
func TestGenericContainerWithTmpfs(t *testing.T) {
	ctx := context.Background()

	alpineContainer, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithTmpfs(map[string]string{
			"/tmp": "rw,size=100m",
		}),
		testcontainers.WithCmd("sleep", "300"),
	)
	testcontainers.CleanupContainer(t, alpineContainer)
	require.NoError(t, err)

	// Verify tmpfs is mounted
	exitCode, reader, err := alpineContainer.Exec(ctx, []string{"mount"}, exec.Multiplexed())
	require.NoError(t, err)
	require.Equal(t, 0, exitCode)

	output, err := io.ReadAll(reader)
	require.NoError(t, err)
	require.Contains(t, string(output), "tmpfs on /tmp")

	t.Log("Successfully mounted tmpfs in container")
}

// TestGenericContainerLogs demonstrates accessing container logs
func TestGenericContainerLogs(t *testing.T) {
	ctx := context.Background()

	// Start container that produces logs
	alpineContainer, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithCmd("sh", "-c", "echo 'Starting...'; sleep 1; echo 'Running...'; sleep 300"),
	)
	testcontainers.CleanupContainer(t, alpineContainer)
	require.NoError(t, err)

	// Wait a moment for logs to be written
	time.Sleep(2 * time.Second)

	// Read logs
	logs, err := alpineContainer.Logs(ctx)
	require.NoError(t, err)
	defer logs.Close()

	logContent, err := io.ReadAll(logs)
	require.NoError(t, err)

	logStr := string(logContent)
	require.Contains(t, logStr, "Starting...")
	require.Contains(t, logStr, "Running...")

	t.Log("Successfully read container logs")
}

// TestGenericContainerExec demonstrates executing commands in a running container
func TestGenericContainerExec(t *testing.T) {
	ctx := context.Background()

	alpineContainer, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithCmd("sleep", "300"),
	)
	testcontainers.CleanupContainer(t, alpineContainer)
	require.NoError(t, err)

	// Execute multiple commands
	tests := []struct {
		name     string
		cmd      []string
		expected string
	}{
		{
			name:     "echo",
			cmd:      []string{"echo", "hello world"},
			expected: "hello world",
		},
		{
			name:     "pwd",
			cmd:      []string{"pwd"},
			expected: "/",
		},
		{
			name:     "uname",
			cmd:      []string{"uname", "-s"},
			expected: "Linux",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			exitCode, reader, err := alpineContainer.Exec(ctx, tt.cmd, exec.Multiplexed())
			require.NoError(t, err)
			require.Equal(t, 0, exitCode)

			output, err := io.ReadAll(reader)
			require.NoError(t, err)
			require.Contains(t, string(output), tt.expected)
		})
	}

	t.Log("Successfully executed multiple commands")
}

// TestGenericContainerHTTPWait demonstrates waiting for an HTTP endpoint
func TestGenericContainerHTTPWait(t *testing.T) {
	ctx := context.Background()

	nginxContainer, err := testcontainers.Run(
		ctx,
		"nginx:alpine",
		testcontainers.WithExposedPorts("80/tcp"),
		testcontainers.WithWaitStrategy(
			wait.ForListeningPort("80/tcp"),
			wait.ForHTTP("/").
				WithPort("80/tcp").
				WithStatusCodeMatcher(func(status int) bool {
					return status == http.StatusOK
				}).
				WithStartupTimeout(30*time.Second),
		),
	)
	testcontainers.CleanupContainer(t, nginxContainer)
	require.NoError(t, err)

	endpoint, err := nginxContainer.Endpoint(ctx, "http")
	require.NoError(t, err)

	// Container is already ready because wait strategy succeeded
	resp, err := http.Get(endpoint)
	require.NoError(t, err)
	defer resp.Body.Close()

	require.Equal(t, http.StatusOK, resp.StatusCode)

	t.Log("HTTP wait strategy worked correctly")
}

// TestGenericContainerLogWait demonstrates waiting for a log message
func TestGenericContainerLogWait(t *testing.T) {
	ctx := context.Background()

	alpineContainer, err := testcontainers.Run(
		ctx,
		"alpine:latest",
		testcontainers.WithCmd(
			"sh", "-c",
			"echo 'Initializing...'; sleep 2; echo 'Ready!'; sleep 300",
		),
		testcontainers.WithWaitStrategy(
			wait.ForLog("Ready!").WithStartupTimeout(10*time.Second),
		),
	)
	testcontainers.CleanupContainer(t, alpineContainer)
	require.NoError(t, err)

	// If we got here, the "Ready!" message was logged
	t.Log("Container became ready after logging expected message")
}

// TestGenericContainerPortInfo demonstrates getting port information
func TestGenericContainerPortInfo(t *testing.T) {
	ctx := context.Background()

	nginxContainer, err := testcontainers.Run(
		ctx,
		"nginx:alpine",
		testcontainers.WithExposedPorts("80/tcp", "443/tcp"),
		testcontainers.WithWaitStrategy(wait.ForListeningPort("80/tcp")),
	)
	testcontainers.CleanupContainer(t, nginxContainer)
	require.NoError(t, err)

	// Method 1: Get mapped port
	port80, err := nginxContainer.MappedPort(ctx, "80/tcp")
	require.NoError(t, err)
	t.Logf("Port 80 is mapped to: %s", port80.Port())

	// Method 2: Get host
	host, err := nginxContainer.Host(ctx)
	require.NoError(t, err)
	t.Logf("Container host: %s", host)

	// Method 3: Get endpoint
	endpoint, err := nginxContainer.Endpoint(ctx, "http")
	require.NoError(t, err)
	t.Logf("HTTP endpoint: %s", endpoint)

	// Method 4: Get all ports
	ports, err := nginxContainer.Ports(ctx)
	require.NoError(t, err)
	t.Logf("All ports: %v", ports)

	// Verify we can access port 80
	resp, err := http.Get(fmt.Sprintf("http://%s:%s", host, port80.Port()))
	require.NoError(t, err)
	defer resp.Body.Close()
	require.Equal(t, http.StatusOK, resp.StatusCode)

	t.Log("Successfully retrieved and used port information")
}
