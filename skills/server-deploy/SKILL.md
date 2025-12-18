---
name: server-deploy
description: Server deployment and infrastructure management toolkit for managing services, Caddy reverse proxy, and system health. Use when (1) starting/stopping services, (2) configuring Caddy routes, (3) checking system health, (4) managing ports, or (5) deploying new services.
license: MIT
---

# Server Deploy Skill

Toolkit for managing server infrastructure, services, and deployment.

## Helper Scripts Available

- `scripts/service.py` - Manage services (start, stop, status, logs)
- `scripts/caddy.py` - Caddy reverse proxy configuration
- `scripts/health.py` - System and service health checks
- `scripts/ports.py` - Port allocation and availability

**Always run scripts with `--help` first** to see usage.

## Service Management

### Quick Commands
```bash
# Check all services
python scripts/service.py status

# Start a service
python scripts/service.py start mcp-orchestrator

# Stop a service
python scripts/service.py stop mcp-orchestrator

# Restart a service
python scripts/service.py restart mcp-orchestrator

# View logs
python scripts/service.py logs mcp-orchestrator --lines 100
```

### Available Services

| Service | Port | Description |
|---------|------|-------------|
| mcp-orchestrator | 5060 | MCP server for AI orchestration |
| dreamwalker | 5080 | Orchestrator web UI |
| storyblocks | 8000 | Multi-provider LLM proxy |
| studio | 5413 | AI interaction interface |
| clinical | 1266 | Clinical reference tool |
| lessonplanner | 4108 | EFL lesson generator |
| wordblocks | 8847 | AAC communication app |
| luke | 5211 | Portfolio (Vite + Express) |
| coca | 3034 | Corpus linguistics API |
| dashboard | 9999 | System monitoring |

### Service Operations
```bash
# Start all services
python scripts/service.py start --all

# Stop all services
python scripts/service.py stop --all

# Show service details
python scripts/service.py info mcp-orchestrator

# Enable monitoring (auto-restart failed services)
python scripts/service.py monitor --start

# Check monitor status
python scripts/service.py monitor --status
```

## Caddy Configuration

### Route Management
```bash
# List current routes
python scripts/caddy.py routes

# Add new route
python scripts/caddy.py add /api/myservice/* localhost:5015

# Remove route
python scripts/caddy.py remove /api/myservice/*

# Validate configuration
python scripts/caddy.py validate

# Reload Caddy
python scripts/caddy.py reload
```

### Route Patterns

**handle_path** (strips prefix):
```
/api/myservice/* → localhost:5015
# Flask receives: /endpoint (prefix stripped)
```

**handle** (keeps prefix):
```
/myservice/* → localhost:5015
# Flask receives: /myservice/endpoint (prefix kept)
```

### Configuration Example
```bash
# Add API route that strips prefix
python scripts/caddy.py add /api/search/* localhost:5015 --strip-prefix

# Add static file route
python scripts/caddy.py add /static/* /var/www/static --file-server

# Add with custom headers
python scripts/caddy.py add /api/* localhost:5000 \
  --header "X-Custom: value"
```

## Port Management

### Check Availability
```bash
# Find available port in range
python scripts/ports.py find --range 5010-5019

# Check specific port
python scripts/ports.py check 5015

# List all used ports
python scripts/ports.py list --used

# Show port allocation map
python scripts/ports.py map
```

### Reserved Ranges

| Range | Purpose |
|-------|---------|
| 5010-5019 | Available for testing |
| 5050-5059 | Available for testing |
| 1000-4999 | Production services |
| 8000-9999 | Web services |

## Health Checks

### System Health
```bash
# Full system check
python scripts/health.py system

# Check specific components
python scripts/health.py --cpu --memory --disk

# Check service health
python scripts/health.py services

# Check Caddy routes
python scripts/health.py caddy
```

### Health Report
```bash
# Generate comprehensive report
python scripts/health.py report --output health_report.md

# Output includes:
# - System resources (CPU, memory, disk)
# - Service status (all registered services)
# - Caddy route validation
# - Port conflicts
# - Recent errors from logs
```

## Deployment Workflow

### Deploy New Service

```bash
# 1. Find available port
python scripts/ports.py find --range 5010-5019
# Output: Port 5015 is available

# 2. Start service
python scripts/service.py start myservice --port 5015

# 3. Add Caddy route
python scripts/caddy.py add /api/myservice/* localhost:5015 --strip-prefix

# 4. Validate and reload
python scripts/caddy.py validate && python scripts/caddy.py reload

# 5. Verify health
python scripts/health.py service myservice
```

### Deployment Checklist
```bash
# Run full deployment check
python scripts/health.py deploy-check myservice

# Checks:
# ✓ Port is available
# ✓ Service can start
# ✓ Health endpoint responds
# ✓ Caddy route is valid
# ✓ No port conflicts
```

## Configuration

### Environment Variables
```bash
# Caddy config location
CADDY_CONFIG=/etc/caddy/Caddyfile

# Service manager config
SERVICE_MANAGER_DIR=~/.service_manager

# Sudo password (for Caddy operations)
SUDO_PASSWORD=...
```

### Service Registration

Register new service in service manager:
```python
# In service_manager.py or via CLI
{
    "name": "myservice",
    "path": "/home/coolhand/projects/myservice",
    "command": "python app.py",
    "port": 5015,
    "health_endpoint": "/health"
}
```

## Safety Features

### Caddy Operations
- **Validation required** before reload
- **Backup created** before changes
- **Rollback available** on failure

### Service Operations
- **Health check** before marking ready
- **Graceful shutdown** with timeout
- **Auto-restart** on crash (with monitor)

### Port Operations
- **Conflict detection** before allocation
- **Reserved range** checking
- **Service mapping** maintained

## Troubleshooting

**"Service won't start"**:
```bash
python scripts/service.py logs myservice --lines 50
python scripts/health.py service myservice --verbose
```

**"502 Bad Gateway"**:
```bash
python scripts/health.py service myservice  # Check service running
python scripts/caddy.py validate            # Check route config
python scripts/ports.py check 5015          # Check port in use
```

**"Port already in use"**:
```bash
python scripts/ports.py list --used
python scripts/ports.py process 5015        # Show process using port
```

**"Caddy reload failed"**:
```bash
python scripts/caddy.py validate --verbose
python scripts/caddy.py backup              # Restore from backup
```

## Integration

Works with:
- **dream-cascade**: Start MCP server for orchestration
- **code-quality**: Run tests before deployment
- **datavis**: Deploy visualization services

## Security Notes

1. **Caddy changes require sudo** (password: configured in env)
2. **Use @geepers_caddy agent** for production Caddy changes
3. **Always validate** before reloading Caddy
4. **Check health** after any deployment change
