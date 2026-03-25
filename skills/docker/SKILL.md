---
name: docker
description: Use this skill whenever the user wants to containerize an application, write a Dockerfile, use Docker Compose, manage containers or images, debug Docker issues, set up Docker networking, or deploy with Docker. If the user mentions Docker, containers, Dockerfile, docker-compose, images, or wants to run something in a container, use this skill.
license: Proprietary. LICENSE.txt has complete terms
---

# Docker Guide

## Overview

This guide covers writing Dockerfiles, using Docker Compose, and common container operations.

## Dockerfile Basics

### Python Application
```dockerfile
FROM python:3.12-slim

WORKDIR /app

# Install dependencies first (better layer caching)
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application code
COPY . .

# Create non-root user for security
RUN adduser --disabled-password --gecos '' appuser
USER appuser

EXPOSE 8000

CMD ["python", "app.py"]
```

### Node.js Application
```dockerfile
FROM node:20-alpine

WORKDIR /app

# Install dependencies
COPY package*.json ./
RUN npm ci --only=production

# Copy source
COPY . .

# Non-root user
RUN addgroup -S appgroup && adduser -S appuser -G appgroup
USER appuser

EXPOSE 3000

CMD ["node", "server.js"]
```

### Multi-stage Build (smaller final image)
```dockerfile
# Build stage
FROM node:20 AS builder
WORKDIR /app
COPY package*.json ./
RUN npm ci
COPY . .
RUN npm run build

# Production stage
FROM node:20-alpine AS production
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production
COPY --from=builder /app/dist ./dist
USER node
EXPOSE 3000
CMD ["node", "dist/server.js"]
```

## Common Docker Commands

```bash
# Build image
docker build -t my-app .
docker build -t my-app:v1.0 -f Dockerfile.prod .

# Run container
docker run my-app
docker run -p 8080:8000 my-app          # map host:container ports
docker run -d my-app                     # detached (background)
docker run --name my-container my-app   # named container
docker run -e DATABASE_URL=postgres://... my-app  # env var
docker run -v $(pwd)/data:/app/data my-app         # volume mount

# Container management
docker ps                # running containers
docker ps -a             # all containers (including stopped)
docker stop my-container
docker start my-container
docker restart my-container
docker rm my-container   # remove stopped container
docker rm -f my-container  # force remove running container

# Logs and inspection
docker logs my-container
docker logs -f my-container   # follow logs
docker inspect my-container
docker exec -it my-container bash   # interactive shell

# Image management
docker images
docker rmi my-app
docker pull python:3.12-slim
docker tag my-app:latest my-app:v1.0

# Cleanup
docker system prune        # remove unused resources
docker image prune         # remove dangling images
docker volume prune        # remove unused volumes
```

## Docker Compose

### Basic Example (`docker-compose.yml`)
```yaml
version: '3.8'

services:
  web:
    build: .
    ports:
      - "8000:8000"
    environment:
      - DATABASE_URL=postgresql://user:password@db:5432/mydb
      - DEBUG=false
    depends_on:
      db:
        condition: service_healthy
    volumes:
      - ./uploads:/app/uploads

  db:
    image: postgres:16-alpine
    environment:
      POSTGRES_DB: mydb
      POSTGRES_USER: user
      POSTGRES_PASSWORD: password
    volumes:
      - postgres_data:/var/lib/postgresql/data
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U user -d mydb"]
      interval: 10s
      timeout: 5s
      retries: 5

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

volumes:
  postgres_data:
```

### Docker Compose Commands
```bash
# Start services
docker compose up
docker compose up -d           # detached
docker compose up --build      # rebuild images

# Stop services
docker compose down
docker compose down -v         # also remove volumes

# View logs
docker compose logs
docker compose logs -f web     # follow specific service

# Run command in service
docker compose exec web bash
docker compose exec web python manage.py migrate

# Scale a service
docker compose up -d --scale worker=3

# Rebuild without starting
docker compose build
docker compose build --no-cache
```

### Using .env with Compose
```bash
# .env file (auto-loaded by compose)
POSTGRES_PASSWORD=secretpassword
APP_PORT=8080
```

```yaml
# docker-compose.yml
services:
  web:
    ports:
      - "${APP_PORT}:8000"
  db:
    environment:
      POSTGRES_PASSWORD: ${POSTGRES_PASSWORD}
```

## Volumes

```bash
# Named volumes (managed by Docker, persists data)
docker volume create my-data
docker run -v my-data:/app/data my-app

# Bind mount (host directory)
docker run -v /host/path:/container/path my-app
docker run -v $(pwd):/app my-app  # current directory

# Read-only mount
docker run -v $(pwd)/config:/app/config:ro my-app
```

## Networking

```bash
# Create custom network
docker network create my-network

# Connect containers on same network (use service name as hostname)
docker run --network my-network --name web my-app
docker run --network my-network --name db postgres

# Containers can reach each other by name:
# web can connect to db:5432
```

## Environment Variables

```bash
# Pass single env var
docker run -e MY_VAR=value my-app

# Pass env file
docker run --env-file .env my-app
```

## Debugging

```bash
# Shell into running container
docker exec -it my-container bash
docker exec -it my-container sh   # if bash not available (alpine)

# Run container with shell override (don't start app)
docker run -it --entrypoint bash my-app

# Copy files in/out of container
docker cp my-container:/app/log.txt ./log.txt
docker cp ./config.json my-container:/app/config.json

# View resource usage
docker stats
docker stats my-container
```

## .dockerignore

```
# .dockerignore
node_modules/
__pycache__/
*.pyc
.git/
.env
.env.local
dist/
build/
*.log
.DS_Store
README.md
tests/
```

## Best Practices

- Use specific image tags (e.g., `python:3.12-slim`) not `latest`
- Use slim/alpine variants to minimize image size
- Copy `requirements.txt`/`package.json` before source code for better layer caching
- Run as non-root user (`USER appuser`)
- Use multi-stage builds to separate build and runtime dependencies
- Always include a `.dockerignore` file
- Use `CMD` for default command, `ENTRYPOINT` for fixed executable
- Use `HEALTHCHECK` in Compose for dependency ordering

## Quick Reference

| Task | Command |
|------|---------|
| Build image | `docker build -t name .` |
| Run container | `docker run -p host:container name` |
| Run detached | `docker run -d name` |
| List running | `docker ps` |
| Shell into container | `docker exec -it container bash` |
| View logs | `docker logs -f container` |
| Stop container | `docker stop container` |
| Compose up | `docker compose up -d` |
| Compose down | `docker compose down` |
| Compose logs | `docker compose logs -f` |
| Cleanup | `docker system prune` |
