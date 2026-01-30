# Rust Open Responses Engine Docker Image
# Multi-stage build for minimal production image

# ==============================================================================
# Stage 1: Build Environment
# ==============================================================================
FROM rust:1.75-slim-bookworm AS builder

WORKDIR /app

# Install build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# Cache dependencies by building a dummy project first
COPY Cargo.toml Cargo.lock ./
COPY crates/or-core/Cargo.toml crates/or-core/Cargo.toml
COPY crates/or-server/Cargo.toml crates/or-server/Cargo.toml
COPY crates/or-providers/Cargo.toml crates/or-providers/Cargo.toml

# Create dummy source files
RUN mkdir -p crates/or-core/src crates/or-server/src crates/or-providers/src src && \
    echo "fn main() {}" > src/main.rs && \
    echo "pub fn dummy() {}" > crates/or-core/src/lib.rs && \
    echo "pub fn dummy() {}" > crates/or-server/src/lib.rs && \
    echo "pub fn dummy() {}" > crates/or-providers/src/lib.rs

# Build dependencies (this layer is cached)
RUN cargo build --release && rm -rf src crates

# Copy actual source
COPY . .

# Touch files to invalidate cached builds
RUN touch src/main.rs crates/*/src/*.rs

# Build the application
RUN cargo build --release --bin or-server

# ==============================================================================
# Stage 2: Runtime
# ==============================================================================
FROM debian:bookworm-slim AS runtime

WORKDIR /app

# Install runtime dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN groupadd --gid 1000 appgroup && \
    useradd --uid 1000 --gid appgroup --shell /bin/bash --create-home appuser

# Copy binary from builder
COPY --from=builder /app/target/release/or-server /usr/local/bin/

# Copy configuration
COPY --chown=appuser:appgroup config/ /app/config/

# Set permissions
RUN chmod +x /usr/local/bin/or-server

# Switch to non-root user
USER appuser

# Environment
ENV RUST_LOG=info
ENV OR_SERVER__HOST=0.0.0.0
ENV OR_SERVER__PORT=8080

# Expose port
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=5s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# Run the server
CMD ["or-server", "--config", "/app/config/production.toml"]


# ==============================================================================
# Stage 3: Development
# ==============================================================================
FROM rust:1.75-slim-bookworm AS development

WORKDIR /app

# Install development tools
RUN apt-get update && apt-get install -y --no-install-recommends \
    pkg-config \
    libssl-dev \
    git \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Install Rust tools
RUN rustup component add rustfmt clippy && \
    cargo install cargo-watch cargo-nextest

# Copy source
COPY . .

# Environment
ENV RUST_LOG=debug
ENV OR_SERVER__HOST=0.0.0.0
ENV OR_SERVER__PORT=8080

# Expose port
EXPOSE 8080

# Run with hot reload
CMD ["cargo", "watch", "-x", "run -- --config config/default.toml"]


# ==============================================================================
# Stage 4: GPU-enabled (Optional)
# ==============================================================================
FROM nvidia/cuda:12.2.0-runtime-ubuntu22.04 AS gpu-runtime

WORKDIR /app

# Install runtime dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN groupadd --gid 1000 appgroup && \
    useradd --uid 1000 --gid appgroup --shell /bin/bash --create-home appuser

# Copy binary from builder (must be built with GPU features)
COPY --from=builder /app/target/release/or-server /usr/local/bin/

# Copy configuration
COPY --chown=appuser:appgroup config/ /app/config/

# Set permissions
RUN chmod +x /usr/local/bin/or-server

# Switch to non-root user
USER appuser

# Environment
ENV RUST_LOG=info
ENV OR_SERVER__HOST=0.0.0.0
ENV OR_SERVER__PORT=8080
ENV NVIDIA_VISIBLE_DEVICES=all
ENV NVIDIA_DRIVER_CAPABILITIES=compute,utility

# Expose port
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=5s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# Run the server
CMD ["or-server", "--config", "/app/config/production.toml"]
