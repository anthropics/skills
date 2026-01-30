#!/bin/bash
# Rust Open Responses Engine Build Script
# Handles development, release, and Docker builds

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Project root
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

# Print colored message
info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1"
    exit 1
}

# Check dependencies
check_deps() {
    info "Checking dependencies..."

    if ! command -v cargo &> /dev/null; then
        error "Rust/Cargo not found. Install from https://rustup.rs"
    fi

    if ! command -v docker &> /dev/null; then
        warn "Docker not found. Docker builds will not be available."
    fi
}

# Development build
build_dev() {
    info "Building development version..."
    cargo build
    info "Development build complete: target/debug/or-server"
}

# Release build
build_release() {
    info "Building release version..."
    cargo build --release
    info "Release build complete: target/release/or-server"
}

# Build with all features
build_full() {
    info "Building with all features..."
    cargo build --release --features full
    info "Full build complete: target/release/or-server"
}

# Docker build
build_docker() {
    local tag="${1:-latest}"
    info "Building Docker image: or-engine:$tag"

    docker build \
        --target runtime \
        -t "or-engine:$tag" \
        -f Dockerfile \
        .

    info "Docker image built: or-engine:$tag"
}

# Docker build for development
build_docker_dev() {
    info "Building Docker development image..."

    docker build \
        --target development \
        -t "or-engine:dev" \
        -f Dockerfile \
        .

    info "Docker development image built: or-engine:dev"
}

# Run tests
run_tests() {
    info "Running tests..."
    cargo test --workspace
    info "All tests passed!"
}

# Run lints
run_lint() {
    info "Running lints..."
    cargo fmt --check
    cargo clippy --workspace --all-targets -- -D warnings
    info "Lint checks passed!"
}

# Clean build artifacts
clean() {
    info "Cleaning build artifacts..."
    cargo clean
    info "Clean complete."
}

# Print usage
usage() {
    echo "Usage: $0 <command>"
    echo ""
    echo "Commands:"
    echo "  dev         Build development version"
    echo "  release     Build release version"
    echo "  full        Build with all features (GPU, local inference)"
    echo "  docker      Build Docker image for production"
    echo "  docker-dev  Build Docker image for development"
    echo "  test        Run tests"
    echo "  lint        Run lints (fmt, clippy)"
    echo "  clean       Clean build artifacts"
    echo "  all         Run lint, test, and release build"
    echo ""
}

# Main
main() {
    check_deps

    case "${1:-}" in
        dev)
            build_dev
            ;;
        release)
            build_release
            ;;
        full)
            build_full
            ;;
        docker)
            build_docker "${2:-latest}"
            ;;
        docker-dev)
            build_docker_dev
            ;;
        test)
            run_tests
            ;;
        lint)
            run_lint
            ;;
        clean)
            clean
            ;;
        all)
            run_lint
            run_tests
            build_release
            ;;
        *)
            usage
            exit 1
            ;;
    esac
}

main "$@"
