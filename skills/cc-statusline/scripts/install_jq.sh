#!/bin/bash
# install_jq.sh — Auto-detect and install jq on Windows/macOS/Linux

set -e

JQ_CLAUDE_PATH="$HOME/.claude/jq"
JQ_CLAUDE_EXE="$HOME/.claude/jq.exe"

detect_os() {
    case "$(uname -s 2>/dev/null)" in
        Linux*)  echo "linux" ;;
        Darwin*) echo "macos" ;;
        CYGWIN*|MINGW*|MSYS*) echo "windows" ;;
        *)
            # fallback: check WINDIR
            [ -n "$WINDIR" ] && echo "windows" || echo "linux"
            ;;
    esac
}

check_jq() {
    # Check ~/.claude/jq.exe (Windows convention used by statusline)
    if [ -f "$JQ_CLAUDE_EXE" ] && "$JQ_CLAUDE_EXE" --version &>/dev/null; then
        echo "$JQ_CLAUDE_EXE"
        return 0
    fi
    # Check ~/.claude/jq
    if [ -f "$JQ_CLAUDE_PATH" ] && "$JQ_CLAUDE_PATH" --version &>/dev/null; then
        echo "$JQ_CLAUDE_PATH"
        return 0
    fi
    # Check system jq
    if command -v jq &>/dev/null; then
        echo "$(command -v jq)"
        return 0
    fi
    return 1
}

install_jq_windows() {
    echo "Downloading jq for Windows..."
    local url="https://github.com/jqlang/jq/releases/latest/download/jq-windows-amd64.exe"
    local dest="$JQ_CLAUDE_EXE"
    mkdir -p "$HOME/.claude"
    if command -v curl &>/dev/null; then
        curl -fsSL -o "$dest" "$url"
    elif command -v wget &>/dev/null; then
        wget -q -O "$dest" "$url"
    elif command -v powershell.exe &>/dev/null; then
        powershell.exe -Command "Invoke-WebRequest -Uri '$url' -OutFile '$dest'"
    else
        echo "ERROR: No download tool found (curl/wget/powershell). Please download jq manually:"
        echo "  $url"
        echo "  Save to: $dest"
        exit 1
    fi
    chmod +x "$dest"
    echo "jq installed at: $dest"
}

install_jq_macos() {
    if command -v brew &>/dev/null; then
        echo "Installing jq via Homebrew..."
        brew install jq
    else
        echo "Downloading jq for macOS..."
        local arch
        arch=$(uname -m)
        local url
        if [ "$arch" = "arm64" ]; then
            url="https://github.com/jqlang/jq/releases/latest/download/jq-macos-arm64"
        else
            url="https://github.com/jqlang/jq/releases/latest/download/jq-macos-amd64"
        fi
        mkdir -p "$HOME/.claude"
        curl -fsSL -o "$JQ_CLAUDE_PATH" "$url"
        chmod +x "$JQ_CLAUDE_PATH"
        echo "jq installed at: $JQ_CLAUDE_PATH"
    fi
}

install_jq_linux() {
    # Try package managers in order
    if command -v apt-get &>/dev/null; then
        echo "Installing jq via apt..."
        sudo apt-get install -y jq
    elif command -v dnf &>/dev/null; then
        echo "Installing jq via dnf..."
        sudo dnf install -y jq
    elif command -v yum &>/dev/null; then
        echo "Installing jq via yum..."
        sudo yum install -y jq
    elif command -v pacman &>/dev/null; then
        echo "Installing jq via pacman..."
        sudo pacman -Sy --noconfirm jq
    elif command -v zypper &>/dev/null; then
        echo "Installing jq via zypper..."
        sudo zypper install -y jq
    elif command -v apk &>/dev/null; then
        echo "Installing jq via apk..."
        sudo apk add jq
    else
        # Fallback: download binary
        echo "No package manager found. Downloading jq binary..."
        local arch
        arch=$(uname -m)
        local url
        case "$arch" in
            x86_64)  url="https://github.com/jqlang/jq/releases/latest/download/jq-linux-amd64" ;;
            aarch64|arm64) url="https://github.com/jqlang/jq/releases/latest/download/jq-linux-arm64" ;;
            *) echo "ERROR: Unsupported architecture: $arch. Install jq manually."; exit 1 ;;
        esac
        mkdir -p "$HOME/.claude"
        if command -v curl &>/dev/null; then
            curl -fsSL -o "$JQ_CLAUDE_PATH" "$url"
        else
            wget -q -O "$JQ_CLAUDE_PATH" "$url"
        fi
        chmod +x "$JQ_CLAUDE_PATH"
        echo "jq installed at: $JQ_CLAUDE_PATH"
    fi
}

main() {
    echo "=== jq Detection ==="
    local existing
    if existing=$(check_jq); then
        echo "jq already available at: $existing"
        echo "Version: $($existing --version)"
        exit 0
    fi

    echo "jq not found. Installing..."
    local os
    os=$(detect_os)
    echo "Detected OS: $os"

    case "$os" in
        windows) install_jq_windows ;;
        macos)   install_jq_macos ;;
        linux)   install_jq_linux ;;
    esac

    # Verify
    if existing=$(check_jq); then
        echo "jq successfully installed: $($existing --version)"
    else
        echo "ERROR: jq installation failed. Please install manually from https://jqlang.github.io/jq/download/"
        exit 1
    fi
}

main "$@"
