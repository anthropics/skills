#!/bin/bash
# detect-project.sh - 检测项目类型和构建命令

set -e

PROJECT_DIR="${1:-.}"
cd "$PROJECT_DIR"

# 检测项目类型
detect_project_type() {
    if [ -f "Package.swift" ]; then
        echo "swift"
        return
    fi
    
    if [ -f "package.json" ]; then
        if grep -q '"build"' package.json 2>/dev/null; then
            echo "node"
            return
        fi
    fi
    
    if [ -f "Cargo.toml" ]; then
        echo "rust"
        return
    fi
    
    if [ -f "go.mod" ]; then
        echo "go"
        return
    fi
    
    if [ -f "pyproject.toml" ]; then
        echo "python"
        return
    fi
    
    if [ -f "Makefile" ]; then
        if grep -q "^build:" Makefile 2>/dev/null; then
            echo "make"
            return
        fi
    fi
    
    if [ -f "build.gradle" ] || [ -f "build.gradle.kts" ]; then
        echo "gradle"
        return
    fi
    
    echo "unknown"
}

# 获取构建命令
get_build_command() {
    local project_type="$1"
    local version="$2"
    
    case "$project_type" in
        swift)
            echo "swift build -c release"
            ;;
        node)
            echo "npm run build"
            ;;
        rust)
            echo "cargo build --release"
            ;;
        go)
            echo "go build -o ./release/"
            ;;
        python)
            echo "python -m build"
            ;;
        make)
            echo "make build"
            ;;
        gradle)
            echo "./gradlew build"
            ;;
        *)
            echo ""
            ;;
    esac
}

# 获取 release 命令
get_release_command() {
    local project_type="$1"
    local version="$2"
    
    # 优先检测项目特定的 release 脚本
    if [ -f "script/build_and_run_codex.sh" ]; then
        echo "RELEASE_VERSION=$version bash script/build_and_run_codex.sh release"
        return
    fi
    
    if [ -f "scripts/release.sh" ]; then
        echo "bash scripts/release.sh $version"
        return
    fi
    
    if [ -f "Makefile" ] && grep -q "^release:" Makefile 2>/dev/null; then
        echo "make release VERSION=$version"
        return
    fi
    
    # 回退到默认构建命令
    get_build_command "$project_type" "$version"
}

# 主逻辑
PROJECT_TYPE=$(detect_project_type)
BUILD_COMMAND=$(get_build_command "$PROJECT_TYPE" "")
RELEASE_COMMAND=$(get_release_command "$PROJECT_TYPE" "")

# 输出结果
echo "PROJECT_TYPE=$PROJECT_TYPE"
echo "BUILD_COMMAND=$BUILD_COMMAND"
echo "RELEASE_COMMAND=$RELEASE_COMMAND"
