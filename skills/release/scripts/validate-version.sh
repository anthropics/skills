#!/bin/bash
# validate-version.sh - 验证版本号格式和递增

set -e

VERSION="$1"
LATEST_TAG="$2"

# 验证格式
if [[ ! "$VERSION" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "❌ 错误: 版本号格式不正确"
    echo "   期望格式: vX.Y.Z (如 v0.9.2)"
    echo "   实际输入: $VERSION"
    exit 1
fi

# 如果没有最新 tag，默认为 v0.0.0
if [ -z "$LATEST_TAG" ]; then
    LATEST_TAG="v0.0.0"
fi

# 解析版本号
IFS='.' read -r major minor patch <<< "${VERSION#v}"
IFS='.' read -r latest_major latest_minor latest_patch <<< "${LATEST_TAG#v}"

# 比较版本
if [ "$major" -gt "$latest_major" ]; then
    echo "✅ MAJOR 版本升级: $LATEST_TAG → $VERSION"
    exit 0
elif [ "$major" -lt "$latest_major" ]; then
    echo "❌ 错误: 版本号不能低于当前版本"
    echo "   当前: $LATEST_TAG"
    echo "   输入: $VERSION"
    exit 1
fi

if [ "$minor" -gt "$latest_minor" ]; then
    echo "✅ MINOR 版本升级: $LATEST_TAG → $VERSION"
    exit 0
elif [ "$minor" -lt "$latest_minor" ]; then
    echo "❌ 错误: 版本号不能低于当前版本"
    echo "   当前: $LATEST_TAG"
    echo "   输入: $VERSION"
    exit 1
fi

if [ "$patch" -gt "$latest_patch" ]; then
    echo "✅ PATCH 版本升级: $LATEST_TAG → $VERSION"
    exit 0
elif [ "$patch" -eq "$latest_patch" ]; then
    echo "❌ 错误: 版本号已存在"
    echo "   当前: $LATEST_TAG"
    echo "   输入: $VERSION"
    exit 1
else
    echo "❌ 错误: 版本号不能低于当前版本"
    echo "   当前: $LATEST_TAG"
    echo "   输入: $VERSION"
    exit 1
fi
